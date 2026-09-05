import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_1260 (x : ℝ) (h₁ : (10319/2048:ℝ) ≤ x) (h₂ : x ≤ (5215/1024:ℝ)) : (181069953/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (605922411/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2914563497/10000000000:ℝ) := by nlinarith
  have hc1 : (191565282153/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (191565282153/200000000000:ℝ) ≤ taylorCos (2914563497/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (248166536179/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (605922411/5000000000:ℝ) + taylorErr ≤ (248166536179/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120888084931/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120888084931/1000000000000:ℝ) ≤ taylorSin (605922411/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (287347461809/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2914563497/10000000000:ℝ) + taylorErr ≤ (287347461809/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-248166536179/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-191565282153/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-287347461809/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-120888084931/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15829147750191/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (999963726103/62500000000:ℝ) := by nlinarith
  have hp1 : (26197217071337/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13239508562809/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1902169590561/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-126677256091/40000000000:ℝ) := by nlinarith
  have hN : (2174265257559/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12774071405079/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2174265257559/1000000000000:ℝ) (12774071405079/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (181069953/10000000000000:ℝ) ≤ ((2174265257559/1000000000000:ℝ)/(12774071405079/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1261 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (10345/2048:ℝ)) : (194122073/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (402669957/2500000000:ℝ) := by nlinarith
  have hc1 : (123382071129/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (123382071129/125000000000:ℝ) ≤ taylorCos (402669957/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (20046557447/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (402669957/2500000000:ℝ) + taylorErr ≤ (20046557447/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123382071129/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20046557447/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15869031250677/1000000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6565806140089/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2105948959571/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502652305669927/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (502652305669927/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (194122073/10000000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(502652305669927/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1262 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (5175/1024:ℝ)) : (38749297/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15876701154617/1000000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13137959120333/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4412732968517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (251569639553017/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (251569639553017/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38749297/2000000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(251569639553017/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1263 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (20711/4096:ℝ)) : (48333597/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1771747811/10000000000:ℝ) := by nlinarith
  have hc1 : (492172780569/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492172780569/500000000000:ℝ) ≤ taylorCos (1771747811/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (22031161387/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1771747811/10000000000:ℝ) + taylorErr ≤ (22031161387/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492172780569/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22031161387/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (317702760979/20000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13144940644503/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2316786470093/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (503675221668399/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (503675221668399/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (48333597/2500000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(503675221668399/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1264 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (1295/256:ℝ)) : (12062377/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (248313140039/15625000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5260261120257/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4814188091217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252056965953651/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (252056965953651/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (12062377/625000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(252056965953651/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1265 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (5185/1024:ℝ)) : (19225319/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (79767001/400000000:ℝ) := by nlinarith
  have hc1 : (980182133691/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980182133691/1000000000000:ℝ) ≤ taylorCos (79767001/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980182133691/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-198098413053/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127259046163/8000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265338592381/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5215276096687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505089525947393/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (505089525947393/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (19225319/1000000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(505089525947393/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1266 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (2595/512:ℝ)) : (191511939/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (134223319/625000000:ℝ) := by nlinarith
  have hc1 : (7816225123/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7816225123/8000000000:ℝ) ≤ taylorCos (134223319/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7816225123/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6659697571/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15922720578253/1000000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13176040161261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5615900330071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126516515306561/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (126516515306561/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (191511939/10000000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(126516515306561/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1267 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (325/64:ℝ)) : (190040129/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970031250923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-242980182203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15953400194011/1000000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26402855043761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6415370529213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508021955500541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (508021955500541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (190040129/10000000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(508021955500541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1268 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (2605/512:ℝ)) : (37716487/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2761165419/10000000000:ℝ) := by nlinarith
  have hc1 : (192424280397/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192424280397/200000000000:ℝ) ≤ taylorCos (2761165419/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-192424280397/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27262135779/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15984079809769/1000000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26453629764999/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-450739029063/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50998161473013/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (50998161473013/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37716487/2000000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(50998161473013/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1269 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (1305/256:ℝ)) : (187138697/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/1250000000:ℝ) := by nlinarith
  have hc1 : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190661207617/200000000000:ℝ) ≤ taylorCos (383495197/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-190661207617/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-302005951603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16014759425527/1000000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13252202243119/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4002243949269/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127986259728753/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (127986259728753/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (187138697/10000000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(127986259728753/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1270 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (655/128:ℝ)) : (5759139/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3681553891/10000000000:ℝ) := by nlinarith
  have hc1 : (93299279657/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (93299279657/100000000000:ℝ) ≤ taylorCos (3681553891/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-93299279657/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89973759701/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8038059328521/500000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26605953928713/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1196918852699/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128970795537647/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (128970795537647/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5759139/312500000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(128970795537647/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1271 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (1315/256:ℝ)) : (90750063/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4295146207/10000000000:ℝ) := by nlinarith
  have hc1 : (90916798079/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (90916798079/100000000000:ℝ) ≤ taylorCos (4295146207/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-90916798079/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-416429562443/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16137477888557/1000000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6676875842797/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11121793942809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (519836385207333/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (519836385207333/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (90750063/5000000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(519836385207333/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1272 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (665/128:ℝ)) : (21679333/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/625000000:ℝ) := by nlinarith
  have hc1 : (817584810857/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (817584810857/1000000000000:ℝ) ≤ taylorCos (383495197/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (575808193717/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/625000000:ℝ) + taylorErr ≤ (575808193717/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-817584810857/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-575808193717/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127512152993/7812500000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (27012151698617/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-15553818277991/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (531786353304707/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (531786353304707/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (21679333/1250000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(531786353304707/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1273 (x : ℝ) (h₁ : (645/128:ℝ) ≤ x) (h₂ : x ≤ (335/64:ℝ)) : (168305763/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3681553891/5000000000:ℝ) := by nlinarith
  have hc1 : (74095112303/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (74095112303/100000000000:ℝ) ≤ taylorCos (3681553891/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-74095112303/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-671558957117/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15830681730979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3288854809227/200000000000:ℝ) := by nlinarith
  have hp1 : (5239951161473/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2721525058357/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-18276645299581/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200445608647/62500000000:ℝ) := by nlinarith
  have hN : (2214650201487/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (539828297808779/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2214650201487/1000000000000:ℝ) (539828297808779/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (168305763/10000000000000:ℝ) ≤ ((2214650201487/1000000000000:ℝ)/(539828297808779/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1274 (x : ℝ) (h₁ : (10321/2048:ℝ) ≤ x) (h₂ : x ≤ (20733/4096:ℝ)) : (99799521/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (621262219/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1940485697/10000000000:ℝ) := by nlinarith
  have hc1 : (49061578929/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49061578929/50000000000:ℝ) ≤ taylorCos (1940485697/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (992290593613/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (621262219/5000000000:ℝ) + taylorErr ≤ (992290593613/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61966486419/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61966486419/500000000000:ℝ) ≤ taylorSin (621262219/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (96416525593/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1940485697/10000000000:ℝ) + taylorErr ≤ (96416525593/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-992290593613/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-49061578929/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-96416525593/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61966486419/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15832215711767/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15902011837617/1000000000000:ℝ) := by nlinarith
  have hp1 : (26202294543393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26317807385687/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1268735774677/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3247328257939/1000000000000:ℝ) := by nlinarith
  have hN : (1127518832163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504747960967423/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1127518832163/500000000000:ℝ) (504747960967423/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (99799521/5000000000000:ℝ) ≤ ((1127518832163/500000000000:ℝ)/(504747960967423/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1275 (x : ℝ) (h₁ : (10321/2048:ℝ) ≤ x) (h₂ : x ≤ (1299/256:ℝ)) : (19764329/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (621262219/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (992290593613/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (621262219/5000000000:ℝ) + taylorErr ≤ (992290593613/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61966486419/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61966486419/500000000000:ℝ) ≤ taylorSin (621262219/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-992290593613/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-486469974967/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-231058110583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61966486419/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15832215711767/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3985282086927/250000000000:ℝ) := by nlinarith
  have hp1 : (26202294543393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13191272577633/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6095901035947/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3247328257939/1000000000000:ℝ) := by nlinarith
  have hN : (1127518832163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2536195729981/5000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1127518832163/500000000000:ℝ) (2536195729981/5000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (19764329/1000000000000:ℝ) ≤ ((1127518832163/500000000000:ℝ)/(2536195729981/5000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1276 (x : ℝ) (h₁ : (10323/2048:ℝ) ≤ x) (h₂ : x ≤ (5207/1024:ℝ)) : (42053501/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1273204053/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2669126571/10000000000:ℝ) := by nlinarith
  have hc1 : (482294895513/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482294895513/500000000000:ℝ) ≤ taylorCos (2669126571/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (198381140541/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1273204053/10000000000:ℝ) + taylorErr ≤ (198381140541/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (126976694141/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (126976694141/1000000000000:ℝ) ≤ taylorSin (1273204053/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198381140541/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-482294895513/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52750936249/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-126976694141/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15835283673343/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7987437962521/500000000000:ℝ) := by nlinarith
  have hp1 : (26207372015449/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6609599337157/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6973251065317/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-665545092129/200000000000:ℝ) := by nlinarith
  have hN : (116790987897/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (509393321640973/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (116790987897/50000000000:ℝ) (509393321640973/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (42053501/2000000000000:ℝ) ≤ ((116790987897/50000000000:ℝ)/(509393321640973/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1277 (x : ℝ) (h₁ : (10325/2048:ℝ) ≤ x) (h₂ : x ≤ (10345/2048:ℝ)) : (3611587/156250000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1303883669/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (402669957/2500000000:ℝ) := by nlinarith
  have hc1 : (123382071129/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (123382071129/125000000000:ℝ) ≤ taylorCos (402669957/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (99151147559/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1303883669/10000000000:ℝ) + taylorErr ≤ (99151147559/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13001922039/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13001922039/100000000000:ℝ) ≤ taylorSin (1303883669/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (20046557447/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (402669957/2500000000:ℝ) + taylorErr ≤ (20046557447/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-99151147559/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123382071129/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20046557447/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13001922039/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15838351634919/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15869031250677/1000000000000:ℝ) := by nlinarith
  have hp1 : (5242489897501/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6565806140089/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2105948959571/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3408122246877/1000000000000:ℝ) := by nlinarith
  have hN : (2416610771287/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502652305669927/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2416610771287/1000000000000:ℝ) (502652305669927/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3611587/156250000000:ℝ) ≤ ((2416610771287/1000000000000:ℝ)/(502652305669927/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1278 (x : ℝ) (h₁ : (10325/2048:ℝ) ≤ x) (h₂ : x ≤ (5175/1024:ℝ)) : (115347177/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1303883669/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (99151147559/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1303883669/10000000000:ℝ) + taylorErr ≤ (99151147559/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13001922039/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13001922039/100000000000:ℝ) ≤ taylorSin (1303883669/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-99151147559/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13001922039/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15838351634919/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15876701154617/1000000000000:ℝ) := by nlinarith
  have hp1 : (5242489897501/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13137959120333/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4412732968517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3408122246877/1000000000000:ℝ) := by nlinarith
  have hN : (2416610771287/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (251569639553017/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2416610771287/1000000000000:ℝ) (251569639553017/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (115347177/5000000000000:ℝ) ≤ ((2416610771287/1000000000000:ℝ)/(251569639553017/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1279 (x : ℝ) (h₁ : (20651/4096:ℝ) ≤ x) (h₂ : x ≤ (41413/8192:ℝ)) : (9370879/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1311553573/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1737233243/10000000000:ℝ) := by nlinarith
  have hc1 : (246237003427/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246237003427/250000000000:ℝ) ≤ taylorCos (1737233243/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (61963216279/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1311553573/10000000000:ℝ) + taylorErr ≤ (61963216279/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (65389830927/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (65389830927/500000000000:ℝ) ≤ taylorSin (1311553573/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (21606352733/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1737233243/10000000000:ℝ) + taylorErr ≤ (21606352733/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-61963216279/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246237003427/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21606352733/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-65389830927/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15839118625313/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7940843296089/500000000000:ℝ) := by nlinarith
  have hp1 : (26213718855519/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6571042283217/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4543240236629/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-171411064393/50000000000:ℝ) := by nlinarith
  have hN : (609202456849/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (503455938024333/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (609202456849/250000000000:ℝ) (503455938024333/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9370879/400000000000:ℝ) ≤ ((609202456849/250000000000:ℝ)/(503455938024333/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1280 (x : ℝ) (h₁ : (20651/4096:ℝ) ≤ x) (h₂ : x ≤ (10381/2048:ℝ)) : (115886053/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1311553573/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2162912911/10000000000:ℝ) := by nlinarith
  have hc1 : (195340016773/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195340016773/200000000000:ℝ) ≤ taylorCos (2162912911/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (61963216279/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1311553573/10000000000:ℝ) + taylorErr ≤ (61963216279/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (65389830927/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (65389830927/500000000000:ℝ) ≤ taylorSin (1311553573/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-61963216279/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-195340016773/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13413050829/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-65389830927/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15839118625313/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15924254559041/1000000000000:ℝ) := by nlinarith
  have hp1 : (26213718855519/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3294327382323/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1413983380047/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-171411064393/50000000000:ℝ) := by nlinarith
  have hN : (609202456849/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506163766522277/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (609202456849/250000000000:ℝ) (506163766522277/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (115886053/5000000000000:ℝ) ≤ ((609202456849/250000000000:ℝ)/(506163766522277/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1281 (x : ℝ) (h₁ : (1291/256:ℝ) ≤ x) (h₂ : x ≤ (5235/1024:ℝ)) : (242928173/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3528155813/10000000000:ℝ) := by nlinarith
  have hc1 : (938403531771/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (938403531771/1000000000000:ℝ) ≤ taylorCos (3528155813/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (345541327307/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3528155813/10000000000:ℝ) + taylorErr ≤ (345541327307/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-938403531771/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-345541327307/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7921476788641/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16060778849163/1000000000000:ℝ) := by nlinarith
  have hp1 : (26220065695587/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13290283284047/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-287021382891/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-352871495821/100000000000:ℝ) := by nlinarith
  have hN : (634453080129/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128724308620861/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (634453080129/250000000000:ℝ) (128724308620861/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (242928173/10000000000000:ℝ) ≤ ((634453080129/250000000000:ℝ)/(128724308620861/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1282 (x : ℝ) (h₁ : (1291/256:ℝ) ≤ x) (h₂ : x ≤ (5275/1024:ℝ)) : (14726831/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4755340443/10000000000:ℝ) := by nlinarith
  have hc1 : (889048353567/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (889048353567/1000000000000:ℝ) ≤ taylorCos (4755340443/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (45781330591/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4755340443/10000000000:ℝ) + taylorErr ≤ (45781330591/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-889048353567/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-45781330591/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7921476788641/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8091748656097/500000000000:ℝ) := by nlinarith
  have hp1 : (26220065695587/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13391832726523/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-12261918425447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-352871495821/100000000000:ℝ) := by nlinarith
  have hN : (634453080129/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (522811170507581/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (634453080129/250000000000:ℝ) (522811170507581/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14726831/625000000000:ℝ) ≤ ((634453080129/250000000000:ℝ)/(522811170507581/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1283 (x : ℝ) (h₁ : (1291/256:ℝ) ≤ x) (h₂ : x ≤ (2653/512:ℝ)) : (46032101/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (5706408531/10000000000:ℝ) := by nlinarith
  have hc1 : (841554975169/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (841554975169/1000000000000:ℝ) ≤ taylorCos (5706408531/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (540171474997/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5706408531/10000000000:ℝ) + taylorErr ≤ (540171474997/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-841554975169/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-540171474997/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7921476788641/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16278604121043/1000000000000:ℝ) := by nlinarith
  have hp1 : (26220065695587/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6735266772221/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3638198986849/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-352871495821/100000000000:ℝ) := by nlinarith
  have hN : (634453080129/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (528985904259277/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (634453080129/250000000000:ℝ) (528985904259277/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (46032101/2000000000000:ℝ) ≤ ((634453080129/250000000000:ℝ)/(528985904259277/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1284 (x : ℝ) (h₁ : (1291/256:ℝ) ≤ x) (h₂ : x ≤ (21/4:ℝ)) : (109191861/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7921476788641/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16493361431347/1000000000000:ℝ) := by nlinarith
  have hp1 : (26220065695587/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (545929802751/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9650766670237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-352871495821/100000000000:ℝ) := by nlinarith
  have hN : (634453080129/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (54306194261009/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (634453080129/250000000000:ℝ) (54306194261009/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (109191861/5000000000000:ℝ) ≤ ((634453080129/250000000000:ℝ)/(54306194261009/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1285 (x : ℝ) (h₁ : (5165/1024:ℝ) ≤ x) (h₂ : x ≤ (5175/1024:ℝ)) : (270875209/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1380582709/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (24762127163/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1380582709/10000000000:ℝ) + taylorErr ≤ (24762127163/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27524023863/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27524023863/200000000000:ℝ) ≤ taylorSin (1380582709/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-24762127163/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27524023863/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7923010769429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15876701154617/1000000000000:ℝ) := by nlinarith
  have hp1 : (26225143167643/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13137959120333/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4412732968517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3609107331783/1000000000000:ℝ) := by nlinarith
  have hN : (2618622245263/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (251569639553017/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2618622245263/1000000000000:ℝ) (251569639553017/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (270875209/10000000000000:ℝ) ≤ ((2618622245263/1000000000000:ℝ)/(251569639553017/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1286 (x : ℝ) (h₁ : (5165/1024:ℝ) ≤ x) (h₂ : x ≤ (10355/2048:ℝ)) : (67587843/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1380582709/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1764077907/10000000000:ℝ) := by nlinarith
  have hc1 : (196896090621/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (196896090621/200000000000:ℝ) ≤ taylorCos (1764077907/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (24762127163/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1380582709/10000000000:ℝ) + taylorErr ≤ (24762127163/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27524023863/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27524023863/200000000000:ℝ) ≤ taylorSin (1380582709/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (175494255731/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1764077907/10000000000:ℝ) + taylorErr ≤ (175494255731/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-24762127163/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-196896090621/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-175494255731/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27524023863/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7923010769429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3971092764639/250000000000:ℝ) := by nlinarith
  have hp1 : (26225143167643/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1051544476839/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4613500383273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3609107331783/1000000000000:ℝ) := by nlinarith
  have hN : (2618622245263/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (503626487851783/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2618622245263/1000000000000:ℝ) (503626487851783/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (67587843/2500000000000:ℝ) ≤ ((2618622245263/1000000000000:ℝ)/(503626487851783/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1287 (x : ℝ) (h₁ : (5165/1024:ℝ) ≤ x) (h₂ : x ≤ (41431/8192:ℝ)) : (135031901/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1380582709/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (903131189/5000000000:ℝ) := by nlinarith
  have hc1 : (3842700713/3906250000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (3842700713/3906250000:ℝ) ≤ taylorCos (903131189/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (24762127163/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1380582709/10000000000:ℝ) + taylorErr ≤ (24762127163/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27524023863/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27524023863/200000000000:ℝ) ≤ taylorSin (1380582709/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (44911415163/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (903131189/5000000000:ℝ) + taylorErr ≤ (44911415163/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-24762127163/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-3842700713/3906250000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-44911415163/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27524023863/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7923010769429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15888589505723/1000000000000:ℝ) := by nlinarith
  have hp1 : (26225143167643/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13147796722573/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-472388925669/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3609107331783/1000000000000:ℝ) := by nlinarith
  have hN : (2618622245263/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (503894552962743/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2618622245263/1000000000000:ℝ) (503894552962743/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (135031901/5000000000000:ℝ) ≤ ((2618622245263/1000000000000:ℝ)/(503894552962743/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1288 (x : ℝ) (h₁ : (5165/1024:ℝ) ≤ x) (h₂ : x ≤ (1295/256:ℝ)) : (134914401/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1380582709/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (24762127163/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1380582709/10000000000:ℝ) + taylorErr ≤ (24762127163/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27524023863/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27524023863/200000000000:ℝ) ≤ taylorSin (1380582709/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-24762127163/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27524023863/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7923010769429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (248313140039/15625000000:ℝ) := by nlinarith
  have hp1 : (26225143167643/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5260261120257/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4814188091217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3609107331783/1000000000000:ℝ) := by nlinarith
  have hN : (2618622245263/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252056965953651/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2618622245263/1000000000000:ℝ) (252056965953651/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (134914401/5000000000000:ℝ) ≤ ((2618622245263/1000000000000:ℝ)/(252056965953651/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1289 (x : ℝ) (h₁ : (5165/1024:ℝ) ≤ x) (h₂ : x ≤ (20731/4096:ℝ)) : (269255433/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1380582709/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1925145889/10000000000:ℝ) := by nlinarith
  have hc1 : (981526226193/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981526226193/1000000000000:ℝ) ≤ taylorCos (1925145889/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (24762127163/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1380582709/10000000000:ℝ) + taylorErr ≤ (24762127163/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27524023863/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27524023863/200000000000:ℝ) ≤ taylorSin (1380582709/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (95663817247/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1925145889/10000000000:ℝ) + taylorErr ≤ (95663817247/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-24762127163/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-981526226193/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-95663817247/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27524023863/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7923010769429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15900477856829/1000000000000:ℝ) := by nlinarith
  have hp1 : (26225143167643/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (210522149197/8000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5034838101807/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3609107331783/1000000000000:ℝ) := by nlinarith
  have hN : (2618622245263/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504650392151019/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2618622245263/1000000000000:ℝ) (504650392151019/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (269255433/10000000000000:ℝ) ≤ ((2618622245263/1000000000000:ℝ)/(504650392151019/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1290 (x : ℝ) (h₁ : (5165/1024:ℝ) ≤ x) (h₂ : x ≤ (5185/1024:ℝ)) : (53757489/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1380582709/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (79767001/400000000:ℝ) := by nlinarith
  have hc1 : (980182133691/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980182133691/1000000000000:ℝ) ≤ taylorCos (79767001/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (24762127163/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1380582709/10000000000:ℝ) + taylorErr ≤ (24762127163/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27524023863/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27524023863/200000000000:ℝ) ≤ taylorSin (1380582709/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-24762127163/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980182133691/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-198098413053/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27524023863/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7923010769429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127259046163/8000000000:ℝ) := by nlinarith
  have hp1 : (26225143167643/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265338592381/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5215276096687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3609107331783/1000000000000:ℝ) := by nlinarith
  have hN : (2618622245263/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505089525947393/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2618622245263/1000000000000:ℝ) (505089525947393/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (53757489/2000000000000:ℝ) ≤ ((2618622245263/1000000000000:ℝ)/(505089525947393/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1291 (x : ℝ) (h₁ : (5165/1024:ℝ) ≤ x) (h₂ : x ≤ (20751/4096:ℝ)) : (268216841/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1380582709/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (64954499/312500000:ℝ) := by nlinarith
  have hc1 : (97847593311/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97847593311/100000000000:ℝ) ≤ taylorCos (64954499/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (24762127163/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1380582709/10000000000:ℝ) + taylorErr ≤ (24762127163/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27524023863/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27524023863/200000000000:ℝ) ≤ taylorSin (1380582709/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-24762127163/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-97847593311/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-25795119703/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27524023863/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7923010769429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3978954416177/250000000000:ℝ) := by nlinarith
  have hp1 : (26225143167643/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6585164002561/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5435682998719/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3609107331783/1000000000000:ℝ) := by nlinarith
  have hN : (2618622245263/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505626503872463/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2618622245263/1000000000000:ℝ) (505626503872463/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (268216841/10000000000000:ℝ) ≤ ((2618622245263/1000000000000:ℝ)/(505626503872463/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1292 (x : ℝ) (h₁ : (5165/1024:ℝ) ≤ x) (h₂ : x ≤ (2595/512:ℝ)) : (26775111/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1380582709/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (134223319/625000000:ℝ) := by nlinarith
  have hc1 : (7816225123/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7816225123/8000000000:ℝ) ≤ taylorCos (134223319/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (24762127163/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1380582709/10000000000:ℝ) + taylorErr ≤ (24762127163/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27524023863/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27524023863/200000000000:ℝ) ≤ taylorSin (1380582709/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-24762127163/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7816225123/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6659697571/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27524023863/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7923010769429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15922720578253/1000000000000:ℝ) := by nlinarith
  have hp1 : (26225143167643/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13176040161261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5615900330071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3609107331783/1000000000000:ℝ) := by nlinarith
  have hN : (2618622245263/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126516515306561/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2618622245263/1000000000000:ℝ) (126516515306561/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (26775111/1000000000000:ℝ) ≤ ((2618622245263/1000000000000:ℝ)/(126516515306561/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1293 (x : ℝ) (h₁ : (10331/2048:ℝ) ≤ x) (h₂ : x ≤ (20733/4096:ℝ)) : (4336279/156250000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (348980629/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1940485697/10000000000:ℝ) := by nlinarith
  have hc1 : (49061578929/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49061578929/50000000000:ℝ) ≤ taylorCos (1940485697/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (990272814639/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (348980629/2500000000:ℝ) + taylorErr ≤ (990272814639/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27827868361/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27827868361/200000000000:ℝ) ≤ taylorSin (348980629/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (96416525593/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1940485697/10000000000:ℝ) + taylorErr ≤ (96416525593/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-990272814639/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-49061578929/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-96416525593/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27827868361/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7923777759823/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15902011837617/1000000000000:ℝ) := by nlinarith
  have hp1 : (26227681903671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26317807385687/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1268735774677/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3649302397147/1000000000000:ℝ) := by nlinarith
  have hN : (664757395627/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504747960967423/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (664757395627/250000000000:ℝ) (504747960967423/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4336279/156250000000:ℝ) ≤ ((664757395627/250000000000:ℝ)/(504747960967423/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1294 (x : ℝ) (h₁ : (2583/512:ℝ) ≤ x) (h₂ : x ≤ (20775/4096:ℝ)) : (283710363/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2262621663/10000000000:ℝ) := by nlinarith
  have hc1 : (194902346219/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194902346219/200000000000:ℝ) ≤ taylorCos (2262621663/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (224336538627/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2262621663/10000000000:ℝ) + taylorErr ≤ (224336538627/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194902346219/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-224336538627/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7924544750217/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15934225434163/1000000000000:ℝ) := by nlinarith
  have hp1 : (26230220639699/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6592780210747/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5916005969631/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3689496590933/1000000000000:ℝ) := by nlinarith
  have hN : (2699438378397/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (101359816074691/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2699438378397/1000000000000:ℝ) (101359816074691/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (283710363/10000000000000:ℝ) ≤ ((2699438378397/1000000000000:ℝ)/(101359816074691/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1295 (x : ℝ) (h₁ : (2583/512:ℝ) ≤ x) (h₂ : x ≤ (10403/2048:ℝ)) : (282019961/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (500077737/2000000000:ℝ) := by nlinarith
  have hc1 : (15139106289/15625000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15139106289/15625000000:ℝ) ≤ taylorCos (500077737/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-15139106289/15625000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-123720810751/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7924544750217/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127664017091/8000000000:ℝ) := by nlinarith
  have hp1 : (26230220639699/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26410471251947/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3267524915607/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3689496590933/1000000000000:ℝ) := by nlinarith
  have hN : (2699438378397/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508315664369099/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2699438378397/1000000000000:ℝ) (508315664369099/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (282019961/10000000000000:ℝ) ≤ ((2699438378397/1000000000000:ℝ)/(508315664369099/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1296 (x : ℝ) (h₁ : (2583/512:ℝ) ≤ x) (h₂ : x ≤ (10423/2048:ℝ)) : (55971473/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1403592421/5000000000:ℝ) := by nlinarith
  have hc1 : (960856630841/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (960856630841/1000000000000:ℝ) ≤ taylorCos (1403592421/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-960856630841/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-55409216517/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7924544750217/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15988681752133/1000000000000:ℝ) := by nlinarith
  have hp1 : (26230220639699/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5292249194637/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-733098453719/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3689496590933/1000000000000:ℝ) := by nlinarith
  have hN : (2699438378397/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (255137944170991/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2699438378397/1000000000000:ℝ) (255137944170991/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (55971473/2000000000000:ℝ) ≤ ((2699438378397/1000000000000:ℝ)/(255137944170991/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1297 (x : ℝ) (h₁ : (2583/512:ℝ) ≤ x) (h₂ : x ≤ (5237/1024:ℝ)) : (274435871/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (897378761/2500000000:ℝ) := by nlinarith
  have hc1 : (7314575507/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7314575507/7812500000:ℝ) ≤ taylorCos (897378761/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (17564637919/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/2500000000:ℝ) + taylorErr ≤ (17564637919/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7314575507/7812500000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-17564637919/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7924544750217/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3213382954463/200000000000:ℝ) := by nlinarith
  have hp1 : (26230220639699/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13295360756171/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4670563953693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3689496590933/1000000000000:ℝ) := by nlinarith
  have hN : (2699438378397/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128822875150417/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2699438378397/1000000000000:ℝ) (128822875150417/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (274435871/10000000000000:ℝ) ≤ ((2699438378397/1000000000000:ℝ)/(128822875150417/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1298 (x : ℝ) (h₁ : (41333/8192:ℝ) ≤ x) (h₂ : x ≤ (10361/2048:ℝ)) : (37182159/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (357609271/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (928058377/5000000000:ℝ) := by nlinarith
  have hc1 : (245705887231/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245705887231/250000000000:ℝ) ≤ taylorCos (928058377/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (61861667739/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (357609271/2500000000:ℝ) + taylorErr ≤ (61861667739/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1425563901/10000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1425563901/10000000000:ℝ) ≤ taylorSin (357609271/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (36909547853/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (928058377/5000000000:ℝ) + taylorErr ≤ (36909547853/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-61861667739/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245705887231/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-36909547853/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1425563901/10000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15851006976419/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3973393735821/250000000000:ℝ) := by nlinarith
  have hp1 : (13116697029867/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26303844337347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1213578751609/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1869868978613/500000000000:ℝ) := by nlinarith
  have hN : (1374975636701/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504211448955571/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1374975636701/500000000000:ℝ) (504211448955571/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37182159/1250000000000:ℝ) ≤ ((1374975636701/500000000000:ℝ)/(504211448955571/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1299 (x : ℝ) (h₁ : (20669/4096:ℝ) ≤ x) (h₂ : x ≤ (5195/1024:ℝ)) : (76262343/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (362402961/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1150485591/5000000000:ℝ) := by nlinarith
  have hc1 : (194728849477/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194728849477/200000000000:ℝ) ≤ taylorCos (1150485591/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (989511515949/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (362402961/2500000000:ℝ) + taylorErr ≤ (989511515949/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (72227009537/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (72227009537/500000000000:ℝ) ≤ taylorSin (362402961/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-989511515949/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194728849477/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4561441709/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-72227009537/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3963231113101/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3984515096533/250000000000:ℝ) := by nlinarith
  have hp1 : (26236567479769/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26377467683141/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-751995507923/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1894988809579/500000000000:ℝ) := by nlinarith
  have hN : (2800466103209/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507043537743981/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2800466103209/1000000000000:ℝ) (507043537743981/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (76262343/2500000000000:ℝ) ≤ ((2800466103209/1000000000000:ℝ)/(507043537743981/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1300 (x : ℝ) (h₁ : (10335/2048:ℝ) ≤ x) (h₂ : x ≤ (10355/2048:ℝ)) : (313680999/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1764077907/10000000000:ℝ) := by nlinarith
  have hc1 : (196896090621/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (196896090621/200000000000:ℝ) ≤ taylorCos (1764077907/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (989400430061/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (364320437/2500000000:ℝ) + taylorErr ≤ (989400430061/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (72606461171/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (72606461171/500000000000:ℝ) ≤ taylorSin (364320437/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (175494255731/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1764077907/10000000000:ℝ) + taylorErr ≤ (175494255731/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-989400430061/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-196896090621/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-175494255731/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-72606461171/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7926845721399/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3971092764639/250000000000:ℝ) := by nlinarith
  have hp1 : (3279729605973/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1051544476839/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4613500383273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3810072964599/1000000000000:ℝ) := by nlinarith
  have hN : (1410336267269/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (503626487851783/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1410336267269/500000000000:ℝ) (503626487851783/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (313680999/10000000000000:ℝ) ≤ ((1410336267269/500000000000:ℝ)/(503626487851783/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1301 (x : ℝ) (h₁ : (10335/2048:ℝ) ≤ x) (h₂ : x ≤ (1295/256:ℝ)) : (12522987/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (989400430061/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (364320437/2500000000:ℝ) + taylorErr ≤ (989400430061/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (72606461171/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (72606461171/500000000000:ℝ) ≤ taylorSin (364320437/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-989400430061/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-72606461171/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7926845721399/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (248313140039/15625000000:ℝ) := by nlinarith
  have hp1 : (3279729605973/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5260261120257/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4814188091217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3810072964599/1000000000000:ℝ) := by nlinarith
  have hN : (1410336267269/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252056965953651/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1410336267269/500000000000:ℝ) (252056965953651/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (12522987/400000000000:ℝ) ≤ ((1410336267269/500000000000:ℝ)/(252056965953651/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1302 (x : ℝ) (h₁ : (20671/4096:ℝ) ≤ x) (h₂ : x ≤ (41453/8192:ℝ)) : (317177363/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (366237913/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (945315661/5000000000:ℝ) := by nlinarith
  have hc1 : (245545184421/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245545184421/250000000000:ℝ) ≤ taylorCos (945315661/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (989288762133/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (366237913/2500000000:ℝ) + taylorErr ≤ (989288762133/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (29194348037/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (29194348037/200000000000:ℝ) ≤ taylorSin (366237913/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (187938806343/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (945315661/5000000000:ℝ) + taylorErr ≤ (187938806343/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-989288762133/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245545184421/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-187938806343/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-29194348037/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1981807304149/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1987128300007/125000000000:ℝ) := by nlinarith
  have hp1 : (13119553107899/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13154778246743/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-12361466607/2500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3830167995219/1000000000000:ℝ) := by nlinarith
  have hN : (1420439616543/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (100886179345631/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1420439616543/500000000000:ℝ) (100886179345631/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (317177363/10000000000000:ℝ) ≤ ((1420439616543/500000000000:ℝ)/(100886179345631/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1303 (x : ℝ) (h₁ : (323/64:ℝ) ≤ x) (h₂ : x ≤ (2655/512:ℝ)) : (72912521/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2914563497/5000000000:ℝ) := by nlinarith
  have hc1 : (834862872719/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (834862872719/1000000000000:ℝ) ≤ taylorCos (2914563497/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (123647064029/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2500000000:ℝ) + taylorErr ≤ (123647064029/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (146730472157/1000000000000:ℝ) ≤ taylorSin (368155389/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (550457975201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2914563497/5000000000:ℝ) + taylorErr ≤ (550457975201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-123647064029/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-834862872719/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-550457975201/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-146730472157/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3171045084717/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8145437983673/500000000000:ℝ) := by nlinarith
  have hp1 : (2624037558381/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26961376977379/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-14841104979599/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3850262698989/1000000000000:ℝ) := by nlinarith
  have hN : (2861086186757/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (529785279566903/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2861086186757/1000000000000:ℝ) (529785279566903/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (72912521/2500000000000:ℝ) ≤ ((2861086186757/1000000000000:ℝ)/(529785279566903/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1304 (x : ℝ) (h₁ : (20673/4096:ℝ) ≤ x) (h₂ : x ≤ (2593/512:ℝ)) : (325164083/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (74014573/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (39562547217/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (74014573/500000000:ℝ) + taylorErr ≤ (39562547217/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (14748911781/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (14748911781/100000000000:ℝ) ≤ taylorSin (74014573/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (201104637201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2024854641/10000000000:ℝ) + taylorErr ≤ (201104637201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-39562547217/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-979569763403/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-201104637201/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-14748911781/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15855992413979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (318208974639/20000000000:ℝ) := by nlinarith
  have hp1 : (1640102809489/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26331770434027/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1323860284999/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3870357063827/1000000000000:ℝ) := by nlinarith
  have hN : (1440646691701/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505284757704019/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1440646691701/500000000000:ℝ) (505284757704019/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (325164083/10000000000000:ℝ) ≤ ((1440646691701/500000000000:ℝ)/(505284757704019/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1305 (x : ℝ) (h₁ : (20673/4096:ℝ) ≤ x) (h₂ : x ≤ (5191/1024:ℝ)) : (10122207/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (74014573/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2178252719/10000000000:ℝ) := by nlinarith
  have hc1 : (976369729063/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (976369729063/1000000000000:ℝ) ≤ taylorCos (2178252719/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (39562547217/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (74014573/500000000:ℝ) + taylorErr ≤ (39562547217/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (14748911781/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (14748911781/100000000000:ℝ) ≤ taylorSin (74014573/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-39562547217/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-976369729063/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-108053399679/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-14748911781/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15855992413979/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15925788539829/1000000000000:ℝ) := by nlinarith
  have hp1 : (1640102809489/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13178578897323/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-227838440447/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3870357063827/1000000000000:ℝ) := by nlinarith
  have hN : (1440646691701/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (253130740615349/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1440646691701/500000000000:ℝ) (253130740615349/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10122207/312500000000:ℝ) ≤ ((1440646691701/500000000000:ℝ)/(253130740615349/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1306 (x : ℝ) (h₁ : (41351/8192:ℝ) ≤ x) (h₂ : x ≤ (20731/4096:ℝ)) : (337513471/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (74973311/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1925145889/10000000000:ℝ) := by nlinarith
  have hc1 : (981526226193/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981526226193/1000000000000:ℝ) ≤ taylorCos (1925145889/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494389527749/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (74973311/500000000:ℝ) + taylorErr ≤ (494389527749/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9336584461/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9336584461/62500000000:ℝ) ≤ taylorSin (74973311/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (95663817247/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1925145889/10000000000:ℝ) + taylorErr ≤ (95663817247/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-494389527749/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-981526226193/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-95663817247/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9336584461/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3964477472491/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15900477856829/1000000000000:ℝ) := by nlinarith
  have hp1 : (26244818371859/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (210522149197/8000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5034838101807/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3920591414279/1000000000000:ℝ) := by nlinarith
  have hN : (2931812358781/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504650392151019/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2931812358781/1000000000000:ℝ) (504650392151019/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (337513471/10000000000000:ℝ) ≤ ((2931812358781/1000000000000:ℝ)/(504650392151019/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1307 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (1295/256:ℝ)) : (359539763/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (248313140039/15625000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5260261120257/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4814188091217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252056965953651/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (252056965953651/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (359539763/10000000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(252056965953651/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1308 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (10365/2048:ℝ)) : (71769027/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/2000000000:ℝ) := by nlinarith
  have hc1 : (245418170983/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245418170983/250000000000:ℝ) ≤ taylorCos (383495197/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245418170983/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-23821844637/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3179942173287/200000000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13156999640797/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1002956804263/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504601611272463/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (504601611272463/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (71769027/2000000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(504601611272463/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1309 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (41471/8192:ℝ)) : (89615951/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1959660457/10000000000:ℝ) := by nlinarith
  have hc1 : (98086002221/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (98086002221/100000000000:ℝ) ≤ taylorCos (1959660457/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (24339272943/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1959660457/10000000000:ℝ) + taylorErr ≤ (24339272943/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-98086002221/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24339272943/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7951964656801/500000000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5264196161153/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-640633535959/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252434967612049/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (252434967612049/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (89615951/2500000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(252434967612049/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1310 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (5185/1024:ℝ)) : (358152183/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (79767001/400000000:ℝ) := by nlinarith
  have hc1 : (980182133691/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980182133691/1000000000000:ℝ) ≤ taylorCos (79767001/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980182133691/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-198098413053/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127259046163/8000000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265338592381/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5215276096687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505089525947393/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (505089525947393/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (358152183/10000000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(505089525947393/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1311 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (20751/4096:ℝ)) : (89347967/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (64954499/312500000:ℝ) := by nlinarith
  have hc1 : (97847593311/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97847593311/100000000000:ℝ) ≤ taylorCos (64954499/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-97847593311/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-25795119703/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3978954416177/250000000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6585164002561/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5435682998719/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505626503872463/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (505626503872463/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (89347967/2500000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(505626503872463/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1312 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (2595/512:ℝ)) : (356771293/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (134223319/625000000:ℝ) := by nlinarith
  have hc1 : (7816225123/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7816225123/8000000000:ℝ) ≤ taylorCos (134223319/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7816225123/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6659697571/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15922720578253/1000000000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13176040161261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5615900330071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126516515306561/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (126516515306561/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (356771293/10000000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(126516515306561/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1313 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (5195/1024:ℝ)) : (71079411/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1150485591/5000000000:ℝ) := by nlinarith
  have hc1 : (194728849477/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194728849477/200000000000:ℝ) ≤ taylorCos (1150485591/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194728849477/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4561441709/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3984515096533/250000000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26377467683141/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-751995507923/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507043537743981/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (507043537743981/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (71079411/2000000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(507043537743981/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1314 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (325/64:ℝ)) : (354029429/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970031250923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-242980182203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15953400194011/1000000000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26402855043761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6415370529213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508021955500541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (508021955500541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (354029429/10000000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(508021955500541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1315 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (2605/512:ℝ)) : (43914233/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2761165419/10000000000:ℝ) := by nlinarith
  have hc1 : (192424280397/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192424280397/200000000000:ℝ) ≤ taylorCos (2761165419/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-192424280397/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27262135779/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15984079809769/1000000000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26453629764999/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-450739029063/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50998161473013/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (50998161473013/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (43914233/1250000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(50998161473013/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1316 (x : ℝ) (h₁ : (2585/512:ℝ) ≤ x) (h₂ : x ≤ (1305/256:ℝ)) : (43578037/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1533980787/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/1250000000:ℝ) := by nlinarith
  have hc1 : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190661207617/200000000000:ℝ) ≤ taylorCos (383495197/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (494128785003/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1533980787/10000000000:ℝ) + taylorErr ≤ (494128785003/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152797182909/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152797182909/1000000000000:ℝ) ≤ taylorSin (1533980787/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494128785003/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-190661207617/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-302005951603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152797182909/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15861361346737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16014759425527/1000000000000:ℝ) := by nlinarith
  have hp1 : (13125265263961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13252202243119/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4002243949269/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4011007114533/1000000000000:ℝ) := by nlinarith
  have hN : (3022749544527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127986259728753/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3022749544527/1000000000000:ℝ) (127986259728753/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (43578037/1250000000000:ℝ) ≤ ((3022749544527/1000000000000:ℝ)/(127986259728753/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1317 (x : ℝ) (h₁ : (10341/2048:ℝ) ≤ x) (h₂ : x ≤ (41475/8192:ℝ)) : (367971747/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (395000053/2000000000:ℝ) := by nlinarith
  have hc1 : (490280090241/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (490280090241/500000000000:ℝ) ≤ taylorCos (395000053/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (49054643577/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/2000000000:ℝ) + taylorErr ≤ (49054643577/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-490280090241/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-49054643577/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (634515813101/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1590546329439/100000000000:ℝ) := by nlinarith
  have hp1 : (525061385279/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26323519541827/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5165163475267/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-15824957451/3906250000:ℝ) := by nlinarith
  have hN : (3063167088039/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (63120940652297/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3063167088039/1000000000000:ℝ) (63120940652297/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (367971747/10000000000000:ℝ) ≤ ((3063167088039/1000000000000:ℝ)/(63120940652297/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1318 (x : ℝ) (h₁ : (10341/2048:ℝ) ≤ x) (h₂ : x ≤ (20753/4096:ℝ)) : (183435743/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (16358467/78125000:ℝ) := by nlinarith
  have hc1 : (489079114133/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (489079114133/500000000000:ℝ) ≤ taylorCos (16358467/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-489079114133/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-10393083877/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (634515813101/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1989668955687/125000000000:ℝ) := by nlinarith
  have hp1 : (525061385279/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26343194746307/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5475740651731/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-15824957451/3906250000:ℝ) := by nlinarith
  have hN : (3063167088039/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505724166812749/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3063167088039/1000000000000:ℝ) (505724166812749/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (183435743/5000000000000:ℝ) ≤ ((3063167088039/1000000000000:ℝ)/(505724166812749/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1319 (x : ℝ) (h₁ : (10341/2048:ℝ) ≤ x) (h₂ : x ≤ (20773/4096:ℝ)) : (73091573/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (449456371/2000000000:ℝ) := by nlinarith
  have hc1 : (48742735617/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (48742735617/50000000000:ℝ) ≤ taylorCos (449456371/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-48742735617/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-111420696491/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (634515813101/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127461531627/8000000000:ℝ) := by nlinarith
  have hp1 : (525061385279/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13184291053463/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1469002891917/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-15824957451/3906250000:ℝ) := by nlinarith
  have hN : (3063167088039/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (253350656948449/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3063167088039/1000000000000:ℝ) (253350656948449/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (73091573/2000000000000:ℝ) ≤ ((3063167088039/1000000000000:ℝ)/(253350656948449/500000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
