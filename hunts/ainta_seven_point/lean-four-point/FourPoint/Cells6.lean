import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_360 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (199/64:ℝ)) : (162913869/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_361 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (801/256:ℝ)) : (635452827/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_362 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (3139/1024:ℝ)) : (930293373/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_363 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (393/128:ℝ)) : (924357731/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_364 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (393/128:ℝ)) : (9367789/78125000000:ℝ) ≤ wfun x := by
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

theorem wc_365 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (1577/512:ℝ)) : (591930551/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_366 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (791/256:ℝ)) : (1168886057/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_367 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (1587/512:ℝ)) : (288536823/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_368 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (199/64:ℝ)) : (569820171/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_369 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (791/256:ℝ)) : (1810022563/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_370 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (199/64:ℝ)) : (1764735511/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_371 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (801/256:ℝ)) : (215107179/1250000000000:ℝ) ≤ wfun x := by
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

theorem wc_372 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (403/128:ℝ)) : (419583999/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_373 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (811/256:ℝ)) : (1637121129/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_374 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (51/16:ℝ)) : (798582451/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_375 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (413/128:ℝ)) : (1520846759/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_376 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (13/4:ℝ)) : (1477240831/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_377 (x : ℝ) (h₁ : (1577/512:ℝ) ≤ x) (h₂ : x ≤ (1597/512:ℝ)) : (124770657/500000000000:ℝ) ≤ wfun x := by
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

theorem wc_378 (x : ℝ) (h₁ : (791/256:ℝ) ≤ x) (h₂ : x ≤ (801/256:ℝ)) : (1670535297/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_379 (x : ℝ) (h₁ : (791/256:ℝ) ≤ x) (h₂ : x ≤ (403/128:ℝ)) : (1629257293/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_380 (x : ℝ) (h₁ : (791/256:ℝ) ≤ x) (h₂ : x ≤ (811/256:ℝ)) : (1589247651/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2822524649/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (5276893911/10000000000:ℝ) := by nlinarith
  have hc1 : (34558914153/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (34558914153/40000000000:ℝ) ≤ taylorCos (5276893911/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (960430521697/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2822524649/10000000000:ℝ) + taylorErr ≤ (960430521697/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (55703937411/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (55703937411/200000000000:ℝ) ≤ taylorSin (2822524649/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-960430521697/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-34558914153/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-251769193023/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-55703937411/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (485351521287/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9952467351803/1000000000000:ℝ) := by nlinarith
  have hp1 : (8032560792103/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16471319569609/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8293941672129/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4474452636133/1000000000000:ℝ) := by nlinarith
  have hN : (878505528609/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19710321277741/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (878505528609/250000000000:ℝ) (19710321277741/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1589247651/5000000000000:ℝ) ≤ ((878505528609/250000000000:ℝ)/(19710321277741/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_381 (x : ℝ) (h₁ : (791/256:ℝ) ≤ x) (h₂ : x ≤ (51/16:ℝ)) : (3100919687/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2822524649/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (960430521697/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2822524649/10000000000:ℝ) + taylorErr ≤ (960430521697/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (55703937411/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (55703937411/200000000000:ℝ) ≤ taylorSin (2822524649/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-960430521697/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22222809413/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-55703937411/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (485351521287/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5006913291659/500000000000:ℝ) := by nlinarith
  have hp1 : (8032560792103/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4143217253021/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4603696368527/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4474452636133/1000000000000:ℝ) := by nlinarith
  have hN : (878505528609/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (199553445681533/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (878505528609/250000000000:ℝ) (199553445681533/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3100919687/10000000000000:ℝ) ≤ ((878505528609/250000000000:ℝ)/(199553445681533/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_382 (x : ℝ) (h₁ : (1587/512:ℝ) ≤ x) (h₂ : x ≤ (809/256:ℝ)) : (2090005161/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (3129320807/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1006291397/2000000000:ℝ) := by nlinarith
  have hc1 : (876070091897/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (876070091897/1000000000000:ℝ) ≤ taylorCos (1006291397/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (23785875581/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (3129320807/10000000000:ℝ) + taylorErr ≤ (23785875581/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (38481204719/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (38481204719/125000000000:ℝ) ≤ taylorSin (3129320807/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-23785875581/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-876070091897/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-241091887203/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-38481204719/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4868855020749/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2481980914799/250000000000:ℝ) := by nlinarith
  have hp1 : (16115896304763/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16430699792617/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-990327105267/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-496127283947/100000000000:ℝ) := by nlinarith
  have hN : (400983781623/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12257958522853/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (400983781623/100000000000:ℝ) (12257958522853/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2090005161/5000000000000:ℝ) ≤ ((400983781623/100000000000:ℝ)/(12257958522853/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_383 (x : ℝ) (h₁ : (199/64:ℝ) ≤ x) (h₂ : x ≤ (811/256:ℝ)) : (5223624809/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (5276893911/10000000000:ℝ) := by nlinarith
  have hc1 : (34558914153/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (34558914153/40000000000:ℝ) ≤ taylorCos (5276893911/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-470772033737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-34558914153/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-251769193023/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1953677931451/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9952467351803/1000000000000:ℝ) := by nlinarith
  have hp1 : (16166671025319/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16471319569609/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8293941672129/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5446387393677/1000000000000:ℝ) := by nlinarith
  have hN : (4504843326203/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19710321277741/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4504843326203/1000000000000:ℝ) (19710321277741/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5223624809/10000000000000:ℝ) ≤ ((4504843326203/1000000000000:ℝ)/(19710321277741/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_384 (x : ℝ) (h₁ : (199/64:ℝ) ≤ x) (h₂ : x ≤ (51/16:ℝ)) : (5096134953/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-470772033737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22222809413/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1953677931451/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5006913291659/500000000000:ℝ) := by nlinarith
  have hp1 : (16166671025319/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4143217253021/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4603696368527/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5446387393677/1000000000000:ℝ) := by nlinarith
  have hN : (4504843326203/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (199553445681533/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4504843326203/1000000000000:ℝ) (199553445681533/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5096134953/10000000000000:ℝ) ≤ ((4504843326203/1000000000000:ℝ)/(199553445681533/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_385 (x : ℝ) (h₁ : (199/64:ℝ) ≤ x) (h₂ : x ≤ (413/128:ℝ)) : (37911123/78125000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (889708857/1250000000:ℝ) := by nlinarith
  have hc1 : (151441768839/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (151441768839/200000000000:ℝ) ≤ taylorCos (889708857/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-470772033737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-151441768839/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-65317284523/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1953677931451/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10136545046349/1000000000000:ℝ) := by nlinarith
  have hp1 : (16166671025319/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16775967897037/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2191521336559/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5446387393677/1000000000000:ℝ) := by nlinarith
  have hN : (4504843326203/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8179963638133/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4504843326203/1000000000000:ℝ) (8179963638133/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37911123/78125000000:ℝ) ≤ ((4504843326203/1000000000000:ℝ)/(8179963638133/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_386 (x : ℝ) (h₁ : (199/64:ℝ) ≤ x) (h₂ : x ≤ (13/4:ℝ)) : (589186081/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-470772033737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1953677931451/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10210176124167/1000000000000:ℝ) := by nlinarith
  have hp1 : (16166671025319/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16897827228007/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11948568258389/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5446387393677/1000000000000:ℝ) := by nlinarith
  have hN : (4504843326203/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10374769648651/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4504843326203/1000000000000:ℝ) (10374769648651/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (589186081/1250000000000:ℝ) ≤ ((4504843326203/1000000000000:ℝ)/(10374769648651/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_387 (x : ℝ) (h₁ : (403/128:ℝ) ≤ x) (h₂ : x ≤ (13/4:ℝ)) : (9713220361/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (932660319/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (178644860693/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (932660319/2000000000:ℝ) + taylorErr ≤ (178644860693/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (449611327377/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (449611327377/1000000000000:ℝ) ≤ taylorSin (932660319/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-178644860693/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-449611327377/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4945554060143/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10210176124167/1000000000000:ℝ) := by nlinarith
  have hp1 : (16369769907547/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16897827228007/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11948568258389/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1840008494247/250000000000:ℝ) := by nlinarith
  have hN : (6466809673523/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10374769648651/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6466809673523/1000000000000:ℝ) (10374769648651/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9713220361/10000000000000:ℝ) ≤ ((6466809673523/1000000000000:ℝ)/(10374769648651/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_388 (x : ℝ) (h₁ : (809/256:ℝ) ≤ x) (h₂ : x ≤ (13/4:ℝ)) : (11532825879/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (628932123/1250000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (87607009647/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (628932123/1250000000:ℝ) + taylorErr ≤ (87607009647/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (241091884897/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (241091884897/500000000000:ℝ) ≤ taylorSin (628932123/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-87607009647/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-241091884897/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1985584731839/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10210176124167/1000000000000:ℝ) := by nlinarith
  have hp1 : (3286139914443/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16897827228007/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11948568258389/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7922616660083/1000000000000:ℝ) := by nlinarith
  have hN : (7046546563613/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10374769648651/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7046546563613/1000000000000:ℝ) (10374769648651/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11532825879/10000000000000:ℝ) ≤ ((7046546563613/1000000000000:ℝ)/(10374769648651/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_389 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (209/64:ℝ)) : (1799437923/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (7363107781/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (740951127621/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (7363107781/10000000000:ℝ) + taylorErr ≤ (740951127621/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (671558952519/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (671558952519/1000000000000:ℝ) ≤ taylorSin (7363107781/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-671558952519/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-740951127621/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (512963175469/50000000000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16979066781989/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3145164669517/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (209504975509793/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (209504975509793/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1799437923/625000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(209504975509793/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_390 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (105/32:ℝ)) : (7060987389/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6872233929/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (24156576739/31250000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6872233929/10000000000:ℝ) + taylorErr ≤ (24156576739/31250000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (158598320461/250000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (158598320461/250000000000:ℝ) ≤ taylorSin (6872233929/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-158598320461/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24156576739/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (20133497841/1953125000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17060306335969/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6593897587131/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (26440524541509/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (26440524541509/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7060987389/2500000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(26440524541509/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_391 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (423/128:ℝ)) : (27447518209/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6135923151/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (817584815439/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6135923151/10000000000:ℝ) + taylorErr ≤ (817584815439/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (575808189111/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (575808189111/1000000000000:ℝ) ≤ taylorSin (6135923151/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-575808189111/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-817584815439/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10381981972411/1000000000000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17182165666941/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-14047877745649/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (107285549675467/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (107285549675467/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (27447518209/10000000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(107285549675467/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_392 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (107/32:ℝ)) : (5236311191/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (4908738521/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (881921266621/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (4908738521/10000000000:ℝ) + taylorErr ≤ (881921266621/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (471396734543/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (471396734543/1000000000000:ℝ) ≤ taylorSin (4908738521/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-471396734543/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-881921266621/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10504700435441/1000000000000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4346316137973/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7666217267073/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (219697462476709/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (219697462476709/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5236311191/2000000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(219697462476709/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_393 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (219/64:ℝ)) : (23861384437/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-242980177581/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-60626953467/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10750137361503/1000000000000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4447865580449/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3451654906539/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (115065453291183/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (115065453291183/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (23861384437/10000000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(115065453291183/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_394 (x : ℝ) (h₁ : (105/32:ℝ) ≤ x) (h₂ : x ≤ (421/128:ℝ)) : (34886068921/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797003/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (687223393/1000000000:ℝ) := by nlinarith
  have hc1 : (38650522553/50000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38650522553/50000000000:ℝ) ≤ taylorCos (687223393/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (157669285983/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797003/10000000000:ℝ) + taylorErr ≤ (157669285983/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (123046317653/200000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (123046317653/200000000000:ℝ) ≤ taylorSin (6626797003/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (317196643223/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/1000000000:ℝ) + taylorErr ≤ (317196643223/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-317196643223/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123046317653/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-157669285983/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-38650522553/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (10308350894591/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5166447293599/500000000000:ℝ) := by nlinarith
  have hp1 : (17060306107121/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17100926112959/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-842590878087/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-13187794919087/1000000000000:ℝ) := by nlinarith
  have hN : (12553401632641/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (53134355275073/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12553401632641/1000000000000:ℝ) (53134355275073/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (34886068921/10000000000000:ℝ) ≤ ((12553401632641/1000000000000:ℝ)/(53134355275073/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_395 (x : ℝ) (h₁ : (421/128:ℝ) ≤ x) (h₂ : x ≤ (211/64:ℝ)) : (9074663383/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6381360077/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (1656699251/2500000000:ℝ) := by nlinarith
  have hc1 : (788346425329/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (788346425329/1000000000000:ℝ) ≤ taylorCos (1656699251/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (803207533769/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6381360077/10000000000:ℝ) + taylorErr ≤ (803207533769/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (595699302181/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (595699302181/1000000000000:ℝ) ≤ taylorSin (6381360077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (153807898217/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/2500000000:ℝ) + taylorErr ≤ (153807898217/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-153807898217/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-595699302181/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-803207533769/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-788346425329/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (10332894587197/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2589359569951/250000000000:ℝ) := by nlinarith
  have hp1 : (8550462941783/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17141545889949/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2753643759851/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-107851630321/8000000000:ℝ) := by nlinarith
  have hN : (12866222197257/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (213553055439899/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12866222197257/1000000000000:ℝ) (213553055439899/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9074663383/2500000000000:ℝ) ≤ ((12866222197257/1000000000000:ℝ)/(213553055439899/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_396 (x : ℝ) (h₁ : (211/64:ℝ) ≤ x) (h₂ : x ≤ (53/16:ℝ)) : (37331393477/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (235619449/400000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (207867403647/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (235619449/400000000:ℝ) + taylorErr ≤ (207867403647/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (555570230717/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (555570230717/1000000000000:ℝ) ≤ taylorSin (235619449/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-297849653393/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-555570230717/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-207867403647/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160641505837/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (10357438279803/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10406525665017/1000000000000:ℝ) := by nlinarith
  have hp1 : (4285386415003/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17222785443931/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7160111387599/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1376821853599/100000000000:ℝ) := by nlinarith
  have hN : (3293129807301/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (53897888208329/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3293129807301/250000000000:ℝ) (53897888208329/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37331393477/10000000000000:ℝ) ≤ ((3293129807301/250000000000:ℝ)/(53897888208329/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_397 (x : ℝ) (h₁ : (53/16:ℝ) ≤ x) (h₂ : x ≤ (27/8:ℝ)) : (7562713/2000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (22222809413/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/5000000000:ℝ) + taylorErr ≤ (22222809413/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-22222809413/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-95670857503/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-923879534811/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1300815708127/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5301437602933/500000000000:ℝ) := by nlinarith
  have hp1 : (2152848151613/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (8773871829927/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-16212001249449/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-447506953257/31250000000:ℝ) := by nlinarith
  have hN : (13764652268899/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (218595630139/976562500:ℝ) := by nlinarith
  have hfin := wfun_ge x (13764652268899/1000000000000:ℝ) (218595630139/976562500:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7562713/2000000000:ℝ) ≤ ((13764652268899/1000000000000:ℝ)/(218595630139/976562500:ℝ))^2 := by norm_num
  linarith

theorem wc_398 (x : ℝ) (h₁ : (27/8:ℝ) ≤ x) (h₂ : x ≤ (7/2:ℝ)) : (43210796373/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-95670858657/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-500000001131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-923879530249/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2120575041173/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2199114857513/200000000000:ℝ) := by nlinarith
  have hp1 : (17547743424467/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (18197660091701/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3639532026573/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-8106000475963/500000000000:ℝ) := by nlinarith
  have hN : (7914658758649/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (120402653913361/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7914658758649/500000000000:ℝ) (120402653913361/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (43210796373/10000000000000:ℝ) ≤ ((7914658758649/500000000000:ℝ)/(120402653913361/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_399 (x : ℝ) (h₁ : (7/2:ℝ) ≤ x) (h₂ : x ≤ (29/8:ℝ)) : (1058437871/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (7/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (7/2:ℝ)) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (7/2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (7/2:ℝ))) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hcxl : (-1131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-500000001131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-923879530249/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2748893571891/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (711767085579/62500000000:ℝ) := by nlinarith
  have hp1 : (4549414961899/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (18847576523547/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-18847576566181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4203111357907/250000000000:ℝ) := by nlinarith
  have hN : (8406222714683/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4037274072909/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (8406222714683/500000000000:ℝ) (4037274072909/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1058437871/250000000000:ℝ) ≤ ((8406222714683/500000000000:ℝ)/(4037274072909/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_400 (x : ℝ) (h₁ : (29/8:ℝ) ≤ x) (h₂ : x ≤ (59/16:ℝ)) : (9010606921/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * (x - (7/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (7/2:ℝ)) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (7/2:ℝ))) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (7/2:ℝ))) ≤ (22222809413/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/5000000000:ℝ) + taylorErr ≤ (22222809413/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hcxl : (95670857503/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (22222809413/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-923879534811/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (11388273369263/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (11584622910113/1000000000000:ℝ) := by nlinarith
  have hp1 : (753903050829/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1917253473947/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-14170489981/800000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3134237378283/200000000000:ℝ) := by nlinarith
  have hN : (16053870321427/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (26740697593903/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (16053870321427/1000000000000:ℝ) (26740697593903/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9010606921/2500000000000:ℝ) ≤ ((16053870321427/1000000000000:ℝ)/(26740697593903/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_401 (x : ℝ) (h₁ : (59/16:ℝ) ≤ x) (h₂ : x ≤ (237/64:ℝ)) : (35001008619/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (235619449/400000000:ℝ) ≤ Real.pi * (x - (7/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (7/2:ℝ)) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (7/2:ℝ))) ≤ (207867403647/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (235619449/400000000:ℝ) + taylorErr ≤ (207867403647/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (555570230717/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (555570230717/1000000000000:ℝ) ≤ taylorSin (235619449/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (7/2:ℝ))) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hcxl : (555570230717/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (297849653393/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-207867403647/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160641505837/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (362019465941/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (465348411813/40000000000:ℝ) := by nlinarith
  have hp1 : (19172534482289/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (385075485869/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-800446414557/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-15399524049733/1000000000000:ℝ) := by nlinarith
  have hN : (319101885609/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (134843215235551/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (319101885609/20000000000:ℝ) (134843215235551/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (35001008619/10000000000000:ℝ) ≤ ((319101885609/20000000000:ℝ)/(134843215235551/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_402 (x : ℝ) (h₁ : (237/64:ℝ) ≤ x) (h₂ : x ≤ (15/4:ℝ)) : (26396659657/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6381360077/10000000000:ℝ) ≤ Real.pi * (x - (7/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (7/2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (7/2:ℝ))) ≤ (803207533769/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6381360077/10000000000:ℝ) + taylorErr ≤ (803207533769/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (595699302181/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (595699302181/1000000000000:ℝ) ≤ taylorSin (6381360077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (7/2:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hcxl : (595699302181/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-803207533769/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2908427573831/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5890486225481/500000000000:ℝ) := by nlinarith
  have hp1 : (19253774035179/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (19497492955393/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-783026661569/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1701809267239/125000000000:ℝ) := by nlinarith
  have hN : (14210173440093/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (69145655945163/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14210173440093/1000000000000:ℝ) (69145655945163/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (26396659657/10000000000000:ℝ) ≤ ((14210173440093/1000000000000:ℝ)/(69145655945163/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_403 (x : ℝ) (h₁ : (15/4:ℝ) ≤ x) (h₂ : x ≤ (10143/2560:ℝ)) : (957611737/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1190369091/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (992923471399/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1190369091/10000000000:ℝ) + taylorErr ≤ (992923471399/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (118755984693/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (118755984693/1000000000000:ℝ) ≤ taylorSin (1190369091/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (992923471399/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-118755984693/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (11780972450961/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (622366685261/50000000000:ℝ) := by nlinarith
  have hp1 : (4874373173463/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20600319900683/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1456662594289/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1157721971951/500000000000:ℝ) := by nlinarith
  have hN : (302255072271/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77218058184553/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (302255072271/100000000000:ℝ) (77218058184553/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (957611737/10000000000000:ℝ) ≤ ((302255072271/100000000000:ℝ)/(77218058184553/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_404 (x : ℝ) (h₁ : (999/256:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (91689533/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (383495197/1250000000:ℝ) := by nlinarith
  have hc1 : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190661207617/200000000000:ℝ) ≤ taylorCos (383495197/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (302005951603/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/1250000000:ℝ) + taylorErr ≤ (302005951603/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-302005951603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6129787228391/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (20289578334541/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6280916174791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (953305991041/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (953305991041/1000000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (91689533/10000000000000:ℝ) ≤ ((953305991041/1000000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_405 (x : ℝ) (h₁ : (63/16:ℝ) ≤ x) (h₂ : x ≤ (509/128:ℝ)) : (319416431/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (24386290541/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1963495409/10000000000:ℝ) + taylorErr ≤ (24386290541/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498645229471/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24386290541/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-73564561319/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12370021073509/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12492739536541/1000000000000:ℝ) := by nlinarith
  have hp1 : (4094473465709/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10337733244057/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4033583462799/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-301208144337/200000000000:ℝ) := by nlinarith
  have hN : (310853249977/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (31113708225571/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (310853249977/125000000000:ℝ) (31113708225571/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (319416431/5000000000000:ℝ) ≤ ((310853249977/125000000000:ℝ)/(31113708225571/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_406 (x : ℝ) (h₁ : (63/16:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (38435113/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (24386290541/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1963495409/10000000000:ℝ) + taylorErr ≤ (24386290541/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24386290541/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12370021073509/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (4094473465709/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1013348694117/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-125613696543/500000000000:ℝ) := by nlinarith
  have hN : (1232012671217/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1232012671217/1000000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38435113/2500000000000:ℝ) ≤ ((1232012671217/1000000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_407 (x : ℝ) (h₁ : (1009/256:ℝ) ≤ x) (h₂ : x ≤ (4087/1024:ℝ)) : (122092393/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (276116541/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (24990470619/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (276116541/10000000000:ℝ) + taylorErr ≤ (24990470619/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5521628687/200000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5521628687/200000000000:ℝ) ≤ taylorSin (276116541/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (24990470619/25000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5521628687/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3095573229953/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6269379480089/500000000000:ℝ) := by nlinarith
  have hp1 : (40024760189/1953125000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5187907142493/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-949593954093/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-565764771967/1000000000000:ℝ) := by nlinarith
  have hN : (774435128563/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (313440952522889/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (774435128563/500000000000:ℝ) (313440952522889/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (122092393/5000000000000:ℝ) ≤ ((774435128563/500000000000:ℝ)/(313440952522889/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_408 (x : ℝ) (h₁ : (1009/256:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (48755691/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3095573229953/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (40024760189/1953125000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-761348047167/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (196621087623/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (196621087623/200000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (48755691/5000000000000:ℝ) ≤ ((196621087623/200000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_409 (x : ℝ) (h₁ : (1013/256:ℝ) ≤ x) (h₂ : x ≤ (2041/512:ℝ)) : (71867913/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/500000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999077730017/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/500000000:ℝ) + taylorErr ≤ (999077730017/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (10734563653/250000000000:ℝ) ≤ taylorSin (21475731/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999077730017/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-10734563653/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (497255212201/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12523419152299/1000000000000:ℝ) := by nlinarith
  have hp1 : (1028695838483/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20726241209353/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2789352274893/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-883408076621/1000000000000:ℝ) := by nlinarith
  have hN : (937155354889/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (312672054528339/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (937155354889/500000000000:ℝ) (312672054528339/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (71867913/2000000000000:ℝ) ≤ ((937155354889/500000000000:ℝ)/(312672054528339/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_410 (x : ℝ) (h₁ : (1013/256:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (31317919/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (497255212201/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (1028695838483/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-279618557297/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-252473560711/1000000000000:ℝ) := by nlinarith
  have hN : (310844048467/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (310844048467/250000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (31317919/2000000000000:ℝ) ≤ ((310844048467/250000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_411 (x : ℝ) (h₁ : (507/128:ℝ) ≤ x) (h₂ : x ≤ (8183/2048:ℝ)) : (82600037/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (13805827/1000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (1227184631/10000000000:ℝ) := by nlinarith
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (499952351673/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (13805827/1000000000:ℝ) + taylorErr ≤ (499952351673/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (552215447/40000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (552215447/40000000000:ℝ) ≤ taylorSin (13805827/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499952351673/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-552215447/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (388864129729/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12552564787269/1000000000000:ℝ) := by nlinarith
  have hp1 : (10297113328941/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20774477194529/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1271508914357/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-284311251987/1000000000000:ℝ) := by nlinarith
  have hN : (255358156863/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78533441369293/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (255358156863/200000000000:ℝ) (78533441369293/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (82600037/5000000000000:ℝ) ≤ ((255358156863/200000000000:ℝ)/(78533441369293/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_412 (x : ℝ) (h₁ : (507/128:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (99379817/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (1227184631/10000000000:ℝ) := by nlinarith
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (388864129729/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10297113328941/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2545814744327/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (248119871321/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (248119871321/250000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (99379817/10000000000000:ℝ) ≤ ((248119871321/250000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_413 (x : ℝ) (h₁ : (2031/512:ℝ) ≤ x) (h₂ : x ≤ (2041/512:ℝ)) : (11299473/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/500000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (130388367/1250000000:ℝ) := by nlinarith
  have hc1 : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99456456847/100000000000:ℝ) ≤ taylorCos (130388367/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999077730017/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/500000000:ℝ) + taylorErr ≤ (999077730017/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (10734563653/250000000000:ℝ) ≤ taylorSin (21475731/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (52060818079/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/1250000000:ℝ) + taylorErr ≤ (52060818079/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999077730017/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52060818079/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-10734563653/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12523419152299/1000000000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20726241209353/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-539512536531/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1771176509/2000000000:ℝ) := by nlinarith
  have hN : (188015282297/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (312672054528339/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (188015282297/100000000000:ℝ) (312672054528339/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11299473/312500000000:ℝ) ≤ ((188015282297/100000000000:ℝ)/(312672054528339/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_414 (x : ℝ) (h₁ : (2031/512:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (157670757/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (130388367/1250000000:ℝ) := by nlinarith
  have hc1 : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99456456847/100000000000:ℝ) ≤ taylorCos (130388367/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (52060818079/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/1250000000:ℝ) + taylorErr ≤ (52060818079/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52060818079/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1081668446587/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-253096644523/1000000000000:ℝ) := by nlinarith
  have hN : (1247661212993/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1247661212993/1000000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (157670757/10000000000000:ℝ) ≤ ((1247661212993/1000000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_415 (x : ℝ) (h₁ : (4067/1024:ℝ) ≤ x) (h₂ : x ≤ (8185/2048:ℝ)) : (30026951/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/2000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (889708857/10000000000:ℝ) := by nlinarith
  have hc1 : (996044698639/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996044698639/1000000000000:ℝ) ≤ taylorCos (889708857/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (499971175969/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/2000000000:ℝ) + taylorErr ≤ (499971175969/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1073765689/100000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1073765689/100000000000:ℝ) ≤ taylorSin (21475731/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (88853554847/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/10000000000:ℝ) + taylorErr ≤ (88853554847/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (996044698639/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499971175969/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-88853554847/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1073765689/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12477399728661/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3138908187211/250000000000:ℝ) := by nlinarith
  have hp1 : (10325039425247/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5194888666663/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-184633730027/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-27716682681/125000000000:ℝ) := by nlinarith
  have hN : (1217778160087/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39285978430961/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1217778160087/1000000000000:ℝ) (39285978430961/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (30026951/2000000000000:ℝ) ≤ ((1217778160087/1000000000000:ℝ)/(39285978430961/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_416 (x : ℝ) (h₁ : (4067/1024:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (2502377/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (889708857/10000000000:ℝ) := by nlinarith
  have hc1 : (996044698639/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996044698639/1000000000000:ℝ) ≤ taylorCos (889708857/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (88853554847/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/10000000000:ℝ) + taylorErr ≤ (88853554847/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (996044698639/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-88853554847/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12477399728661/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10325039425247/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-923958165169/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (199208930319/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (199208930319/200000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2502377/250000000000:ℝ) ≤ ((199208930319/200000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_417 (x : ℝ) (h₁ : (8143/2048:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (100322671/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1561400694469/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (4134585494949/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1561760690871/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (498588193711/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (498588193711/500000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (100322671/10000000000000:ℝ) ≤ ((498588193711/500000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_418 (x : ℝ) (h₁ : (509/128:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (39629583/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (736310779/10000000000:ℝ) := by nlinarith
  have hc1 : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997290454411/1000000000000:ℝ) ≤ taylorCos (736310779/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (73564565943/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (736310779/10000000000:ℝ) + taylorErr ≤ (73564565943/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73564565943/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (20675466210773/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-61138086341/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-50743945667/200000000000:ℝ) := by nlinarith
  have hN : (625505091373/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (625505091373/500000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (39629583/2500000000000:ℝ) ≤ ((625505091373/500000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_419 (x : ℝ) (h₁ : (509/128:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (20069123/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (736310779/10000000000:ℝ) := by nlinarith
  have hc1 : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997290454411/1000000000000:ℝ) ≤ taylorCos (736310779/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (73564565943/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (736310779/10000000000:ℝ) + taylorErr ≤ (73564565943/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73564565943/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (20675466210773/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1529946246657/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (997290407367/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (997290407367/1000000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (20069123/2000000000000:ℝ) ≤ ((997290407367/1000000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
