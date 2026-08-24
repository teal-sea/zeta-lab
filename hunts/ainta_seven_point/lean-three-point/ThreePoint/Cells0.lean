import ThreePoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.ThreePoint


theorem wc_0 (x : ℝ) (h₁ : (1/2:ℝ) ≤ x) (h₂ : x ≤ (3/4:ℝ)) : (66207635573/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (1/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1/2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1/2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1/2:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1/2:ℝ))) := by
    have h := (trig_shift (1/2:ℝ) (x - (1/2:ℝ))).1
    rw [show (1/2:ℝ) + (x - (1/2:ℝ)) = x by ring, cs_h1.1, cs_h1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (1/2:ℝ))) := by
    have h := (trig_shift (1/2:ℝ) (x - (1/2:ℝ))).2
    rw [show (1/2:ℝ) + (x - (1/2:ℝ)) = x by ring, cs_h1.1, cs_h1.2] at h
    rw [h]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (785398163397/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2356194490193/1000000000000:ℝ) := by nlinarith
  have hp1 : (81239552891/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (97487464777/25000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1838241233809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3899498599901/1000000000000:ℝ) := by nlinarith
  have hN : (1838241231547/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157864139863/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1838241231547/1000000000000:ℝ) (157864139863/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (66207635573/2000000000000:ℝ) ≤ ((1838241231547/1000000000000:ℝ)/(157864139863/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1 (x : ℝ) (h₁ : (3/4:ℝ) ≤ x) (h₂ : x ≤ (1:ℝ)) : (14238606443/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((1:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((1:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((1:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((1:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (147262155637/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/100000000000:ℝ) := by nlinarith
  have hp1 : (389949853877/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1299832863693/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11761/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (919120635261/250000000000:ℝ) := by nlinarith
  have hN : (707106767047/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9369604401091/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (707106767047/1000000000000:ℝ) (9369604401091/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14238606443/10000000000000:ℝ) ≤ ((707106767047/1000000000000:ℝ)/(9369604401091/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_2 (x : ℝ) (h₁ : (1:ℝ) ≤ x) (h₂ : x ≤ (65/64:ℝ)) : (7298263069/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (490873853/10000000000:ℝ) := by nlinarith
  have hc1 : (998795453939/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998795453939/1000000000000:ℝ) ≤ taylorCos (490873853/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (49067676677/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (490873853/10000000000:ℝ) + taylorErr ≤ (49067676677/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-998795453939/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-49067676677/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3141592653589/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3190680038803/1000000000000:ℝ) := by nlinarith
  have hp1 : (2599665692513/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2640285504377/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-16194084433/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2389/200000000000:ℝ) := by nlinarith
  have hN : (739690103011/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75628430547/3906250000:ℝ) := by nlinarith
  have hfin := wfun_ge x (739690103011/1000000000000:ℝ) (75628430547/3906250000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7298263069/5000000000000:ℝ) ≤ ((739690103011/1000000000000:ℝ)/(75628430547/3906250000:ℝ))^2 := by norm_num
  linarith

theorem wc_3 (x : ℝ) (h₁ : (65/64:ℝ) ≤ x) (h₂ : x ≤ (263/256:ℝ)) : (7358852099/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (429514621/5000000000:ℝ) := by nlinarith
  have hc1 : (498156304957/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498156304957/500000000000:ℝ) ≤ taylorCos (429514621/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (249698864617/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2500000000:ℝ) + taylorErr ≤ (249698864617/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (49067672053/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (49067672053/1000000000000:ℝ) ≤ taylorSin (122718463/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (17159462937/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/5000000000:ℝ) + taylorErr ≤ (17159462937/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-249698864617/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-498156304957/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-17159462937/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-49067672053/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (201718473607/62500000000:ℝ) := by nlinarith
  have hp1 : (2640285468959/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5341500674239/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-229143207119/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-129552661517/500000000000:ℝ) := by nlinarith
  have hN : (134506548919/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9916727704151/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (134506548919/250000000000:ℝ) (9916727704151/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7358852099/10000000000000:ℝ) ≤ ((134506548919/250000000000:ℝ)/(9916727704151/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_4 (x : ℝ) (h₁ : (65/64:ℝ) ≤ x) (h₂ : x ≤ (133/128:ℝ)) : (2658307323/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1227184631/10000000000:ℝ) := by nlinarith
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (249698864617/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2500000000:ℝ) + taylorErr ≤ (249698864617/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (49067672053/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (49067672053/1000000000000:ℝ) ≤ taylorSin (122718463/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-249698864617/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-124059941541/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-49067672053/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3264311116621/1000000000000:ℝ) := by nlinarith
  have hp1 : (2640285468959/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1350607584931/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-132263031639/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-129552661517/500000000000:ℝ) := by nlinarith
  have hN : (331164374133/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20311454132191/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (331164374133/1000000000000:ℝ) (20311454132191/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2658307323/10000000000000:ℝ) ≤ ((331164374133/1000000000000:ℝ)/(20311454132191/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_5 (x : ℝ) (_h₁ : (65/64:ℝ) ≤ x) (_h₂ : x ≤ (17/16:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_6 (x : ℝ) (_h₁ : (65/64:ℝ) ≤ x) (_h₂ : x ≤ (71/64:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_7 (x : ℝ) (h₁ : (263/256:ℝ) ≤ x) (h₂ : x ≤ (529/512:ℝ)) : (1175437333/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (130388367/1250000000:ℝ) := by nlinarith
  have hc1 : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99456456847/100000000000:ℝ) ≤ taylorCos (130388367/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (996312614447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/10000000000:ℝ) + taylorErr ≤ (996312614447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (85797310061/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (85797310061/1000000000000:ℝ) ≤ taylorSin (859029241/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (52060818079/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/1250000000:ℝ) + taylorErr ≤ (52060818079/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-996312614447/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99456456847/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52060818079/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-85797310061/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3227495577711/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3245903347167/1000000000000:ℝ) := by nlinarith
  have hp1 : (2670750301293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2685982753491/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-139834459493/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-458286383391/1000000000000:ℝ) := by nlinarith
  have hN : (217613365249/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (200717770783/10000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (217613365249/500000000000:ℝ) (200717770783/10000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1175437333/2500000000000:ℝ) ≤ ((217613365249/500000000000:ℝ)/(200717770783/10000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_8 (x : ℝ) (h₁ : (263/256:ℝ) ≤ x) (h₂ : x ≤ (133/128:ℝ)) : (2658307323/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1227184631/10000000000:ℝ) := by nlinarith
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (996312614447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/10000000000:ℝ) + taylorErr ≤ (996312614447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (85797310061/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (85797310061/1000000000000:ℝ) ≤ taylorSin (859029241/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-996312614447/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-124059941541/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-85797310061/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3227495577711/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3264311116621/1000000000000:ℝ) := by nlinarith
  have hp1 : (2670750301293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1350607584931/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-132263031639/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-458286383391/1000000000000:ℝ) := by nlinarith
  have hN : (331164374133/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20311454132191/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (331164374133/1000000000000:ℝ) (20311454132191/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2658307323/10000000000000:ℝ) ≤ ((331164374133/1000000000000:ℝ)/(20311454132191/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_9 (x : ℝ) (h₁ : (529/512:ℝ) ≤ x) (h₂ : x ≤ (133/128:ℝ)) : (2658307323/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (208621387/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1227184631/10000000000:ℝ) := by nlinarith
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (248641143251/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (208621387/2000000000:ℝ) + taylorErr ≤ (248641143251/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (52060815767/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (52060815767/500000000000:ℝ) ≤ taylorSin (208621387/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-248641143251/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-124059941541/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-52060815767/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3264311116621/1000000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1350607584931/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-132263031639/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-139834451407/250000000000:ℝ) := by nlinarith
  have hN : (331164374133/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20311454132191/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (331164374133/1000000000000:ℝ) (20311454132191/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2658307323/10000000000000:ℝ) ≤ ((331164374133/1000000000000:ℝ)/(20311454132191/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_10 (x : ℝ) (h₁ : (133/128:ℝ) ≤ x) (h₂ : x ≤ (1067/1024:ℝ)) : (930124941/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (659611739/5000000000:ℝ) := by nlinarith
  have hc1 : (495655428789/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495655428789/500000000000:ℝ) ≤ taylorCos (659611739/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (131540031007/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (659611739/5000000000:ℝ) + taylorErr ≤ (131540031007/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495655428789/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-131540031007/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (163215555831/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (818378750337/250000000000:ℝ) := by nlinarith
  have hp1 : (2701215133627/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1083532551219/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-712639526923/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-330657562171/500000000000:ℝ) := by nlinarith
  have hN : (55734266131/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20431800928101/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (55734266131/200000000000:ℝ) (20431800928101/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (930124941/5000000000000:ℝ) ≤ ((55734266131/200000000000:ℝ)/(20431800928101/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_11 (x : ℝ) (h₁ : (133/128:ℝ) ≤ x) (h₂ : x ≤ (535/512:ℝ)) : (120785339/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (56450493/400000000:ℝ) := by nlinarith
  have hc1 : (495029103999/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495029103999/500000000000:ℝ) ≤ taylorCos (56450493/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (140658241609/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/400000000:ℝ) + taylorErr ≤ (140658241609/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495029103999/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-140658241609/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (163215555831/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (820679721519/250000000000:ℝ) := by nlinarith
  have hp1 : (2701215133627/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1358223793117/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-382090740903/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-330657562171/500000000000:ℝ) := by nlinarith
  have hN : (14117295387/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20552486570001/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14117295387/62500000000:ℝ) (20552486570001/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (120785339/1000000000000:ℝ) ≤ ((14117295387/62500000000:ℝ)/(20552486570001/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_12 (x : ℝ) (h₁ : (133/128:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (163215555831/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by nlinarith
  have hp1 : (2701215133627/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-330657562171/500000000000:ℝ) := by nlinarith
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_13 (x : ℝ) (_h₁ : (133/128:ℝ) ≤ x) (_h₂ : x ≤ (17/16:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_14 (x : ℝ) (h₁ : (1067/1024:ℝ) ≤ x) (h₂ : x ≤ (2137/2048:ℝ)) : (1516005697/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1319223477/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (682621451/5000000000:ℝ) := by nlinarith
  have hc1 : (99069502317/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99069502317/100000000000:ℝ) ≤ taylorCos (682621451/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247827715529/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1319223477/10000000000:ℝ) + taylorErr ≤ (247827715529/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (131540026383/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (131540026383/1000000000000:ℝ) ≤ taylorSin (1319223477/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (27220115503/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (682621451/5000000000:ℝ) + taylorErr ≤ (27220115503/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247827715529/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99069502317/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27220115503/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-131540026383/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3273515001347/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (102441154491/31250000000:ℝ) := by nlinarith
  have hp1 : (270883134171/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5425278964281/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-738383600219/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-712639492311/1000000000000:ℝ) := by nlinarith
  have hN : (252311422951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2561512674163/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (252311422951/1000000000000:ℝ) (2561512674163/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1516005697/10000000000000:ℝ) ≤ ((252311422951/1000000000000:ℝ)/(2561512674163/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_15 (x : ℝ) (h₁ : (1067/1024:ℝ) ≤ x) (h₂ : x ≤ (535/512:ℝ)) : (120785339/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1319223477/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (56450493/400000000:ℝ) := by nlinarith
  have hc1 : (495029103999/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495029103999/500000000000:ℝ) ≤ taylorCos (56450493/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247827715529/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1319223477/10000000000:ℝ) + taylorErr ≤ (247827715529/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (131540026383/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (131540026383/1000000000000:ℝ) ≤ taylorSin (1319223477/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (140658241609/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/400000000:ℝ) + taylorErr ≤ (140658241609/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247827715529/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495029103999/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-140658241609/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-131540026383/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3273515001347/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (820679721519/250000000000:ℝ) := by nlinarith
  have hp1 : (270883134171/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1358223793117/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-382090740903/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-712639492311/1000000000000:ℝ) := by nlinarith
  have hN : (14117295387/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20552486570001/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14117295387/62500000000:ℝ) (20552486570001/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (120785339/1000000000000:ℝ) ≤ ((14117295387/62500000000:ℝ)/(20552486570001/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_16 (x : ℝ) (h₁ : (2137/2048:ℝ) ≤ x) (h₂ : x ≤ (535/512:ℝ)) : (120785339/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1365242901/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (56450493/400000000:ℝ) := by nlinarith
  have hc1 : (495029103999/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495029103999/500000000000:ℝ) ≤ taylorCos (56450493/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247673756927/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1365242901/10000000000:ℝ) + taylorErr ≤ (247673756927/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (34025143223/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (34025143223/250000000000:ℝ) ≤ taylorSin (1365242901/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (140658241609/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/400000000:ℝ) + taylorErr ≤ (140658241609/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247673756927/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495029103999/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-140658241609/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-34025143223/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3278116943711/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (820679721519/250000000000:ℝ) := by nlinarith
  have hp1 : (1085055778301/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1358223793117/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-382090740903/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-46148972827/62500000000:ℝ) := by nlinarith
  have hN : (14117295387/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20552486570001/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14117295387/62500000000:ℝ) (20552486570001/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (120785339/1000000000000:ℝ) ≤ ((14117295387/62500000000:ℝ)/(20552486570001/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_17 (x : ℝ) (h₁ : (535/512:ℝ) ≤ x) (h₂ : x ≤ (4283/4096:ℝ)) : (533605311/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1434272037/10000000000:ℝ) := by nlinarith
  have hc1 : (989731936811/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989731936811/1000000000000:ℝ) ≤ taylorCos (1434272037/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8933497667/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1434272037/10000000000:ℝ) + taylorErr ≤ (8933497667/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989731936811/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8933497667/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (131308755443/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1642509928629/500000000000:ℝ) := by nlinarith
  have hp1 : (5432895099589/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5436703276561/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-388550208299/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-382090723219/500000000000:ℝ) := by nlinarith
  have hN : (212631520213/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20582710925159/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (212631520213/1000000000000:ℝ) (20582710925159/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (533605311/5000000000000:ℝ) ≤ ((212631520213/1000000000000:ℝ)/(20582710925159/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_18 (x : ℝ) (h₁ : (535/512:ℝ) ≤ x) (h₂ : x ≤ (2143/2048:ℝ)) : (467734771/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1457281749/10000000000:ℝ) := by nlinarith
  have hc1 : (494700212761/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494700212761/500000000000:ℝ) ≤ taylorCos (1457281749/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (29042585393/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1457281749/10000000000:ℝ) + taylorErr ≤ (29042585393/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494700212761/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-29042585393/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (131308755443/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3287320828439/1000000000000:ℝ) := by nlinarith
  have hp1 : (5432895099589/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1360127845163/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-790032581771/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-382090723219/500000000000:ℝ) := by nlinarith
  have hN : (199367843751/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10306478229089/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (199367843751/1000000000000:ℝ) (10306478229089/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (467734771/5000000000000:ℝ) ≤ ((199367843751/1000000000000:ℝ)/(10306478229089/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_19 (x : ℝ) (h₁ : (535/512:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by nlinarith
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (131308755443/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by nlinarith
  have hp1 : (5432895099589/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-382090723219/500000000000:ℝ) := by nlinarith
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_20 (x : ℝ) (h₁ : (535/512:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-123757276567/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-70329118493/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (131308755443/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by nlinarith
  have hp1 : (5432895099589/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-382090723219/500000000000:ℝ) := by nlinarith
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_21 (x : ℝ) (h₁ : (4283/4096:ℝ) ≤ x) (h₂ : x ≤ (2143/2048:ℝ)) : (467734771/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (358568009/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1457281749/10000000000:ℝ) := by nlinarith
  have hc1 : (494700212761/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494700212761/500000000000:ℝ) ≤ taylorCos (1457281749/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (19794638827/20000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (358568009/2500000000:ℝ) + taylorErr ≤ (19794638827/20000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (142935958049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (142935958049/1000000000000:ℝ) ≤ taylorSin (358568009/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (29042585393/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1457281749/10000000000:ℝ) + taylorErr ≤ (29042585393/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-19794638827/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494700212761/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-29042585393/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-142935958049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3285019857257/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3287320828439/1000000000000:ℝ) := by nlinarith
  have hp1 : (5436703203631/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1360127845163/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-790032581771/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-777100381039/1000000000000:ℝ) := by nlinarith
  have hN : (199367843751/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10306478229089/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (199367843751/1000000000000:ℝ) (10306478229089/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (467734771/5000000000000:ℝ) ≤ ((199367843751/1000000000000:ℝ)/(10306478229089/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_22 (x : ℝ) (h₁ : (2143/2048:ℝ) ≤ x) (h₂ : x ≤ (4289/4096:ℝ)) : (812589723/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1480291461/10000000000:ℝ) := by nlinarith
  have hc1 : (494531837943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494531837943/500000000000:ℝ) ≤ taylorCos (1480291461/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989400430061/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (364320437/2500000000:ℝ) + taylorErr ≤ (989400430061/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (72606461171/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (72606461171/500000000000:ℝ) ≤ taylorSin (364320437/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (73744561217/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1480291461/10000000000:ℝ) + taylorErr ≤ (73744561217/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-989400430061/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494531837943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73744561217/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-72606461171/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1643660414219/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3289621799621/1000000000000:ℝ) := by nlinarith
  have hp1 : (5440511307671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1088863896949/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-50186118941/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-790032546021/1000000000000:ℝ) := by nlinarith
  have hN : (18608577283/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5160805792271/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (18608577283/100000000000:ℝ) (5160805792271/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (812589723/10000000000000:ℝ) ≤ ((18608577283/100000000000:ℝ)/(5160805792271/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_23 (x : ℝ) (h₁ : (2143/2048:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by nlinarith
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989400430061/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (364320437/2500000000:ℝ) + taylorErr ≤ (989400430061/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (72606461171/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (72606461171/500000000000:ℝ) ≤ taylorSin (364320437/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-989400430061/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-72606461171/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1643660414219/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by nlinarith
  have hp1 : (5440511307671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-790032546021/1000000000000:ℝ) := by nlinarith
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_24 (x : ℝ) (h₁ : (4289/4096:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (74014573/500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by nlinarith
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39562547217/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (74014573/500000000:ℝ) + taylorErr ≤ (39562547217/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (14748911781/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (14748911781/100000000000:ℝ) ≤ taylorSin (74014573/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-39562547217/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-14748911781/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (164481089981/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by nlinarith
  have hp1 : (5444319411713/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-802977867109/1000000000000:ℝ) := by nlinarith
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_25 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (8587/8192:ℝ)) : (322398213/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1514806029/10000000000:ℝ) := by nlinarith
  have hc1 : (494274366719/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494274366719/500000000000:ℝ) ≤ taylorCos (1514806029/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (9431371733/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1514806029/10000000000:ℝ) + taylorErr ≤ (9431371733/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-494274366719/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-9431371733/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1646536628197/500000000000:ℝ) := by nlinarith
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1090006328177/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-822420389789/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by nlinarith
  have hN : (166128343649/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4137732588791/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (166128343649/1000000000000:ℝ) (4137732588791/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (322398213/5000000000000:ℝ) ≤ ((166128343649/1000000000000:ℝ)/(4137732588791/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_26 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (4295/4096:ℝ)) : (296626083/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (381577721/2500000000:ℝ) := by nlinarith
  have hc1 : (494187234373/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494187234373/500000000000:ℝ) ≤ taylorCos (381577721/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (38009789649/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (381577721/2500000000:ℝ) + taylorErr ≤ (38009789649/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-494187234373/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-38009789649/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (658844748397/200000000000:ℝ) := by nlinarith
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1362983923233/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-828907715473/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by nlinarith
  have hN : (159466753273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5175955031129/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (159466753273/1000000000000:ℝ) (5175955031129/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (296626083/5000000000000:ℝ) ≤ ((159466753273/1000000000000:ℝ)/(5175955031129/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_27 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (2149/2048:ℝ)) : (496713571/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (387330149/2500000000:ℝ) := by nlinarith
  have hc1 : (494011007439/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494011007439/500000000000:ℝ) ≤ taylorCos (387330149/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (77156487649/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (387330149/2500000000:ℝ) + taylorErr ≤ (77156487649/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-494011007439/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-77156487649/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3296524713167/1000000000000:ℝ) := by nlinarith
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (218229751881/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-841892057783/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by nlinarith
  have hN : (29225991419/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10367075184521/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29225991419/200000000000:ℝ) (10367075184521/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (496713571/10000000000000:ℝ) ≤ ((29225991419/200000000000:ℝ)/(10367075184521/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_28 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by nlinarith
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by nlinarith
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_29 (x : ℝ) (h₁ : (8587/8192:ℝ) ≤ x) (h₂ : x ≤ (4295/4096:ℝ)) : (296626083/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (378701507/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (381577721/2500000000:ℝ) := by nlinarith
  have hc1 : (494187234373/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494187234373/500000000000:ℝ) ≤ taylorCos (381577721/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988548737977/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (378701507/2500000000:ℝ) + taylorErr ≤ (988548737977/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (30180388621/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (30180388621/200000000000:ℝ) ≤ taylorSin (378701507/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (38009789649/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (381577721/2500000000:ℝ) + taylorErr ≤ (38009789649/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988548737977/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494187234373/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-38009789649/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-30180388621/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3293073256393/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (658844748397/200000000000:ℝ) := by nlinarith
  have hp1 : (170313486493/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1362983923233/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-828907715473/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-20560508839/25000000000:ℝ) := by nlinarith
  have hN : (159466753273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5175955031129/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (159466753273/1000000000000:ℝ) (5175955031129/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (296626083/5000000000000:ℝ) ≤ ((159466753273/1000000000000:ℝ)/(5175955031129/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_30 (x : ℝ) (h₁ : (4295/4096:ℝ) ≤ x) (h₂ : x ≤ (8593/8192:ℝ)) : (543892897/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1526310883/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (76890787/500000000:ℝ) := by nlinarith
  have hc1 : (98819889581/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (98819889581/100000000000:ℝ) ≤ taylorCos (76890787/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (494187236643/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1526310883/10000000000:ℝ) + taylorErr ≤ (494187236643/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152039153973/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152039153973/1000000000000:ℝ) ≤ taylorSin (1526310883/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (239337763/1562500000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (76890787/500000000:ℝ) + taylorErr ≤ (239337763/1562500000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-494187236643/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-98819889581/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-239337763/1562500000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152039153973/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (102944491937/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (411921778447/125000000000:ℝ) := by nlinarith
  have hp1 : (5451935619797/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2726919872489/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-52212392173/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-828907679149/1000000000000:ℝ) := by nlinarith
  have hN : (76400310521/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4143796519909/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (76400310521/500000000000:ℝ) (4143796519909/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (543892897/10000000000000:ℝ) ≤ ((76400310521/500000000000:ℝ)/(4143796519909/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_31 (x : ℝ) (h₁ : (4295/4096:ℝ) ≤ x) (h₂ : x ≤ (2149/2048:ℝ)) : (496713571/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1526310883/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (387330149/2500000000:ℝ) := by nlinarith
  have hc1 : (494011007439/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494011007439/500000000000:ℝ) ≤ taylorCos (387330149/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (494187236643/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1526310883/10000000000:ℝ) + taylorErr ≤ (494187236643/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (152039153973/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (152039153973/1000000000000:ℝ) ≤ taylorSin (1526310883/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (77156487649/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (387330149/2500000000:ℝ) + taylorErr ≤ (77156487649/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-494187236643/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494011007439/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-77156487649/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-152039153973/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (102944491937/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3296524713167/1000000000000:ℝ) := by nlinarith
  have hp1 : (5451935619797/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (218229751881/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-841892057783/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-828907679149/1000000000000:ℝ) := by nlinarith
  have hN : (29225991419/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10367075184521/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29225991419/200000000000:ℝ) (10367075184521/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (496713571/10000000000000:ℝ) ≤ ((29225991419/200000000000:ℝ)/(10367075184521/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_32 (x : ℝ) (h₁ : (8593/8192:ℝ) ≤ x) (h₂ : x ≤ (2149/2048:ℝ)) : (496713571/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1537815739/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (387330149/2500000000:ℝ) := by nlinarith
  have hc1 : (494011007439/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494011007439/500000000000:ℝ) ≤ taylorCos (387330149/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (19763978007/20000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1537815739/10000000000:ℝ) + taylorErr ≤ (19763978007/20000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (153176163697/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (153176163697/1000000000000:ℝ) ≤ taylorSin (1537815739/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (77156487649/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (387330149/2500000000:ℝ) + taylorErr ≤ (77156487649/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-19763978007/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494011007439/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-77156487649/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-153176163697/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (131814969103/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3296524713167/1000000000000:ℝ) := by nlinarith
  have hp1 : (2726919835909/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (218229751881/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-841892057783/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-835398238347/1000000000000:ℝ) := by nlinarith
  have hN : (29225991419/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10367075184521/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29225991419/200000000000:ℝ) (10367075184521/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (496713571/10000000000000:ℝ) ≤ ((29225991419/200000000000:ℝ)/(10367075184521/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_33 (x : ℝ) (h₁ : (2149/2048:ℝ) ≤ x) (h₂ : x ≤ (8599/8192:ℝ)) : (225854567/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (390206363/2500000000:ℝ) := by nlinarith
  have hc1 : (493921913091/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493921913091/500000000000:ℝ) ≤ taylorCos (390206363/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493921913091/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6217983121/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1648262356583/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1648837599379/500000000000:ℝ) := by nlinarith
  have hp1 : (5455743723839/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5457647849071/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-212097263787/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-841892021267/1000000000000:ℝ) := by nlinarith
  have hN : (69727385517/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1296832714563/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (69727385517/500000000000:ℝ) (1296832714563/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (225854567/5000000000000:ℝ) ≤ ((69727385517/500000000000:ℝ)/(1296832714563/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_34 (x : ℝ) (h₁ : (2149/2048:ℝ) ≤ x) (h₂ : x ≤ (4301/4096:ℝ)) : (81774907/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (393082577/2500000000:ℝ) := by nlinarith
  have hc1 : (24691608249/25000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (24691608249/25000000000:ℝ) ≤ taylorCos (393082577/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (39146493749/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (393082577/2500000000:ℝ) + taylorErr ≤ (39146493749/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-24691608249/25000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-39146493749/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1648262356583/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3298825684349/1000000000000:ℝ) := by nlinarith
  have hp1 : (5455743723839/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2729775950559/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-427444628739/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-841892021267/1000000000000:ℝ) := by nlinarith
  have hN : (66387536241/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10382250895721/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (66387536241/500000000000:ℝ) (10382250895721/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (81774907/2000000000000:ℝ) ≤ ((66387536241/500000000000:ℝ)/(10382250895721/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_35 (x : ℝ) (h₁ : (2149/2048:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1648262356583/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by nlinarith
  have hp1 : (5455743723839/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-841892021267/1000000000000:ℝ) := by nlinarith
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_36 (x : ℝ) (h₁ : (8599/8192:ℝ) ≤ x) (h₂ : x ≤ (4301/4096:ℝ)) : (81774907/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1560825451/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (393082577/2500000000:ℝ) := by nlinarith
  have hc1 : (24691608249/25000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (24691608249/25000000000:ℝ) ≤ taylorCos (393082577/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493921915361/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1560825451/10000000000:ℝ) + taylorErr ≤ (493921915361/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (77724786701/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (77724786701/500000000000:ℝ) ≤ taylorSin (1560825451/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (39146493749/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (393082577/2500000000:ℝ) + taylorErr ≤ (39146493749/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-24691608249/25000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-39146493749/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-77724786701/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3297675198757/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3298825684349/1000000000000:ℝ) := by nlinarith
  have hp1 : (272882388793/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2729775950559/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-427444628739/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-169677803707/200000000000:ℝ) := by nlinarith
  have hN : (66387536241/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10382250895721/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (66387536241/500000000000:ℝ) (10382250895721/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (81774907/2000000000000:ℝ) ≤ ((66387536241/500000000000:ℝ)/(10382250895721/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_37 (x : ℝ) (h₁ : (4301/4096:ℝ) ≤ x) (h₂ : x ≤ (8605/8192:ℝ)) : (4602559/125000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1572330307/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (395958791/2500000000:ℝ) := by nlinarith
  have hc1 : (61717720403/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61717720403/62500000000:ℝ) ≤ taylorCos (395958791/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (987664334499/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1572330307/10000000000:ℝ) + taylorErr ≤ (987664334499/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (156585970373/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (156585970373/1000000000000:ℝ) ≤ taylorSin (1572330307/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (39430541177/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395958791/2500000000:ℝ) + taylorErr ≤ (39430541177/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-987664334499/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61717720403/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-39430541177/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-156585970373/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (824706421087/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3299976169939/1000000000000:ℝ) := by nlinarith
  have hp1 : (5459551827881/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5461455953163/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-861392655391/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-85488922077/100000000000:ℝ) := by nlinarith
  have hN : (126090871057/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20779685444331/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (126090871057/1000000000000:ℝ) (20779685444331/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4602559/125000000000:ℝ) ≤ ((126090871057/1000000000000:ℝ)/(20779685444331/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_38 (x : ℝ) (h₁ : (4301/4096:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1572330307/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (987664334499/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1572330307/10000000000:ℝ) + taylorErr ≤ (987664334499/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (156585970373/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (156585970373/1000000000000:ℝ) ≤ taylorSin (1572330307/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-987664334499/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-156585970373/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (824706421087/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by nlinarith
  have hp1 : (5459551827881/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-85488922077/100000000000:ℝ) := by nlinarith
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_39 (x : ℝ) (h₁ : (8605/8192:ℝ) ≤ x) (h₂ : x ≤ (269/256:ℝ)) : (329694637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1583835163/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (246870882747/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1583835163/10000000000:ℝ) + taylorErr ≤ (246870882747/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (31544432017/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (31544432017/200000000000:ℝ) ≤ taylorSin (1583835163/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-246870882747/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-31544432017/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1649988084969/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (330112665553/100000000000:ℝ) := by nlinarith
  have hp1 : (5461455879901/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-433949619737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-430696309293/500000000000:ℝ) := by nlinarith
  have hN : (29850544103/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10397437195851/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29850544103/250000000000:ℝ) (10397437195851/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329694637/10000000000000:ℝ) ≤ ((29850544103/250000000000:ℝ)/(10397437195851/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_40 (x : ℝ) (h₁ : (269/256:ℝ) ≤ x) (h₂ : x ≤ (8611/8192:ℝ)) : (146669617/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (401711219/2500000000:ℝ) := by nlinarith
  have hc1 : (246779499629/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246779499629/250000000000:ℝ) ≤ taylorCos (401711219/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31998783267/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (401711219/2500000000:ℝ) + taylorErr ≤ (31998783267/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246779499629/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31998783267/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3301126655529/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3302277141121/1000000000000:ℝ) := by nlinarith
  have hp1 : (2731679965961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (683158007157/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-437204500163/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-867899202573/1000000000000:ℝ) := by nlinarith
  have hN : (11270899819/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20810068633541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11270899819/100000000000:ℝ) (20810068633541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (146669617/5000000000000:ℝ) ≤ ((11270899819/100000000000:ℝ)/(20810068633541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_41 (x : ℝ) (h₁ : (269/256:ℝ) ≤ x) (h₂ : x ≤ (4307/4096:ℝ)) : (259133459/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (404587433/2500000000:ℝ) := by nlinarith
  have hc1 : (986933274579/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986933274579/1000000000000:ℝ) ≤ taylorCos (404587433/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986933274579/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32225895049/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3301126655529/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (412928453339/125000000000:ℝ) := by nlinarith
  have hp1 : (2731679965961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5467168109303/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-880921928529/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-867899202573/1000000000000:ℝ) := by nlinarith
  have hN : (2120226921/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20825268169849/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2120226921/20000000000:ℝ) (20825268169849/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (259133459/10000000000000:ℝ) ≤ ((2120226921/20000000000:ℝ)/(20825268169849/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_42 (x : ℝ) (h₁ : (269/256:ℝ) ≤ x) (h₂ : x ≤ (2155/2048:ℝ)) : (98575293/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (410339861/2500000000:ℝ) := by nlinarith
  have hc1 : (986559907987/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986559907987/1000000000000:ℝ) ≤ taylorCos (410339861/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8169997587/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (410339861/2500000000:ℝ) + taylorErr ≤ (8169997587/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986559907987/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8169997587/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3301126655529/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1652864298947/500000000000:ℝ) := by nlinarith
  have hp1 : (2731679965961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1367744053349/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-22348931231/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-867899202573/1000000000000:ℝ) := by nlinarith
  have hN : (92602658747/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20855683125869/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (92602658747/1000000000000:ℝ) (20855683125869/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98575293/5000000000000:ℝ) ≤ ((92602658747/1000000000000:ℝ)/(20855683125869/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_43 (x : ℝ) (h₁ : (269/256:ℝ) ≤ x) (h₂ : x ≤ (1079/1024:ℝ)) : (98758117/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3301126655529/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1655165270129/500000000000:ℝ) := by nlinarith
  have hp1 : (2731679965961/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2739296210791/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-115008185339/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-867899202573/1000000000000:ℝ) := by nlinarith
  have hN : (16433006047/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2091657657153/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (16433006047/250000000000:ℝ) (2091657657153/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98758117/10000000000000:ℝ) ≤ ((16433006047/250000000000:ℝ)/(2091657657153/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_44 (x : ℝ) (_h₁ : (269/256:ℝ) ≤ x) (_h₂ : x ≤ (17/16:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_45 (x : ℝ) (h₁ : (8611/8192:ℝ) ≤ x) (h₂ : x ≤ (4307/4096:ℝ)) : (259133459/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (12854759/80000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (404587433/2500000000:ℝ) := by nlinarith
  have hc1 : (986933274579/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986933274579/1000000000000:ℝ) ≤ taylorCos (404587433/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61694875191/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (12854759/80000000:ℝ) + taylorErr ≤ (61694875191/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4999809741/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4999809741/31250000000:ℝ) ≤ taylorSin (12854759/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-61694875191/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986933274579/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32225895049/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4999809741/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5159808033/1562500000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (412928453339/125000000000:ℝ) := by nlinarith
  have hp1 : (5465263983943/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5467168109303/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-880921928529/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-874408963329/1000000000000:ℝ) := by nlinarith
  have hN : (2120226921/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20825268169849/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2120226921/20000000000:ℝ) (20825268169849/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (259133459/10000000000000:ℝ) ≤ ((2120226921/20000000000:ℝ)/(20825268169849/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_46 (x : ℝ) (h₁ : (4307/4096:ℝ) ≤ x) (h₂ : x ≤ (8617/8192:ℝ)) : (11353613/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1618349731/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (407463647/2500000000:ℝ) := by nlinarith
  have hc1 : (986747244321/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986747244321/1000000000000:ℝ) ≤ taylorCos (407463647/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986933279119/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1618349731/10000000000:ℝ) + taylorErr ≤ (986933279119/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80564735311/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80564735311/500000000000:ℝ) ≤ taylorSin (1618349731/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (162264820881/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (407463647/2500000000:ℝ) + taylorErr ≤ (162264820881/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-986747244321/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-162264820881/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-80564735311/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3303427626711/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3304578112303/1000000000000:ℝ) := by nlinarith
  have hp1 : (1366792008991/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5469072161349/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-887438014647/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-220230472859/250000000000:ℝ) := by nlinarith
  have hN : (49654614837/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (33344756801/1600000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (49654614837/500000000000:ℝ) (33344756801/1600000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11353613/500000000000:ℝ) ≤ ((49654614837/500000000000:ℝ)/(33344756801/1600000000:ℝ))^2 := by norm_num
  linarith

theorem wc_47 (x : ℝ) (h₁ : (4307/4096:ℝ) ≤ x) (h₂ : x ≤ (2155/2048:ℝ)) : (98575293/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1618349731/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (410339861/2500000000:ℝ) := by nlinarith
  have hc1 : (986559907987/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986559907987/1000000000000:ℝ) ≤ taylorCos (410339861/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986933279119/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1618349731/10000000000:ℝ) + taylorErr ≤ (986933279119/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80564735311/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80564735311/500000000000:ℝ) ≤ taylorSin (1618349731/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8169997587/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (410339861/2500000000:ℝ) + taylorErr ≤ (8169997587/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-986559907987/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8169997587/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-80564735311/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3303427626711/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1652864298947/500000000000:ℝ) := by nlinarith
  have hp1 : (1366792008991/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1367744053349/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-22348931231/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-220230472859/250000000000:ℝ) := by nlinarith
  have hN : (92602658747/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20855683125869/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (92602658747/1000000000000:ℝ) (20855683125869/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98575293/5000000000000:ℝ) ≤ ((92602658747/1000000000000:ℝ)/(20855683125869/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_48 (x : ℝ) (h₁ : (8617/8192:ℝ) ≤ x) (h₂ : x ≤ (2155/2048:ℝ)) : (98575293/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1629854587/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (410339861/2500000000:ℝ) := by nlinarith
  have hc1 : (986559907987/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986559907987/1000000000000:ℝ) ≤ taylorCos (410339861/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986747248861/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1629854587/10000000000:ℝ) + taylorErr ≤ (986747248861/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (81132408129/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (81132408129/500000000000:ℝ) ≤ taylorSin (1629854587/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8169997587/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (410339861/2500000000:ℝ) + taylorErr ≤ (8169997587/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-986747248861/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986559907987/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8169997587/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-81132408129/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1652289056151/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1652864298947/500000000000:ℝ) := by nlinarith
  have hp1 : (1093814417597/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1367744053349/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-22348931231/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-443718988729/500000000000:ℝ) := by nlinarith
  have hN : (92602658747/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20855683125869/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (92602658747/1000000000000:ℝ) (20855683125869/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98575293/5000000000000:ℝ) ≤ ((92602658747/1000000000000:ℝ)/(20855683125869/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_49 (x : ℝ) (h₁ : (2155/2048:ℝ) ≤ x) (h₂ : x ≤ (8623/8192:ℝ)) : (169363387/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1641359443/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1652864299/10000000000:ℝ) := by nlinarith
  have hc1 : (493185632921/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493185632921/500000000000:ℝ) ≤ taylorCos (1652864299/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61659994533/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1641359443/10000000000:ℝ) + taylorErr ≤ (61659994533/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (163399947117/1000000000000:ℝ) ≤ taylorSin (1641359443/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (82267433111/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1652864299/10000000000:ℝ) + taylorErr ≤ (82267433111/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61659994533/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493185632921/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-82267433111/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-163399947117/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3305728597893/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (661375816697/200000000000:ℝ) := by nlinarith
  have hp1 : (2735488070003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2736440132721/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-225119905581/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-178791442391/200000000000:ℝ) := by nlinarith
  have hN : (42945821759/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10435449272791/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (42945821759/500000000000:ℝ) (10435449272791/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (169363387/10000000000000:ℝ) ≤ ((42945821759/500000000000:ℝ)/(10435449272791/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_50 (x : ℝ) (h₁ : (2155/2048:ℝ) ≤ x) (h₂ : x ≤ (4313/4096:ℝ)) : (143705609/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1641359443/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (332873831/2000000000:ℝ) := by nlinarith
  have hc1 : (986181318103/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986181318103/1000000000000:ℝ) ≤ taylorCos (332873831/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61659994533/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1641359443/10000000000:ℝ) + taylorErr ≤ (61659994533/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (163399947117/1000000000000:ℝ) ≤ taylorSin (1641359443/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (165669563021/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (332873831/2000000000:ℝ) + taylorErr ≤ (165669563021/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61659994533/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986181318103/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-165669563021/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-163399947117/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3305728597893/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (827007392269/250000000000:ℝ) := by nlinarith
  have hp1 : (2735488070003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5474784317489/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-907005125513/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-178791442391/200000000000:ℝ) := by nlinarith
  have hN : (7917619259/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20886119259763/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7917619259/100000000000:ℝ) (20886119259763/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (143705609/10000000000000:ℝ) ≤ ((7917619259/100000000000:ℝ)/(20886119259763/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_51 (x : ℝ) (h₁ : (2155/2048:ℝ) ≤ x) (h₂ : x ≤ (1079/1024:ℝ)) : (98758117/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1641359443/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61659994533/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1641359443/10000000000:ℝ) + taylorErr ≤ (61659994533/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (163399947117/1000000000000:ℝ) ≤ taylorSin (1641359443/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61659994533/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-163399947117/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3305728597893/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1655165270129/500000000000:ℝ) := by nlinarith
  have hp1 : (2735488070003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2739296210791/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-115008185339/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-178791442391/200000000000:ℝ) := by nlinarith
  have hN : (16433006047/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2091657657153/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (16433006047/250000000000:ℝ) (2091657657153/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98758117/10000000000000:ℝ) ≤ ((16433006047/250000000000:ℝ)/(2091657657153/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_52 (x : ℝ) (h₁ : (8623/8192:ℝ) ≤ x) (h₂ : x ≤ (4313/4096:ℝ)) : (143705609/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (826432149/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (332873831/2000000000:ℝ) := by nlinarith
  have hc1 : (986181318103/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986181318103/1000000000000:ℝ) ≤ taylorCos (332873831/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986371270383/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (826432149/5000000000:ℝ) + taylorErr ≤ (986371270383/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164534861599/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164534861599/1000000000000:ℝ) ≤ taylorSin (826432149/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (165669563021/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (332873831/2000000000:ℝ) + taylorErr ≤ (165669563021/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-986371270383/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986181318103/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-165669563021/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164534861599/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (826719770871/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (827007392269/250000000000:ℝ) := by nlinarith
  have hp1 : (5472880192027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5474784317489/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-907005125513/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-900479584943/1000000000000:ℝ) := by nlinarith
  have hN : (7917619259/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20886119259763/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7917619259/100000000000:ℝ) (20886119259763/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (143705609/10000000000000:ℝ) ≤ ((7917619259/100000000000:ℝ)/(20886119259763/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_53 (x : ℝ) (h₁ : (4313/4096:ℝ) ≤ x) (h₂ : x ≤ (8629/8192:ℝ)) : (60086101/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (832184577/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1675874011/10000000000:ℝ) := by nlinarith
  have hc1 : (492995032519/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492995032519/500000000000:ℝ) ≤ taylorCos (1675874011/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (246545330661/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (832184577/5000000000:ℝ) + taylorErr ≤ (246545330661/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (82834779199/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (82834779199/500000000000:ℝ) ≤ taylorSin (832184577/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-246545330661/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492995032519/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-166804040537/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-82834779199/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (132321182763/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3309180054667/1000000000000:ℝ) := by nlinarith
  have hp1 : (342174015253/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1095337673907/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-913533748801/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-181401017607/200000000000:ℝ) := by nlinarith
  have hN : (72456316237/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5225336317103/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (72456316237/1000000000000:ℝ) (5225336317103/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (60086101/5000000000000:ℝ) ≤ ((72456316237/1000000000000:ℝ)/(5225336317103/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_54 (x : ℝ) (h₁ : (4313/4096:ℝ) ≤ x) (h₂ : x ≤ (1079/1024:ℝ)) : (98758117/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (832184577/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (246545330661/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (832184577/5000000000:ℝ) + taylorErr ≤ (246545330661/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (82834779199/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (82834779199/500000000000:ℝ) ≤ taylorSin (832184577/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-246545330661/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-82834779199/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (132321182763/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1655165270129/500000000000:ℝ) := by nlinarith
  have hp1 : (342174015253/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2739296210791/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-115008185339/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-181401017607/200000000000:ℝ) := by nlinarith
  have hN : (16433006047/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2091657657153/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (16433006047/250000000000:ℝ) (2091657657153/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98758117/10000000000000:ℝ) ≤ ((16433006047/250000000000:ℝ)/(2091657657153/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_55 (x : ℝ) (h₁ : (8629/8192:ℝ) ≤ x) (h₂ : x ≤ (1079/1024:ℝ)) : (98758117/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (167587401/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (985990069579/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (167587401/1000000000:ℝ) + taylorErr ≤ (985990069579/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (33360807183/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (33360807183/200000000000:ℝ) ≤ taylorSin (167587401/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-33360807183/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1654590027333/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1655165270129/500000000000:ℝ) := by nlinarith
  have hp1 : (5476688296069/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2739296210791/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-115008185339/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7136982119/7812500000:ℝ) := by nlinarith
  have hN : (16433006047/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2091657657153/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (16433006047/250000000000:ℝ) (2091657657153/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (98758117/10000000000000:ℝ) ≤ ((16433006047/250000000000:ℝ)/(2091657657153/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_56 (x : ℝ) (h₁ : (1079/1024:ℝ) ≤ x) (h₂ : x ≤ (4319/4096:ℝ)) : (62267711/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1710388579/10000000000:ℝ) := by nlinarith
  have hc1 : (39416339057/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (39416339057/40000000000:ℝ) ≤ taylorCos (1710388579/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (170206142373/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1710388579/10000000000:ℝ) + taylorErr ≤ (170206142373/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-39416339057/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-170206142373/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3310330540257/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (41407893893/12500000000:ℝ) := by nlinarith
  have hp1 : (547859234809/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (219296021027/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-933138244419/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-920065445041/1000000000000:ℝ) := by nlinarith
  have hN : (26135116003/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20947055061171/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (26135116003/500000000000:ℝ) (20947055061171/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (62267711/10000000000000:ℝ) ≤ ((26135116003/500000000000:ℝ)/(20947055061171/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_57 (x : ℝ) (h₁ : (1079/1024:ℝ) ≤ x) (h₂ : x ≤ (2161/2048:ℝ)) : (6838799/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1733398291/10000000000:ℝ) := by nlinarith
  have hc1 : (492507114369/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492507114369/500000000000:ℝ) ≤ taylorCos (1733398291/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492507114369/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-172473086327/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3310330540257/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3314932482621/1000000000000:ℝ) := by nlinarith
  have hp1 : (547859234809/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5486208629767/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-94622333461/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-920065445041/1000000000000:ℝ) := by nlinarith
  have hN : (2424430883/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (655548585271/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2424430883/62500000000:ℝ) (655548585271/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6838799/2000000000000:ℝ) ≤ ((2424430883/62500000000:ℝ)/(655548585271/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_58 (x : ℝ) (h₁ : (1079/1024:ℝ) ≤ x) (h₂ : x ≤ (541/512:ℝ)) : (1567539/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (889708857/5000000000:ℝ) := by nlinarith
  have hc1 : (246052522531/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246052522531/250000000000:ℝ) ≤ taylorCos (889708857/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (177004222679/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/5000000000:ℝ) + taylorErr ≤ (177004222679/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246052522531/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-177004222679/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3310330540257/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (663906884997/200000000000:ℝ) := by nlinarith
  have hp1 : (547859234809/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5493824837953/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-972430194977/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-920065445041/1000000000000:ℝ) := by nlinarith
  have hN : (11779895147/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21038617597321/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11779895147/1000000000000:ℝ) (21038617597321/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1567539/5000000000000:ℝ) ≤ ((11779895147/1000000000000:ℝ)/(21038617597321/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_59 (x : ℝ) (h₁ : (4319/4096:ℝ) ≤ x) (h₂ : x ≤ (2161/2048:ℝ)) : (6838799/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (855194289/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1733398291/10000000000:ℝ) := by nlinarith
  have hc1 : (492507114369/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492507114369/500000000000:ℝ) ≤ taylorCos (1733398291/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (492704240483/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (855194289/5000000000:ℝ) + taylorErr ≤ (492704240483/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (680824551/4000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (680824551/4000000000:ℝ) ≤ taylorSin (855194289/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-492704240483/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492507114369/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-172473086327/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-680824551/4000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3312631511439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3314932482621/1000000000000:ℝ) := by nlinarith
  have hp1 : (1370600113033/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5486208629767/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-94622333461/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-233284551639/250000000000:ℝ) := by nlinarith
  have hN : (2424430883/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (655548585271/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2424430883/62500000000:ℝ) (655548585271/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6838799/2000000000000:ℝ) ≤ ((2424430883/62500000000:ℝ)/(655548585271/31250000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.ThreePoint
