import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


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

theorem wc_1 (x : ℝ) (h₁ : (3/4:ℝ) ≤ x) (h₂ : x ≤ (7/8:ℝ)) : (242869129569/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * ((1:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((1:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((1:ℝ) - x)) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-923879534811/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (147262155637/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (687223392973/250000000000:ℝ) := by nlinarith
  have hp1 : (389949853877/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4549415022927/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1492273476143/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1608461111707/500000000000:ℝ) := by nlinarith
  have hN : (2199380254951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (14112831739179/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2199380254951/1000000000000:ℝ) (14112831739179/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (242869129569/10000000000000:ℝ) ≤ ((2199380254951/1000000000000:ℝ)/(14112831739179/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_2 (x : ℝ) (h₁ : (7/8:ℝ) ≤ x) (h₂ : x ≤ (15/16:ℝ)) : (15345235463/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * ((1:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((1:ℝ) - x) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((1:ℝ) - x)) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((1:ℝ) - x)) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hcxl : (-39231411307/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-923879530249/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2748893571891/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2945243112741/1000000000000:ℝ) := by nlinarith
  have hp1 : (4549414961899/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4874373238849/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (13867919053/15625000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (932670946351/500000000000:ℝ) := by nlinarith
  have hN : (1811426349641/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16348913986297/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1811426349641/1000000000000:ℝ) (16348913986297/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (15345235463/1250000000000:ℝ) ≤ ((1811426349641/1000000000000:ℝ)/(16348913986297/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_3 (x : ℝ) (h₁ : (15/16:ℝ) ≤ x) (h₂ : x ≤ (31/32:ℝ)) : (8658679537/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * ((1:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((1:ℝ) - x) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((1:ℝ) - x)) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((1:ℝ) - x)) ≤ (24386290541/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1963495409/10000000000:ℝ) + taylorErr ≤ (24386290541/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hcxl : (-995184728937/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980785278131/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24386290541/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (147262155637/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1521708941583/500000000000:ℝ) := by nlinarith
  have hp1 : (2437186586731/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5036852346811/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (59721513527/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (245660289483/250000000000:ℝ) := by nlinarith
  have hN : (1458557386347/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (350495696463/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1458557386347/1000000000000:ℝ) (350495696463/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (8658679537/1250000000000:ℝ) ≤ ((1458557386347/1000000000000:ℝ)/(350495696463/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_4 (x : ℝ) (h₁ : (31/32:ℝ) ≤ x) (h₂ : x ≤ (63/64:ℝ)) : (46969344551/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2500000000:ℝ) ≤ Real.pi * ((1:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((1:ℝ) - x) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((1:ℝ) - x)) ≤ (249698864617/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2500000000:ℝ) + taylorErr ≤ (249698864617/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (49067672053/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (49067672053/1000000000000:ℝ) ≤ taylorSin (122718463/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((1:ℝ) - x)) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h, cos_flip (1:ℝ) x, sin_flip (1:ℝ) x]; ring
  have hcxl : (-249698864617/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-995184724403/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (49067672053/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (98017142667/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (608683576633/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1546252634189/500000000000:ℝ) := by nlinarith
  have hp1 : (1007370455849/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (639761487599/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (247146615817/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (501660744023/1000000000000:ℝ) := by nlinarith
  have hN : (62116567011/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4531794417473/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (62116567011/50000000000:ℝ) (4531794417473/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (46969344551/10000000000000:ℝ) ≤ ((62116567011/50000000000:ℝ)/(4531794417473/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_5 (x : ℝ) (h₁ : (63/64:ℝ) ≤ x) (h₂ : x ≤ (1:ℝ)) : (14204325221/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((1:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((1:ℝ) - x) ≤ (490873853/10000000000:ℝ) := by nlinarith
  have hc1 : (998795453939/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((1:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998795453939/1000000000000:ℝ) ≤ taylorCos (490873853/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((1:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((1:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((1:ℝ) - x)) ≤ (49067676677/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (490873853/10000000000:ℝ) + taylorErr ≤ (49067676677/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-998795453939/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (49067676677/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3092505268377/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/100000000000:ℝ) := by nlinarith
  have hp1 : (1023618366427/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1299832863693/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11761/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (6377977869/25000000000:ℝ) := by nlinarith
  have hN : (499397721089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9369604401091/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499397721089/500000000000:ℝ) (9369604401091/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14204325221/5000000000000:ℝ) ≤ ((499397721089/500000000000:ℝ)/(9369604401091/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_6 (x : ℝ) (h₁ : (1:ℝ) ≤ x) (h₂ : x ≤ (257/256:ℝ)) : (12267823741/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (479369/39062500:ℝ) := by nlinarith
  have hc1 : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124990587447/125000000000:ℝ) ≤ taylorCos (479369/39062500:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (2454308129/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/39062500:ℝ) + taylorErr ≤ (2454308129/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-124990587447/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2454308129/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3141592653589/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/1000000000000:ℝ) := by nlinarith
  have hp1 : (2599665692513/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-64053040897/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11807/1000000000000:ℝ) := by nlinarith
  have hN : (935871658679/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (18893722567371/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (935871658679/1000000000000:ℝ) (18893722567371/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (12267823741/5000000000000:ℝ) ≤ ((935871658679/1000000000000:ℝ)/(18893722567371/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_7 (x : ℝ) (h₁ : (1:ℝ) ≤ x) (h₂ : x ≤ (131/128:ℝ)) : (2370342229/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (736310779/10000000000:ℝ) := by nlinarith
  have hc1 : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997290454411/1000000000000:ℝ) ≤ taylorCos (736310779/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (73564565943/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (736310779/10000000000:ℝ) + taylorErr ≤ (73564565943/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-997290454411/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73564565943/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3141592653589/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3215223731409/1000000000000:ℝ) := by nlinarith
  have hp1 : (2599665692513/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (332574424109/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-195725545227/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (12037/1000000000000:ℝ) := by nlinarith
  have hN : (605839363957/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1229707955377/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (605839363957/1000000000000:ℝ) (1229707955377/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2370342229/2500000000000:ℝ) ≤ ((605839363957/1000000000000:ℝ)/(1229707955377/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_8 (x : ℝ) (h₁ : (257/256:ℝ) ≤ x) (h₂ : x ≤ (519/512:ℝ)) : (4015256583/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (429514621/10000000000:ℝ) := by nlinarith
  have hc1 : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999077725489/1000000000000:ℝ) ≤ taylorCos (429514621/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (10734564809/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/10000000000:ℝ) + taylorErr ≤ (10734564809/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-999924704101/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-999077725489/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-10734564809/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (788466124973/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3184544115651/1000000000000:ℝ) := by nlinarith
  have hp1 : (5219641273249/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2635208032253/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11315124563/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-8006626987/125000000000:ℝ) := by nlinarith
  have hN : (772775234229/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3856528489811/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (772775234229/1000000000000:ℝ) (3856528489811/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4015256583/2500000000000:ℝ) ≤ ((772775234229/1000000000000:ℝ)/(3856528489811/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_9 (x : ℝ) (h₁ : (257/256:ℝ) ≤ x) (h₂ : x ≤ (131/128:ℝ)) : (2370342229/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (736310779/10000000000:ℝ) := by nlinarith
  have hc1 : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997290454411/1000000000000:ℝ) ≤ taylorCos (736310779/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (73564565943/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (736310779/10000000000:ℝ) + taylorErr ≤ (73564565943/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-999924704101/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-997290454411/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73564565943/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (788466124973/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3215223731409/1000000000000:ℝ) := by nlinarith
  have hp1 : (5219641273249/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (332574424109/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-195725545227/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-8006626987/125000000000:ℝ) := by nlinarith
  have hN : (605839363957/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1229707955377/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (605839363957/1000000000000:ℝ) (1229707955377/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2370342229/2500000000000:ℝ) ≤ ((605839363957/1000000000000:ℝ)/(1229707955377/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_10 (x : ℝ) (h₁ : (519/512:ℝ) ≤ x) (h₂ : x ≤ (131/128:ℝ)) : (2370342229/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (736310779/10000000000:ℝ) := by nlinarith
  have hc1 : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997290454411/1000000000000:ℝ) ≤ taylorCos (736310779/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (999077730017/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/500000000:ℝ) + taylorErr ≤ (999077730017/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (10734563653/250000000000:ℝ) ≤ taylorSin (21475731/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (73564565943/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (736310779/10000000000:ℝ) + taylorErr ≤ (73564565943/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-999077730017/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-997290454411/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73564565943/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-10734563653/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (63690882313/20000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3215223731409/1000000000000:ℝ) := by nlinarith
  have hp1 : (2635207996903/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (332574424109/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-195725545227/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-226302463853/1000000000000:ℝ) := by nlinarith
  have hN : (605839363957/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1229707955377/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (605839363957/1000000000000:ℝ) (1229707955377/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2370342229/2500000000000:ℝ) ≤ ((605839363957/1000000000000:ℝ)/(1229707955377/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_11 (x : ℝ) (h₁ : (131/128:ℝ) ≤ x) (h₂ : x ≤ (1053/1024:ℝ)) : (3436255003/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (889708857/10000000000:ℝ) := by nlinarith
  have hc1 : (996044698639/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996044698639/1000000000000:ℝ) ≤ taylorCos (889708857/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (88853554847/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/10000000000:ℝ) + taylorErr ≤ (88853554847/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-498645229471/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996044698639/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-88853554847/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-73564561319/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (403820442411/125000000000:ℝ) := by nlinarith
  have hp1 : (5321190714363/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5346578146363/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-118765618643/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-97862765149/250000000000:ℝ) := by nlinarith
  have hN : (520982224067/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3974616312551/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (520982224067/1000000000000:ℝ) (3974616312551/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3436255003/5000000000000:ℝ) ≤ ((520982224067/1000000000000:ℝ)/(3974616312551/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_12 (x : ℝ) (h₁ : (131/128:ℝ) ≤ x) (h₂ : x ≤ (529/512:ℝ)) : (1175437333/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (130388367/1250000000:ℝ) := by nlinarith
  have hc1 : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99456456847/100000000000:ℝ) ≤ taylorCos (130388367/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-498645229471/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99456456847/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52060818079/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-73564561319/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3245903347167/1000000000000:ℝ) := by nlinarith
  have hp1 : (5321190714363/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2685982753491/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-139834459493/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-97862765149/250000000000:ℝ) := by nlinarith
  have hN : (217613365249/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (200717770783/10000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (217613365249/500000000000:ℝ) (200717770783/10000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1175437333/2500000000000:ℝ) ≤ ((217613365249/500000000000:ℝ)/(200717770783/10000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_13 (x : ℝ) (h₁ : (131/128:ℝ) ≤ x) (h₂ : x ≤ (267/256:ℝ)) : (1626727581/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-498645229471/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990902633157/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-73564561319/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/250000000000:ℝ) := by nlinarith
  have hp1 : (5321190714363/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-182449058647/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-97862765149/250000000000:ℝ) := by nlinarith
  have hN : (261106398569/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2558998978231/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (261106398569/1000000000000:ℝ) (2558998978231/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1626727581/10000000000000:ℝ) ≤ ((261106398569/1000000000000:ℝ)/(2558998978231/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_14 (x : ℝ) (h₁ : (1053/1024:ℝ) ≤ x) (h₂ : x ≤ (2111/2048:ℝ)) : (2866556697/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/1250000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (966407897/10000000000:ℝ) := by nlinarith
  have hc1 : (62208369367/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62208369367/62500000000:ℝ) ≤ taylorCos (966407897/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (249011175793/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/1250000000:ℝ) + taylorErr ≤ (249011175793/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (88853550223/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (88853550223/1000000000000:ℝ) ≤ taylorSin (111213607/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (1206130421/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (966407897/10000000000:ℝ) + taylorErr ≤ (1206130421/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-249011175793/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-62208369367/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1206130421/12500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88853550223/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3230563539287/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3238233443227/1000000000000:ℝ) := by nlinarith
  have hp1 : (2673289037321/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (334954489167/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-103423692553/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-118765610869/250000000000:ℝ) := by nlinarith
  have hN : (478215447107/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4993077916417/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (478215447107/1000000000000:ℝ) (4993077916417/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2866556697/5000000000000:ℝ) ≤ ((478215447107/1000000000000:ℝ)/(4993077916417/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_15 (x : ℝ) (h₁ : (1053/1024:ℝ) ≤ x) (h₂ : x ≤ (529/512:ℝ)) : (1175437333/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/1250000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (130388367/1250000000:ℝ) := by nlinarith
  have hc1 : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99456456847/100000000000:ℝ) ≤ taylorCos (130388367/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (249011175793/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/1250000000:ℝ) + taylorErr ≤ (249011175793/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (88853550223/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (88853550223/1000000000000:ℝ) ≤ taylorSin (111213607/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-249011175793/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99456456847/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52060818079/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88853550223/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3230563539287/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3245903347167/1000000000000:ℝ) := by nlinarith
  have hp1 : (2673289037321/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2685982753491/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-139834459493/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-118765610869/250000000000:ℝ) := by nlinarith
  have hN : (217613365249/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (200717770783/10000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (217613365249/500000000000:ℝ) (200717770783/10000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1175437333/2500000000000:ℝ) ≤ ((217613365249/500000000000:ℝ)/(200717770783/10000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_16 (x : ℝ) (h₁ : (2111/2048:ℝ) ≤ x) (h₂ : x ≤ (529/512:ℝ)) : (1175437333/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (120800987/1250000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (130388367/1250000000:ℝ) := by nlinarith
  have hc1 : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99456456847/100000000000:ℝ) ≤ taylorCos (130388367/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (497666957203/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (120800987/1250000000:ℝ) + taylorErr ≤ (497666957203/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (753831477/7812500000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (753831477/7812500000:ℝ) ≤ taylorSin (120800987/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-497666957203/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99456456847/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52060818079/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-753831477/7812500000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1619116721613/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3245903347167/1000000000000:ℝ) := by nlinarith
  have hp1 : (5359271754781/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2685982753491/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-139834459493/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-258559215523/500000000000:ℝ) := by nlinarith
  have hN : (217613365249/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (200717770783/10000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (217613365249/500000000000:ℝ) (200717770783/10000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1175437333/2500000000000:ℝ) ≤ ((217613365249/500000000000:ℝ)/(200717770783/10000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_17 (x : ℝ) (h₁ : (529/512:ℝ) ≤ x) (h₂ : x ≤ (2121/2048:ℝ)) : (1888462017/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (208621387/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (139975747/1250000000:ℝ) := by nlinarith
  have hc1 : (993736719669/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (993736719669/1000000000000:ℝ) ≤ taylorCos (139975747/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (248641143251/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (208621387/2000000000:ℝ) + taylorErr ≤ (248641143251/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (52060815767/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (52060815767/500000000000:ℝ) ≤ taylorSin (208621387/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (111746713557/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (139975747/1250000000:ℝ) + taylorErr ≤ (111746713557/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-993736719669/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-111746713557/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-52060815767/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1626786625553/500000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5384659187291/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-120343593561/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-139834451407/250000000000:ℝ) := by nlinarith
  have hN : (49002343983/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (32274364481/1600000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (49002343983/125000000000:ℝ) (32274364481/1600000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1888462017/5000000000000:ℝ) ≤ ((49002343983/125000000000:ℝ)/(32274364481/1600000000:ℝ))^2 := by norm_num
  linarith

theorem wc_18 (x : ℝ) (h₁ : (529/512:ℝ) ≤ x) (h₂ : x ≤ (1063/1024:ℝ)) : (2957142633/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (208621387/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (239301003/2000000000:ℝ) := by nlinarith
  have hc1 : (31026575381/31250000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (31026575381/31250000000:ℝ) ≤ taylorCos (239301003/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (248641143251/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (208621387/2000000000:ℝ) + taylorErr ≤ (248641143251/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (52060815767/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (52060815767/500000000000:ℝ) ≤ taylorSin (208621387/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (59682608559/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (239301003/2000000000:ℝ) + taylorErr ≤ (59682608559/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-31026575381/31250000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59682608559/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-52060815767/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (652248631009/200000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13493382169/2500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-80532024613/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-139834451407/250000000000:ℝ) := by nlinarith
  have hN : (43574276911/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1266963364541/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (43574276911/125000000000:ℝ) (1266963364541/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2957142633/10000000000000:ℝ) ≤ ((43574276911/125000000000:ℝ)/(1266963364541/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_19 (x : ℝ) (h₁ : (529/512:ℝ) ≤ x) (h₂ : x ≤ (267/256:ℝ)) : (1626727581/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (208621387/2000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (248641143251/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (208621387/2000000000:ℝ) + taylorErr ≤ (248641143251/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (52060815767/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (52060815767/500000000000:ℝ) ≤ taylorSin (208621387/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-990902633157/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-52060815767/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/250000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-182449058647/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-139834451407/250000000000:ℝ) := by nlinarith
  have hN : (261106398569/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2558998978231/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (261106398569/1000000000000:ℝ) (2558998978231/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1626727581/10000000000000:ℝ) ≤ ((261106398569/1000000000000:ℝ)/(2558998978231/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_20 (x : ℝ) (h₁ : (2121/2048:ℝ) ≤ x) (h₂ : x ≤ (4247/4096:ℝ)) : (1676998161/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (44792239/400000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (231631099/2000000000:ℝ) := by nlinarith
  have hc1 : (496650435047/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (496650435047/500000000000:ℝ) ≤ taylorCos (231631099/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198747344841/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (44792239/400000000:ℝ) + taylorErr ≤ (198747344841/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (111746708933/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (111746708933/1000000000000:ℝ) ≤ taylorSin (44792239/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (4622272601/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (231631099/2000000000:ℝ) + taylorErr ≤ (4622272601/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198747344841/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-496650435047/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4622272601/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-111746708933/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (650714650221/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (814352050769/250000000000:ℝ) := by nlinarith
  have hp1 : (5384659115059/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2695503013723/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-622967486313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601717934833/1000000000000:ℝ) := by nlinarith
  have hN : (370333383781/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10110708201467/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (370333383781/1000000000000:ℝ) (10110708201467/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1676998161/5000000000000:ℝ) ≤ ((370333383781/1000000000000:ℝ)/(10110708201467/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_21 (x : ℝ) (h₁ : (2121/2048:ℝ) ≤ x) (h₂ : x ≤ (1063/1024:ℝ)) : (2957142633/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (44792239/400000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (239301003/2000000000:ℝ) := by nlinarith
  have hc1 : (31026575381/31250000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (31026575381/31250000000:ℝ) ≤ taylorCos (239301003/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198747344841/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (44792239/400000000:ℝ) + taylorErr ≤ (198747344841/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (111746708933/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (111746708933/1000000000000:ℝ) ≤ taylorSin (44792239/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (59682608559/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (239301003/2000000000:ℝ) + taylorErr ≤ (59682608559/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198747344841/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-31026575381/31250000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59682608559/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-111746708933/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (650714650221/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (652248631009/200000000000:ℝ) := by nlinarith
  have hp1 : (5384659115059/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13493382169/2500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-80532024613/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601717934833/1000000000000:ℝ) := by nlinarith
  have hN : (43574276911/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1266963364541/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (43574276911/125000000000:ℝ) (1266963364541/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2957142633/10000000000000:ℝ) ≤ ((43574276911/125000000000:ℝ)/(1266963364541/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_22 (x : ℝ) (h₁ : (4247/4096:ℝ) ≤ x) (h₂ : x ≤ (1063/1024:ℝ)) : (2957142633/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (579077747/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (239301003/2000000000:ℝ) := by nlinarith
  have hc1 : (31026575381/31250000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (31026575381/31250000000:ℝ) ≤ taylorCos (239301003/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (99330087463/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (579077747/5000000000:ℝ) + taylorErr ≤ (99330087463/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57778405201/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57778405201/500000000000:ℝ) ≤ taylorSin (579077747/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (59682608559/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (239301003/2000000000:ℝ) + taylorErr ≤ (59682608559/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-99330087463/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-31026575381/31250000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59682608559/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-57778405201/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (130296328123/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (652248631009/200000000000:ℝ) := by nlinarith
  have hp1 : (5391005955129/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13493382169/2500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-80532024613/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-77870931629/125000000000:ℝ) := by nlinarith
  have hN : (43574276911/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1266963364541/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (43574276911/125000000000:ℝ) (1266963364541/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2957142633/10000000000000:ℝ) ≤ ((43574276911/125000000000:ℝ)/(1266963364541/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_23 (x : ℝ) (h₁ : (1063/1024:ℝ) ≤ x) (h₂ : x ≤ (4257/4096:ℝ)) : (2586175977/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (598252507/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (246970907/2000000000:ℝ) := by nlinarith
  have hc1 : (992385352599/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (992385352599/1000000000000:ℝ) ≤ taylorCos (246970907/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (992850416729/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (598252507/5000000000:ℝ) + taylorErr ≤ (992850416729/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59682606247/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59682606247/500000000000:ℝ) ≤ taylorSin (598252507/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (4926874549/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (246970907/2000000000:ℝ) + taylorErr ≤ (4926874549/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-992850416729/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-992385352599/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4926874549/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-59682606247/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (815310788761/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (653015621403/200000000000:ℝ) := by nlinarith
  have hp1 : (2698676397599/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1080739941551/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-133116752803/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-644256163303/1000000000000:ℝ) := by nlinarith
  have hN : (40850198573/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10160735044909/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (40850198573/125000000000:ℝ) (10160735044909/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2586175977/10000000000000:ℝ) ≤ ((40850198573/125000000000:ℝ)/(10160735044909/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_24 (x : ℝ) (h₁ : (1063/1024:ℝ) ≤ x) (h₂ : x ≤ (2131/2048:ℝ)) : (560227329/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (598252507/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (636602027/5000000000:ℝ) := by nlinarith
  have hc1 : (123988212271/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (123988212271/125000000000:ℝ) ≤ taylorCos (636602027/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (992850416729/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (598252507/5000000000:ℝ) + taylorErr ≤ (992850416729/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59682606247/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59682606247/500000000000:ℝ) ≤ taylorSin (598252507/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31744174691/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/5000000000:ℝ) + taylorErr ≤ (31744174691/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-992850416729/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123988212271/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31744174691/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-59682606247/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (815310788761/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (653782611797/200000000000:ℝ) := by nlinarith
  have hp1 : (2698676397599/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (541004654791/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-343474925407/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-644256163303/1000000000000:ℝ) := by nlinarith
  have hN : (152477923677/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10185792587203/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152477923677/500000000000:ℝ) (10185792587203/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (560227329/2500000000000:ℝ) ≤ ((152477923677/500000000000:ℝ)/(10185792587203/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_25 (x : ℝ) (h₁ : (1063/1024:ℝ) ≤ x) (h₂ : x ≤ (267/256:ℝ)) : (1626727581/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (598252507/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (992850416729/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (598252507/5000000000:ℝ) + taylorErr ≤ (992850416729/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59682606247/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59682606247/500000000000:ℝ) ≤ taylorSin (598252507/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-992850416729/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990902633157/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-59682606247/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (815310788761/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/250000000000:ℝ) := by nlinarith
  have hp1 : (2698676397599/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-182449058647/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-644256163303/1000000000000:ℝ) := by nlinarith
  have hN : (261106398569/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2558998978231/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (261106398569/1000000000000:ℝ) (2558998978231/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1626727581/10000000000000:ℝ) ≤ ((261106398569/1000000000000:ℝ)/(2558998978231/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_26 (x : ℝ) (h₁ : (4257/4096:ℝ) ≤ x) (h₂ : x ≤ (8519/8192:ℝ)) : (482068367/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (617427267/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (250805859/2000000000:ℝ) := by nlinarith
  have hc1 : (496073674649/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (496073674649/500000000000:ℝ) ≤ taylorCos (250805859/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (62024084821/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (617427267/5000000000:ℝ) + taylorErr ≤ (62024084821/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61585929551/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61585929551/500000000000:ℝ) ≤ taylorSin (617427267/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (62537255613/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (250805859/2000000000:ℝ) + taylorErr ≤ (62537255613/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-62024084821/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-496073674649/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-62537255613/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61585929551/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1632539053507/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3266995583/1000000000:ℝ) := by nlinarith
  have hp1 : (1350924908817/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5406873127833/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-27050480549/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-83197966263/125000000000:ℝ) := by nlinarith
  have hN : (315885335573/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5086630069671/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (315885335573/1000000000000:ℝ) (5086630069671/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (482068367/2000000000000:ℝ) ≤ ((315885335573/1000000000000:ℝ)/(5086630069671/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_27 (x : ℝ) (h₁ : (4257/4096:ℝ) ≤ x) (h₂ : x ≤ (2131/2048:ℝ)) : (560227329/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (617427267/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (636602027/5000000000:ℝ) := by nlinarith
  have hc1 : (123988212271/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (123988212271/125000000000:ℝ) ≤ taylorCos (636602027/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (62024084821/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (617427267/5000000000:ℝ) + taylorErr ≤ (62024084821/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61585929551/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61585929551/500000000000:ℝ) ≤ taylorSin (617427267/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31744174691/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/5000000000:ℝ) + taylorErr ≤ (31744174691/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-62024084821/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123988212271/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31744174691/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61585929551/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1632539053507/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (653782611797/200000000000:ℝ) := by nlinarith
  have hp1 : (1350924908817/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (541004654791/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-343474925407/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-83197966263/125000000000:ℝ) := by nlinarith
  have hN : (152477923677/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10185792587203/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152477923677/500000000000:ℝ) (10185792587203/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (560227329/2500000000000:ℝ) ≤ ((152477923677/500000000000:ℝ)/(10185792587203/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_28 (x : ℝ) (h₁ : (8519/8192:ℝ) ≤ x) (h₂ : x ≤ (2131/2048:ℝ)) : (560227329/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (627014647/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (636602027/5000000000:ℝ) := by nlinarith
  have hc1 : (123988212271/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (123988212271/125000000000:ℝ) ≤ taylorCos (636602027/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198429470767/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (627014647/5000000000:ℝ) + taylorErr ≤ (198429470767/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (62537253301/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (62537253301/500000000000:ℝ) ≤ taylorSin (627014647/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (31744174691/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/5000000000:ℝ) + taylorErr ≤ (31744174691/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198429470767/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123988212271/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31744174691/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-62537253301/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3266995582999/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (653782611797/200000000000:ℝ) := by nlinarith
  have hp1 : (5406873055303/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (541004654791/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-343474925407/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-676261979651/1000000000000:ℝ) := by nlinarith
  have hN : (152477923677/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10185792587203/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152477923677/500000000000:ℝ) (10185792587203/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (560227329/2500000000000:ℝ) ≤ ((152477923677/500000000000:ℝ)/(10185792587203/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_29 (x : ℝ) (h₁ : (2131/2048:ℝ) ≤ x) (h₂ : x ≤ (8529/8192:ℝ)) : (1038927507/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1273204053/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (646189407/5000000000:ℝ) := by nlinarith
  have hc1 : (991660400073/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (991660400073/1000000000000:ℝ) ≤ taylorCos (646189407/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198381140541/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1273204053/10000000000:ℝ) + taylorErr ≤ (198381140541/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (126976694141/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (126976694141/1000000000000:ℝ) ≤ taylorSin (1273204053/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (25775683909/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (646189407/5000000000:ℝ) + taylorErr ≤ (25775683909/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198381140541/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-991660400073/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-25775683909/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-126976694141/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (408614132373/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (327083053497/100000000000:ℝ) := by nlinarith
  have hp1 : (2705023237669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1353304991997/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-174411808531/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-686949816587/1000000000000:ℝ) := by nlinarith
  have hN : (294013165949/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4079332955397/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (294013165949/1000000000000:ℝ) (4079332955397/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1038927507/5000000000000:ℝ) ≤ ((294013165949/1000000000000:ℝ)/(4079332955397/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_30 (x : ℝ) (h₁ : (2131/2048:ℝ) ≤ x) (h₂ : x ≤ (4267/4096:ℝ)) : (1921155551/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1273204053/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (655776787/5000000000:ℝ) := by nlinarith
  have hc1 : (991411455927/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (991411455927/1000000000000:ℝ) ≤ taylorCos (655776787/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198381140541/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1273204053/10000000000:ℝ) + taylorErr ≤ (198381140541/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (126976694141/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (126976694141/1000000000000:ℝ) ≤ taylorSin (1273204053/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (130779666477/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (655776787/5000000000:ℝ) + taylorErr ≤ (130779666477/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198381140541/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-991411455927/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-130779666477/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-126976694141/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (408614132373/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (654549602191/200000000000:ℝ) := by nlinarith
  have hp1 : (2705023237669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2708196694033/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-885442651/1250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-686949816587/1000000000000:ℝ) := by nlinarith
  have hN : (283057335127/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1021087954321/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (283057335127/1000000000000:ℝ) (1021087954321/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1921155551/10000000000000:ℝ) ≤ ((283057335127/1000000000000:ℝ)/(1021087954321/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_31 (x : ℝ) (h₁ : (2131/2048:ℝ) ≤ x) (h₂ : x ≤ (267/256:ℝ)) : (1626727581/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1273204053/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (198381140541/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1273204053/10000000000:ℝ) + taylorErr ≤ (198381140541/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (126976694141/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (126976694141/1000000000000:ℝ) ≤ taylorSin (1273204053/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-198381140541/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990902633157/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-126976694141/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (408614132373/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/250000000000:ℝ) := by nlinarith
  have hp1 : (2705023237669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-182449058647/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-686949816587/1000000000000:ℝ) := by nlinarith
  have hN : (261106398569/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2558998978231/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (261106398569/1000000000000:ℝ) (2558998978231/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1626727581/10000000000000:ℝ) ≤ ((261106398569/1000000000000:ℝ)/(2558998978231/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_32 (x : ℝ) (h₁ : (8529/8192:ℝ) ≤ x) (h₂ : x ≤ (4267/4096:ℝ)) : (1921155551/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1292378813/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (655776787/5000000000:ℝ) := by nlinarith
  have hc1 : (991411455927/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (991411455927/1000000000000:ℝ) ≤ taylorCos (655776787/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (99166040461/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1292378813/10000000000:ℝ) + taylorErr ≤ (99166040461/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (64439207461/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (64439207461/500000000000:ℝ) ≤ taylorSin (1292378813/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (130779666477/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (655776787/5000000000:ℝ) + taylorErr ≤ (130779666477/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-99166040461/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-991411455927/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-130779666477/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-64439207461/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3270830534969/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (654549602191/200000000000:ℝ) := by nlinarith
  have hp1 : (5413219895373/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2708196694033/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-885442651/1250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-697647199739/1000000000000:ℝ) := by nlinarith
  have hN : (283057335127/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1021087954321/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (283057335127/1000000000000:ℝ) (1021087954321/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1921155551/10000000000000:ℝ) ≤ ((283057335127/1000000000000:ℝ)/(1021087954321/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_33 (x : ℝ) (h₁ : (4267/4096:ℝ) ≤ x) (h₂ : x ≤ (8539/8192:ℝ)) : (1770787537/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1311553573/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (665364167/5000000000:ℝ) := by nlinarith
  have hc1 : (198231773329/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198231773329/200000000000:ℝ) ≤ taylorCos (665364167/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61963216279/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1311553573/10000000000:ℝ) + taylorErr ≤ (61963216279/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (65389830927/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (65389830927/500000000000:ℝ) ≤ taylorSin (1311553573/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (13268043257/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (665364167/5000000000:ℝ) + taylorErr ≤ (13268043257/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61963216279/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-198231773329/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13268043257/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-65389830927/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1636374005477/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3274665486939/1000000000000:ℝ) := by nlinarith
  have hp1 : (338524582213/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2709783404071/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-719070468447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-708354086257/1000000000000:ℝ) := by nlinarith
  have hN : (136044199099/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20446868102699/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (136044199099/500000000000:ℝ) (20446868102699/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1770787537/10000000000000:ℝ) ≤ ((136044199099/500000000000:ℝ)/(20446868102699/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_34 (x : ℝ) (h₁ : (4267/4096:ℝ) ≤ x) (h₂ : x ≤ (267/256:ℝ)) : (1626727581/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1311553573/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61963216279/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1311553573/10000000000:ℝ) + taylorErr ≤ (61963216279/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (65389830927/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (65389830927/500000000000:ℝ) ≤ taylorSin (1311553573/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61963216279/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990902633157/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-65389830927/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1636374005477/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/250000000000:ℝ) := by nlinarith
  have hp1 : (338524582213/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-182449058647/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-708354086257/1000000000000:ℝ) := by nlinarith
  have hN : (261106398569/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2558998978231/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (261106398569/1000000000000:ℝ) (2558998978231/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1626727581/10000000000000:ℝ) ≤ ((261106398569/1000000000000:ℝ)/(2558998978231/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_35 (x : ℝ) (h₁ : (8539/8192:ℝ) ≤ x) (h₂ : x ≤ (267/256:ℝ)) : (1626727581/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1330728333/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (991158871183/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1330728333/10000000000:ℝ) + taylorErr ≤ (991158871183/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (132680427947/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (132680427947/1000000000000:ℝ) ≤ taylorSin (1330728333/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-991158871183/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990902633157/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-132680427947/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1637332743469/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/250000000000:ℝ) := by nlinarith
  have hp1 : (5419566735441/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-182449058647/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-143814086749/200000000000:ℝ) := by nlinarith
  have hN : (261106398569/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2558998978231/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (261106398569/1000000000000:ℝ) (2558998978231/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1626727581/10000000000000:ℝ) ≤ ((261106398569/1000000000000:ℝ)/(2558998978231/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_36 (x : ℝ) (h₁ : (267/256:ℝ) ≤ x) (h₂ : x ≤ (17093/16384:ℝ)) : (778527907/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (679745237/5000000000:ℝ) := by nlinarith
  have hc1 : (990773150129/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990773150129/1000000000000:ℝ) ≤ taylorCos (679745237/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8470666553/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (679745237/5000000000:ℝ) + taylorErr ≤ (8470666553/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990773150129/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8470666553/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3276582962923/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3277541700917/1000000000000:ℝ) := by nlinarith
  have hp1 : (1355685038869/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5424326938259/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-91895329537/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-364898099861/500000000000:ℝ) := by nlinarith
  have hN : (255610513833/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8193823681/400000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (255610513833/1000000000000:ℝ) (8193823681/400000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (778527907/5000000000000:ℝ) ≤ ((255610513833/1000000000000:ℝ)/(8193823681/400000000:ℝ))^2 := by norm_num
  linarith

theorem wc_37 (x : ℝ) (h₁ : (267/256:ℝ) ≤ x) (h₂ : x ≤ (8549/8192:ℝ)) : (1488952289/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (684538927/5000000000:ℝ) := by nlinarith
  have hc1 : (247660689101/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (247660689101/250000000000:ℝ) ≤ taylorCos (684538927/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (27296098857/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (684538927/5000000000:ℝ) + taylorErr ≤ (27296098857/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-247660689101/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27296098857/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3276582962923/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3278500438909/1000000000000:ℝ) := by nlinarith
  have hp1 : (1355685038869/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5425913648297/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-185132844167/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-364898099861/500000000000:ℝ) := by nlinarith
  have hN : (31263922467/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10248565127927/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (31263922467/125000000000:ℝ) (10248565127927/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1488952289/10000000000000:ℝ) ≤ ((31263922467/125000000000:ℝ)/(10248565127927/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_38 (x : ℝ) (h₁ : (267/256:ℝ) ≤ x) (h₂ : x ≤ (4277/4096:ℝ)) : (135743827/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (694126307/5000000000:ℝ) := by nlinarith
  have hc1 : (495189618671/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495189618671/500000000000:ℝ) ≤ taylorCos (694126307/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (27675955187/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (694126307/5000000000:ℝ) + taylorErr ≤ (27675955187/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495189618671/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27675955187/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3276582962923/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1640208957447/500000000000:ℝ) := by nlinarith
  have hp1 : (1355685038869/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2714543534187/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-375637926027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-364898099861/500000000000:ℝ) := by nlinarith
  have hN : (29887923161/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4104456678543/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29887923161/125000000000:ℝ) (4104456678543/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (135743827/1000000000000:ℝ) ≤ ((29887923161/125000000000:ℝ)/(4104456678543/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_39 (x : ℝ) (h₁ : (267/256:ℝ) ≤ x) (h₂ : x ≤ (2141/2048:ℝ)) : (139137559/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1426602133/10000000000:ℝ) := by nlinarith
  have hc1 : (989841276193/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989841276193/1000000000000:ℝ) ≤ taylorCos (1426602133/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8886050363/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1426602133/10000000000:ℝ) + taylorErr ≤ (8886050363/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989841276193/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8886050363/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3276582962923/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (205265804179/62500000000:ℝ) := by nlinarith
  have hp1 : (1355685038869/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (543543390853/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-188670076/244140625:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-364898099861/500000000000:ℝ) := by nlinarith
  have hN : (217048644897/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20572633787009/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (217048644897/1000000000000:ℝ) (20572633787009/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (139137559/1250000000000:ℝ) ≤ ((217048644897/1000000000000:ℝ)/(20572633787009/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_40 (x : ℝ) (h₁ : (267/256:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by nlinarith
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3276582962923/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by nlinarith
  have hp1 : (1355685038869/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-364898099861/500000000000:ℝ) := by nlinarith
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_41 (x : ℝ) (h₁ : (267/256:ℝ) ≤ x) (h₂ : x ≤ (539/512:ℝ)) : (160574441/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1656699251/10000000000:ℝ) := by nlinarith
  have hc1 : (986308094981/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986308094981/1000000000000:ℝ) ≤ taylorCos (1656699251/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-495451318847/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986308094981/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4122828069/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-134580706211/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3276582962923/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1653631289341/500000000000:ℝ) := by nlinarith
  have hp1 : (1355685038869/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2736757474729/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-902654442789/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-364898099861/500000000000:ℝ) := by nlinarith
  have hN : (2614176631/31250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20875971528701/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2614176631/31250000000:ℝ) (20875971528701/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (160574441/10000000000000:ℝ) ≤ ((2614176631/31250000000:ℝ)/(20875971528701/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_42 (x : ℝ) (h₁ : (17093/16384:ℝ) ≤ x) (h₂ : x ≤ (8549/8192:ℝ)) : (1488952289/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1359490473/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (684538927/5000000000:ℝ) := by nlinarith
  have hc1 : (247660689101/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (247660689101/250000000000:ℝ) ≤ taylorCos (684538927/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (990773154667/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1359490473/10000000000:ℝ) + taylorErr ≤ (990773154667/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5421226409/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5421226409/40000000000:ℝ) ≤ taylorSin (1359490473/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (27296098857/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (684538927/5000000000:ℝ) + taylorErr ≤ (27296098857/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-990773154667/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-247660689101/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27296098857/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5421226409/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (819385425229/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3278500438909/1000000000000:ℝ) := by nlinarith
  have hp1 : (1084865373099/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5425913648297/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-185132844167/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-183790650339/250000000000:ℝ) := by nlinarith
  have hN : (31263922467/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10248565127927/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (31263922467/125000000000:ℝ) (10248565127927/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1488952289/10000000000000:ℝ) ≤ ((31263922467/125000000000:ℝ)/(10248565127927/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_43 (x : ℝ) (h₁ : (8549/8192:ℝ) ≤ x) (h₂ : x ≤ (17103/16384:ℝ)) : (1422414083/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1369077853/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (689332617/5000000000:ℝ) := by nlinarith
  have hc1 : (990511452101/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990511452101/1000000000000:ℝ) ≤ taylorCos (689332617/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (495321380471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1369077853/10000000000:ℝ) + taylorErr ≤ (495321380471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (136480489661/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (136480489661/1000000000000:ℝ) ≤ taylorSin (1369077853/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (67104589/488281250:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (689332617/5000000000:ℝ) + taylorErr ≤ (67104589/488281250:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-495321380471/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990511452101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-67104589/488281250:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-136480489661/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (819625109727/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1639729588451/500000000000:ℝ) := by nlinarith
  have hp1 : (678239196939/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5427500358337/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11654725787/15625000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-185132835411/250000000000:ℝ) := by nlinarith
  have hN : (244609001733/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10254852492967/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (244609001733/1000000000000:ℝ) (10254852492967/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1422414083/10000000000000:ℝ) ≤ ((244609001733/1000000000000:ℝ)/(10254852492967/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_44 (x : ℝ) (h₁ : (8549/8192:ℝ) ≤ x) (h₂ : x ≤ (4277/4096:ℝ)) : (135743827/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1369077853/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (694126307/5000000000:ℝ) := by nlinarith
  have hc1 : (495189618671/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495189618671/500000000000:ℝ) ≤ taylorCos (694126307/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (495321380471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1369077853/10000000000:ℝ) + taylorErr ≤ (495321380471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (136480489661/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (136480489661/1000000000000:ℝ) ≤ taylorSin (1369077853/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (27675955187/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (694126307/5000000000:ℝ) + taylorErr ≤ (27675955187/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-495321380471/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495189618671/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27675955187/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-136480489661/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (819625109727/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1640208957447/500000000000:ℝ) := by nlinarith
  have hp1 : (678239196939/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2714543534187/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-375637926027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-185132835411/250000000000:ℝ) := by nlinarith
  have hN : (29887923161/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4104456678543/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29887923161/125000000000:ℝ) (4104456678543/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (135743827/1000000000000:ℝ) ≤ ((29887923161/125000000000:ℝ)/(4104456678543/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_45 (x : ℝ) (h₁ : (17103/16384:ℝ) ≤ x) (h₂ : x ≤ (4277/4096:ℝ)) : (135743827/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1378665233/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (694126307/5000000000:ℝ) := by nlinarith
  have hc1 : (495189618671/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495189618671/500000000000:ℝ) ≤ taylorCos (694126307/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (990511456639/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1378665233/10000000000:ℝ) + taylorErr ≤ (990511456639/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8589387103/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8589387103/62500000000:ℝ) ≤ taylorSin (1378665233/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (27675955187/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (694126307/5000000000:ℝ) + taylorErr ≤ (27675955187/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-990511456639/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495189618671/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27675955187/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-8589387103/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3279459176901/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1640208957447/500000000000:ℝ) := by nlinarith
  have hp1 : (542750028553/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2714543534187/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-375637926027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-23309450477/31250000000:ℝ) := by nlinarith
  have hN : (29887923161/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4104456678543/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (29887923161/125000000000:ℝ) (4104456678543/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (135743827/1000000000000:ℝ) ≤ ((29887923161/125000000000:ℝ)/(4104456678543/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_46 (x : ℝ) (h₁ : (4277/4096:ℝ) ≤ x) (h₂ : x ≤ (17113/16384:ℝ)) : (323505483/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1388252613/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1397839993/10000000000:ℝ) := by nlinarith
  have hc1 : (990246112261/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990246112261/1000000000000:ℝ) ≤ taylorCos (1397839993/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (24759481047/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1388252613/10000000000:ℝ) + taylorErr ≤ (24759481047/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8648735707/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8648735707/62500000000:ℝ) ≤ taylorSin (1388252613/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (2177019161/15625000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1397839993/10000000000:ℝ) + taylorErr ≤ (2177019161/15625000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-24759481047/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990246112261/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2177019161/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-8648735707/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3280417914893/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1640688326443/500000000000:ℝ) := by nlinarith
  have hp1 : (5429086995547/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1357668444603/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-47290723491/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-187818954219/250000000000:ℝ) := by nlinarith
  have hN : (46718907281/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20534865476211/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (46718907281/200000000000:ℝ) (20534865476211/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (323505483/2500000000000:ℝ) ≤ ((46718907281/200000000000:ℝ)/(20534865476211/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_47 (x : ℝ) (h₁ : (4277/4096:ℝ) ≤ x) (h₂ : x ≤ (8559/8192:ℝ)) : (1232162133/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1388252613/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1407427373/10000000000:ℝ) := by nlinarith
  have hc1 : (990112076953/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990112076953/1000000000000:ℝ) ≤ taylorCos (1407427373/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (24759481047/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1388252613/10000000000:ℝ) + taylorErr ≤ (24759481047/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8648735707/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8648735707/62500000000:ℝ) ≤ taylorSin (1388252613/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (4383704647/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1407427373/10000000000:ℝ) + taylorErr ≤ (4383704647/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-24759481047/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990112076953/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4383704647/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-8648735707/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3280417914893/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3282335390879/1000000000000:ℝ) := by nlinarith
  have hp1 : (5429086995547/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1358065122113/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-762029617503/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-187818954219/250000000000:ℝ) := by nlinarith
  have hN : (4561649189/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10273725618217/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4561649189/20000000000:ℝ) (10273725618217/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1232162133/10000000000000:ℝ) ≤ ((4561649189/20000000000:ℝ)/(10273725618217/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_48 (x : ℝ) (h₁ : (4277/4096:ℝ) ≤ x) (h₂ : x ≤ (2141/2048:ℝ)) : (139137559/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1388252613/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1426602133/10000000000:ℝ) := by nlinarith
  have hc1 : (989841276193/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989841276193/1000000000000:ℝ) ≤ taylorCos (1426602133/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (24759481047/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1388252613/10000000000:ℝ) + taylorErr ≤ (24759481047/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8648735707/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8648735707/62500000000:ℝ) ≤ taylorSin (1388252613/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8886050363/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1426602133/10000000000:ℝ) + taylorErr ≤ (8886050363/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-24759481047/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989841276193/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8886050363/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-8648735707/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3280417914893/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (205265804179/62500000000:ℝ) := by nlinarith
  have hp1 : (5429086995547/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (543543390853/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-188670076/244140625:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-187818954219/250000000000:ℝ) := by nlinarith
  have hN : (217048644897/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20572633787009/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (217048644897/1000000000000:ℝ) (20572633787009/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (139137559/1250000000000:ℝ) ≤ ((217048644897/1000000000000:ℝ)/(20572633787009/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_49 (x : ℝ) (h₁ : (17113/16384:ℝ) ≤ x) (h₂ : x ≤ (8559/8192:ℝ)) : (1232162133/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (174729999/1250000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1407427373/10000000000:ℝ) := by nlinarith
  have hc1 : (990112076953/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990112076953/1000000000000:ℝ) ≤ taylorCos (1407427373/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (990246116799/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (174729999/1250000000:ℝ) + taylorErr ≤ (990246116799/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (139329221681/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (139329221681/1000000000000:ℝ) ≤ taylorSin (174729999/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (4383704647/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1407427373/10000000000:ℝ) + taylorErr ≤ (4383704647/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-990246116799/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-990112076953/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4383704647/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-139329221681/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (656275330577/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3282335390879/1000000000000:ℝ) := by nlinarith
  have hp1 : (5430673705563/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1358065122113/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-762029617503/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-756651540599/1000000000000:ℝ) := by nlinarith
  have hN : (4561649189/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10273725618217/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4561649189/20000000000:ℝ) (10273725618217/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1232162133/10000000000000:ℝ) ≤ ((4561649189/20000000000:ℝ)/(10273725618217/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_50 (x : ℝ) (h₁ : (8559/8192:ℝ) ≤ x) (h₂ : x ≤ (17123/16384:ℝ)) : (585927977/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (351856843/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1417014753/10000000000:ℝ) := by nlinarith
  have hc1 : (247494282889/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (247494282889/250000000000:ℝ) ≤ taylorCos (1417014753/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247528020373/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (351856843/2500000000:ℝ) + taylorErr ≤ (247528020373/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (140278544081/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (140278544081/1000000000000:ℝ) ≤ taylorSin (351856843/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (141227742163/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1417014753/10000000000:ℝ) + taylorErr ≤ (141227742163/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247528020373/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-247494282889/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-141227742163/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-140278544081/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1641167695439/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3283294128871/1000000000000:ℝ) := by nlinarith
  have hp1 : (2716130207791/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (543384719849/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-383704985551/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-381014791083/500000000000:ℝ) := by nlinarith
  have hN : (111283580227/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10280020336679/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (111283580227/500000000000:ℝ) (10280020336679/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (585927977/5000000000000:ℝ) ≤ ((111283580227/500000000000:ℝ)/(10280020336679/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_51 (x : ℝ) (h₁ : (8559/8192:ℝ) ≤ x) (h₂ : x ≤ (2141/2048:ℝ)) : (139137559/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (351856843/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1426602133/10000000000:ℝ) := by nlinarith
  have hc1 : (989841276193/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989841276193/1000000000000:ℝ) ≤ taylorCos (1426602133/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247528020373/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (351856843/2500000000:ℝ) + taylorErr ≤ (247528020373/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (140278544081/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (140278544081/1000000000000:ℝ) ≤ taylorSin (351856843/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8886050363/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1426602133/10000000000:ℝ) + taylorErr ≤ (8886050363/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247528020373/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989841276193/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8886050363/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-140278544081/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1641167695439/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (205265804179/62500000000:ℝ) := by nlinarith
  have hp1 : (2716130207791/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (543543390853/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-188670076/244140625:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-381014791083/500000000000:ℝ) := by nlinarith
  have hN : (217048644897/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20572633787009/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (217048644897/1000000000000:ℝ) (20572633787009/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (139137559/1250000000000:ℝ) ≤ ((217048644897/1000000000000:ℝ)/(20572633787009/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_52 (x : ℝ) (h₁ : (17123/16384:ℝ) ≤ x) (h₂ : x ≤ (2141/2048:ℝ)) : (139137559/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (44281711/312500000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1426602133/10000000000:ℝ) := by nlinarith
  have hc1 : (989841276193/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989841276193/1000000000000:ℝ) ≤ taylorCos (1426602133/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (494988568047/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (44281711/312500000:ℝ) + taylorErr ≤ (494988568047/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (141227737539/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (141227737539/1000000000000:ℝ) ≤ taylorSin (44281711/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (8886050363/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1426602133/10000000000:ℝ) + taylorErr ≤ (8886050363/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-494988568047/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989841276193/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8886050363/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-141227737539/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (328329412887/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (205265804179/62500000000:ℝ) := by nlinarith
  have hp1 : (2716923562799/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (543543390853/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-188670076/244140625:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-767409935681/1000000000000:ℝ) := by nlinarith
  have hN : (217048644897/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20572633787009/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (217048644897/1000000000000:ℝ) (20572633787009/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (139137559/1250000000000:ℝ) ≤ ((217048644897/1000000000000:ℝ)/(20572633787009/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_53 (x : ℝ) (h₁ : (2141/2048:ℝ) ≤ x) (h₂ : x ≤ (17133/16384:ℝ)) : (1055892761/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1436189513/10000000000:ℝ) := by nlinarith
  have hc1 : (989704510989/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989704510989/1000000000000:ℝ) ≤ taylorCos (1436189513/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989841280731/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/2500000000:ℝ) + taylorErr ≤ (989841280731/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28435360237/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28435360237/200000000000:ℝ) ≤ taylorSin (356650533/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (143125738767/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1436189513/10000000000:ℝ) + taylorErr ≤ (143125738767/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-989841280731/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989704510989/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-143125738767/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-28435360237/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3284252866863/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (410651450607/125000000000:ℝ) := by nlinarith
  have hp1 : (5435433835617/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (679627577321/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-194544398181/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3863962979/5000000000:ℝ) := by nlinarith
  have hN : (42305383653/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10292615288681/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (42305383653/200000000000:ℝ) (10292615288681/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1055892761/10000000000000:ℝ) ≤ ((42305383653/200000000000:ℝ)/(10292615288681/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_54 (x : ℝ) (h₁ : (2141/2048:ℝ) ≤ x) (h₂ : x ≤ (8569/8192:ℝ)) : (1000229897/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1445776893/10000000000:ℝ) := by nlinarith
  have hc1 : (98956683607/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (98956683607/100000000000:ℝ) ≤ taylorCos (1445776893/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989841280731/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/2500000000:ℝ) + taylorErr ≤ (989841280731/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28435360237/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28435360237/200000000000:ℝ) ≤ taylorSin (356650533/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (18009317521/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1445776893/10000000000:ℝ) + taylorErr ≤ (18009317521/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-989841280731/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-98956683607/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18009317521/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-28435360237/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3284252866863/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3286170342849/1000000000000:ℝ) := by nlinarith
  have hp1 : (5435433835617/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5438607328607/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-97945606253/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3863962979/5000000000:ℝ) := by nlinarith
  have hN : (103000993023/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20597831044441/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (103000993023/500000000000:ℝ) (20597831044441/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1000229897/10000000000000:ℝ) ≤ ((103000993023/500000000000:ℝ)/(20597831044441/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_55 (x : ℝ) (h₁ : (2141/2048:ℝ) ≤ x) (h₂ : x ≤ (4287/4096:ℝ)) : (446763507/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1464951653/10000000000:ℝ) := by nlinarith
  have hc1 : (494644378797/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494644378797/500000000000:ℝ) ≤ taylorCos (1464951653/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989841280731/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/2500000000:ℝ) + taylorErr ≤ (989841280731/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28435360237/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28435360237/200000000000:ℝ) ≤ taylorSin (356650533/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-989841280731/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494644378797/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18246468101/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-28435360237/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3284252866863/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3288087818833/1000000000000:ℝ) := by nlinarith
  have hp1 : (5435433835617/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5441780748683/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-198586557687/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3863962979/5000000000:ℝ) := by nlinarith
  have hN : (97471263423/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5155760752179/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (97471263423/500000000000:ℝ) (5155760752179/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (446763507/5000000000000:ℝ) ≤ ((97471263423/500000000000:ℝ)/(5155760752179/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_56 (x : ℝ) (h₁ : (2141/2048:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by nlinarith
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989841280731/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/2500000000:ℝ) + taylorErr ≤ (989841280731/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28435360237/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28435360237/200000000000:ℝ) ≤ taylorSin (356650533/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-989841280731/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-28435360237/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3284252866863/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by nlinarith
  have hp1 : (5435433835617/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3863962979/5000000000:ℝ) := by nlinarith
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_57 (x : ℝ) (h₁ : (17133/16384:ℝ) ≤ x) (h₂ : x ≤ (8569/8192:ℝ)) : (1000229897/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (179523689/1250000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1445776893/10000000000:ℝ) := by nlinarith
  have hc1 : (98956683607/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (98956683607/100000000000:ℝ) ≤ taylorCos (1445776893/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (123713064441/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (179523689/1250000000:ℝ) + taylorErr ≤ (123713064441/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (559084899/3906250000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (559084899/3906250000:ℝ) ≤ taylorSin (179523689/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (18009317521/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1445776893/10000000000:ℝ) + taylorErr ≤ (18009317521/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-123713064441/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-98956683607/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18009317521/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-559084899/3906250000:ℝ) := by rw [hsx]; linarith
  have hb1 : (657042320971/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3286170342849/1000000000000:ℝ) := by nlinarith
  have hp1 : (5437020545633/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5438607328607/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-97945606253/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-778177557149/1000000000000:ℝ) := by nlinarith
  have hN : (103000993023/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20597831044441/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (103000993023/500000000000:ℝ) (20597831044441/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1000229897/10000000000000:ℝ) ≤ ((103000993023/500000000000:ℝ)/(20597831044441/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_58 (x : ℝ) (h₁ : (8569/8192:ℝ) ≤ x) (h₂ : x ≤ (17143/16384:ℝ)) : (236527239/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (361444223/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1455364273/10000000000:ℝ) := by nlinarith
  have hc1 : (989428251563/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989428251563/1000000000000:ℝ) ≤ taylorCos (1455364273/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989566840609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (361444223/2500000000:ℝ) + taylorErr ≤ (989566840609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28814907109/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28814907109/200000000000:ℝ) ≤ taylorSin (361444223/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (145023209139/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1455364273/10000000000:ℝ) + taylorErr ≤ (145023209139/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-989566840609/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989428251563/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-145023209139/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-28814907109/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (51346411607/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3287129080841/1000000000000:ℝ) := by nlinarith
  have hp1 : (1359651813913/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1088038807729/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6163706233/7812500000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-783564814369/1000000000000:ℝ) := by nlinarith
  have hN : (200473853739/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10305217594111/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (200473853739/1000000000000:ℝ) (10305217594111/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (236527239/2500000000000:ℝ) ≤ ((200473853739/1000000000000:ℝ)/(10305217594111/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_59 (x : ℝ) (h₁ : (8569/8192:ℝ) ≤ x) (h₂ : x ≤ (4287/4096:ℝ)) : (446763507/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (361444223/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1464951653/10000000000:ℝ) := by nlinarith
  have hc1 : (494644378797/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494644378797/500000000000:ℝ) ≤ taylorCos (1464951653/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989566840609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (361444223/2500000000:ℝ) + taylorErr ≤ (989566840609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28814907109/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28814907109/200000000000:ℝ) ≤ taylorSin (361444223/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-989566840609/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494644378797/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18246468101/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-28814907109/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (51346411607/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3288087818833/1000000000000:ℝ) := by nlinarith
  have hp1 : (1359651813913/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5441780748683/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-198586557687/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-783564814369/1000000000000:ℝ) := by nlinarith
  have hN : (97471263423/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5155760752179/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (97471263423/500000000000:ℝ) (5155760752179/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (446763507/5000000000000:ℝ) ≤ ((97471263423/500000000000:ℝ)/(5155760752179/250000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
