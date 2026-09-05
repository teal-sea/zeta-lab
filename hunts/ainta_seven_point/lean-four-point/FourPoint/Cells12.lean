import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_720 (x : ℝ) (h₁ : (32913/8192:ℝ) ≤ x) (h₂ : x ≤ (8241/2048:ℝ)) : (2602367/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/2000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (499227171153/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/2000000000:ℝ) + taylorErr ≤ (499227171153/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13894537137/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13894537137/250000000000:ℝ) ≤ taylorSin (111213607/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499227171153/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13894537137/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (75094303203/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (39443679431/3125000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6320767836483/500000000000:ℝ) := by nlinarith
  have hp1 : (130558467007/6250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20921723886119/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (580495829881/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (785551138517/500000000000:ℝ) := by nlinarith
  have hN : (10158582341/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19913553021359/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (10158582341/62500000000:ℝ) (19913553021359/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2602367/10000000000000:ℝ) ≤ ((10158582341/62500000000:ℝ)/(19913553021359/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_721 (x : ℝ) (h₁ : (32913/8192:ℝ) ≤ x) (h₂ : x ≤ (4123/1024:ℝ)) : (1298021/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/2000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (499227171153/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/2000000000:ℝ) + taylorErr ≤ (499227171153/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13894537137/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13894537137/250000000000:ℝ) ≤ taylorSin (111213607/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499227171153/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13894537137/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (41370133433/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (39443679431/3125000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2529841115381/200000000000:ℝ) := by nlinarith
  have hp1 : (130558467007/6250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5233604391607/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (580495829881/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1732119296131/1000000000000:ℝ) := by nlinarith
  have hN : (10158582341/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (31900480345361/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (10158582341/62500000000:ℝ) (31900480345361/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1298021/5000000000000:ℝ) ≤ ((10158582341/62500000000:ℝ)/(31900480345361/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_722 (x : ℝ) (h₁ : (16459/4096:ℝ) ≤ x) (h₂ : x ≤ (8265/2048:ℝ)) : (2002543/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/2000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (139975747/1250000000:ℝ) := by nlinarith
  have hc1 : (993736719669/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (993736719669/1000000000000:ℝ) ≤ taylorCos (139975747/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (499172968543/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/2000000000:ℝ) + taylorErr ≤ (499172968543/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57492557437/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57492557437/1000000000000:ℝ) ≤ taylorSin (115048559/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (111746713557/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (139975747/1250000000:ℝ) + taylorErr ≤ (111746713557/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (993736719669/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499172968543/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (57492557437/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (111746713557/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (788993430869/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (20285361939/1600000000:ℝ) := by nlinarith
  have hp1 : (20892528141153/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5245663387901/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1201164874159/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2344742576097/1000000000000:ℝ) := by nlinarith
  have hN : (202818937073/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (64096235780661/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (202818937073/1000000000000:ℝ) (64096235780661/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2002543/5000000000000:ℝ) ≤ ((202818937073/1000000000000:ℝ)/(64096235780661/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_723 (x : ℝ) (h₁ : (4115/1024:ℝ) ≤ x) (h₂ : x ≤ (32971/8192:ℝ)) : (471761/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (582912699/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3113981/40000000:ℝ) := by nlinarith
  have hc1 : (62310703349/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62310703349/62500000000:ℝ) ≤ taylorCos (3113981/40000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (499150773599/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (582912699/10000000000:ℝ) + taylorErr ≤ (499150773599/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58258262199/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58258262199/1000000000000:ℝ) ≤ taylorSin (582912699/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (1555418319/20000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3113981/40000000:ℝ) + taylorErr ≤ (1555418319/20000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (62310703349/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499150773599/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58258262199/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1555418319/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6312330942149/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2528844027869/200000000000:ℝ) := by nlinarith
  have hp1 : (20893797509167/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20926166674227/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1217236333621/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1627447149577/1000000000000:ℝ) := by nlinarith
  have hN : (218934786423/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (79688151466109/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (218934786423/1000000000000:ℝ) (79688151466109/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (471761/1000000000000:ℝ) ≤ ((218934786423/1000000000000:ℝ)/(79688151466109/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_724 (x : ℝ) (h₁ : (16461/4096:ℝ) ≤ x) (h₂ : x ≤ (32973/8192:ℝ)) : (2718231/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (590582603/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (393082577/5000000000:ℝ) := by nlinarith
  have hc1 : (2492278277/2500000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (2492278277/2500000000:ℝ) ≤ taylorCos (393082577/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (249564142509/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (590582603/10000000000:ℝ) + taylorErr ≤ (249564142509/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59023932689/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59023932689/1000000000000:ℝ) ≤ taylorSin (590582603/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (39267780191/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (393082577/5000000000:ℝ) + taylorErr ≤ (39267780191/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (2492278277/2500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249564142509/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (59023932689/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (39267780191/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3156357218673/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12644987129739/1000000000000:ℝ) := by nlinarith
  have hp1 : (20895066877181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20927436042259/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (123330902089/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (821773958469/500000000000:ℝ) := by nlinarith
  have hN : (117526225427/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (31879139902253/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (117526225427/500000000000:ℝ) (31879139902253/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2718231/5000000000000:ℝ) ≤ ((117526225427/500000000000:ℝ)/(31879139902253/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_725 (x : ℝ) (h₁ : (16461/4096:ℝ) ≤ x) (h₂ : x ≤ (32993/8192:ℝ)) : (21693/40000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (590582603/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (431432097/5000000000:ℝ) := by nlinarith
  have hc1 : (498139816897/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498139816897/500000000000:ℝ) ≤ taylorCos (431432097/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (249564142509/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (590582603/10000000000:ℝ) + taylorErr ≤ (249564142509/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59023932689/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59023932689/1000000000000:ℝ) ≤ taylorSin (590582603/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (86179389471/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (431432097/5000000000:ℝ) + taylorErr ≤ (86179389471/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (498139816897/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249564142509/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (59023932689/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (86179389471/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3156357218673/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6326328516839/500000000000:ℝ) := by nlinarith
  have hp1 : (20895066877181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20940129722567/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (123330902089/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (360921518987/200000000000:ℝ) := by nlinarith
  have hN : (117526225427/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (319179460023763/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (117526225427/500000000000:ℝ) (319179460023763/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (21693/40000000000:ℝ) ≤ ((117526225427/500000000000:ℝ)/(319179460023763/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_726 (x : ℝ) (h₁ : (16461/4096:ℝ) ≤ x) (h₂ : x ≤ (129/32:ℝ)) : (1350713/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (590582603/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (249564142509/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (590582603/10000000000:ℝ) + taylorErr ≤ (249564142509/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59023932689/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59023932689/1000000000000:ℝ) ≤ taylorSin (590582603/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249564142509/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (59023932689/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (98017142667/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3156357218673/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (791534086549/62500000000:ℝ) := by nlinarith
  have hp1 : (20895066877181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20959804927047/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (123330902089/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2054420189807/1000000000000:ℝ) := by nlinarith
  have hN : (117526225427/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (79945354901627/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (117526225427/500000000000:ℝ) (79945354901627/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1350713/2500000000000:ℝ) ≤ ((117526225427/500000000000:ℝ)/(79945354901627/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_727 (x : ℝ) (h₁ : (16463/4096:ℝ) ≤ x) (h₂ : x ≤ (8257/2048:ℝ)) : (349163/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (605922411/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (997087513/10000000000:ℝ) := by nlinarith
  have hc1 : (995033197167/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995033197167/1000000000000:ℝ) ≤ taylorCos (997087513/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (998164853991/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (605922411/10000000000:ℝ) + taylorErr ≤ (998164853991/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (15138792263/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (15138792263/250000000000:ℝ) ≤ taylorSin (605922411/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (99543621009/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (997087513/10000000000:ℝ) + taylorErr ≤ (99543621009/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (995033197167/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998164853991/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (15138792263/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (99543621009/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (315674071387/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3166519841393/250000000000:ℝ) := by nlinarith
  have hp1 : (20897605613209/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20962343663109/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1265458040689/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2086667593061/1000000000000:ℝ) := by nlinarith
  have hN : (133646593349/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (159929566494969/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (133646593349/500000000000:ℝ) (159929566494969/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349163/500000000000:ℝ) ≤ ((133646593349/500000000000:ℝ)/(159929566494969/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_728 (x : ℝ) (h₁ : (16463/4096:ℝ) ≤ x) (h₂ : x ≤ (8267/2048:ℝ)) : (1737357/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (605922411/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1150485591/10000000000:ℝ) := by nlinarith
  have hc1 : (198677841777/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198677841777/200000000000:ℝ) ≤ taylorCos (1150485591/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (998164853991/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (605922411/10000000000:ℝ) + taylorErr ≤ (998164853991/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (15138792263/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (15138792263/250000000000:ℝ) ≤ taylorSin (605922411/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (114794928877/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1150485591/10000000000:ℝ) + taylorErr ≤ (114794928877/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (198677841777/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998164853991/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (15138792263/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (114794928877/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (315674071387/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12681419173451/1000000000000:ℝ) := by nlinarith
  have hp1 : (20897605613209/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1311733188983/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1265458040689/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2409285090159/1000000000000:ℝ) := by nlinarith
  have hN : (133646593349/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (160318392252771/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (133646593349/500000000000:ℝ) (160318392252771/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1737357/2500000000000:ℝ) ≤ ((133646593349/500000000000:ℝ)/(160318392252771/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_729 (x : ℝ) (h₁ : (1029/256:ℝ) ≤ x) (h₂ : x ≤ (2109/512:ℝ)) : (1440757/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3742913123/10000000000:ℝ) := by nlinarith
  have hc1 : (232691739699/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (232691739699/250000000000:ℝ) ≤ taylorCos (3742913123/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (365613000119/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3742913123/10000000000:ℝ) + taylorErr ≤ (365613000119/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (232691739699/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998118115163/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (365613000119/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6313864922937/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3235165481651/250000000000:ℝ) := by nlinarith
  have hp1 : (20898874981223/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2141677741819/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256306870829/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3915126122373/500000000000:ℝ) := by nlinarith
  have hN : (141708119491/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (333921462197317/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (141708119491/500000000000:ℝ) (333921462197317/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1440757/2000000000000:ℝ) ≤ ((141708119491/500000000000:ℝ)/(333921462197317/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_730 (x : ℝ) (h₁ : (32931/8192:ℝ) ≤ x) (h₂ : x ≤ (16491/4096:ℝ)) : (930027/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (625097171/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (410339861/5000000000:ℝ) := by nlinarith
  have hc1 : (498317155689/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498317155689/500000000000:ℝ) ≤ taylorCos (410339861/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (124755863249/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (625097171/10000000000:ℝ) + taylorErr ≤ (124755863249/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (12493802741/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (12493802741/200000000000:ℝ) ≤ taylorSin (625097171/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (40987941051/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (410339861/5000000000:ℝ) + taylorErr ≤ (40987941051/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (498317155689/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124755863249/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (12493802741/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (40987941051/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2525776066293/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (790527411657/62500000000:ℝ) := by nlinarith
  have hp1 : (5225194758311/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10466574099199/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (40801595371/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (53625415273/31250000000:ℝ) := by nlinarith
  have hN : (7690103647/25000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (79741499338383/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7690103647/25000000000:ℝ) (79741499338383/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (930027/1000000000000:ℝ) ≤ ((7690103647/25000000000:ℝ)/(79741499338383/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_731 (x : ℝ) (h₁ : (32931/8192:ℝ) ≤ x) (h₂ : x ≤ (16501/4096:ℝ)) : (2319419/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (625097171/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (897378761/10000000000:ℝ) := by nlinarith
  have hc1 : (19919525117/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19919525117/20000000000:ℝ) ≤ taylorCos (897378761/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (124755863249/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (625097171/10000000000:ℝ) + taylorErr ≤ (124755863249/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (12493802741/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (12493802741/200000000000:ℝ) ≤ taylorSin (625097171/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (89617485361/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/10000000000:ℝ) + taylorErr ≤ (89617485361/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (19919525117/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124755863249/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (12493802741/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (89617485361/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2525776066293/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12656108490451/1000000000000:ℝ) := by nlinarith
  have hp1 : (5225194758311/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20945841878707/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (40801595371/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1877113677939/1000000000000:ℝ) := by nlinarith
  have hN : (7690103647/25000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (79838541061033/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7690103647/25000000000:ℝ) (79838541061033/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2319419/2500000000000:ℝ) ≤ ((7690103647/25000000000:ℝ)/(79838541061033/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_732 (x : ℝ) (h₁ : (32933/8192:ℝ) ≤ x) (h₂ : x ≤ (4123/1024:ℝ)) : (10298543/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/400000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (498999349649/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/400000000:ℝ) + taylorErr ≤ (498999349649/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (63234487649/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (63234487649/1000000000000:ℝ) ≤ taylorSin (25310683/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498999349649/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (63234487649/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (41370133433/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12629647321859/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2529841115381/200000000000:ℝ) := by nlinarith
  have hp1 : (10451024200629/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5233604391607/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (330432580367/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1732119296131/1000000000000:ℝ) := by nlinarith
  have hN : (32373162217/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (31900480345361/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (32373162217/100000000000:ℝ) (31900480345361/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10298543/10000000000000:ℝ) ≤ ((32373162217/100000000000:ℝ)/(31900480345361/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_733 (x : ℝ) (h₁ : (4117/1024:ℝ) ≤ x) (h₂ : x ≤ (4127/1024:ℝ)) : (11849221/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (64427193/1000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (951068089/10000000000:ℝ) := by nlinarith
  have hc1 : (39819230129/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (39819230129/40000000000:ℝ) ≤ taylorCos (951068089/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997925288467/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (64427193/1000000000:ℝ) + taylorErr ≤ (997925288467/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (64382628577/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (64382628577/1000000000000:ℝ) ≤ taylorSin (64427193/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (94963497643/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (951068089/10000000000:ℝ) + taylorErr ≤ (94963497643/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (39819230129/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997925288467/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (64382628577/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (94963497643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (252615956149/20000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12661477423209/1000000000000:ℝ) := by nlinarith
  have hp1 : (20903952453279/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5238681863731/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (134585140659/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (497483552819/250000000000:ℝ) := by nlinarith
  have hN : (347926118123/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (319626021076863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (347926118123/1000000000000:ℝ) (319626021076863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11849221/10000000000000:ℝ) ≤ ((347926118123/1000000000000:ℝ)/(319626021076863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_734 (x : ℝ) (h₁ : (4117/1024:ℝ) ≤ x) (h₂ : x ≤ (1033/256:ℝ)) : (11791793/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (64427193/1000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (138058271/1250000000:ℝ) := by nlinarith
  have hc1 : (248476741933/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (248476741933/250000000000:ℝ) ≤ taylorCos (138058271/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997925288467/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (64427193/1000000000:ℝ) + taylorErr ≤ (997925288467/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (64382628577/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (64382628577/1000000000000:ℝ) ≤ taylorSin (64427193/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (27555552407/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/1250000000:ℝ) + taylorErr ≤ (27555552407/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (248476741933/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997925288467/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (64382628577/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (27555552407/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (252615956149/20000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12676817231087/1000000000000:ℝ) := by nlinarith
  have hp1 : (20903952453279/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10490057407771/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (134585140659/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2312474613219/1000000000000:ℝ) := by nlinarith
  have hN : (347926118123/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (320403390220769/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (347926118123/1000000000000:ℝ) (320403390220769/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11791793/10000000000000:ℝ) ≤ ((347926118123/1000000000000:ℝ)/(320403390220769/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_735 (x : ℝ) (h₁ : (4117/1024:ℝ) ≤ x) (h₂ : x ≤ (8285/2048:ℝ)) : (11672323/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (64427193/1000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1426602133/10000000000:ℝ) := by nlinarith
  have hc1 : (989841276193/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989841276193/1000000000000:ℝ) ≤ taylorCos (1426602133/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997925288467/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (64427193/1000000000:ℝ) + taylorErr ≤ (997925288467/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (64382628577/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (64382628577/1000000000000:ℝ) ≤ taylorSin (64427193/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (8886050363/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1426602133/10000000000:ℝ) + taylorErr ≤ (8886050363/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (989841276193/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997925288467/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (64382628577/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (8886050363/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (252615956149/20000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12709030827633/1000000000000:ℝ) := by nlinarith
  have hp1 : (20903952453279/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10516714136421/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (134585140659/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (119618625881/40000000000:ℝ) := by nlinarith
  have hN : (347926118123/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (80509732288863/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (347926118123/1000000000000:ℝ) (80509732288863/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11672323/10000000000000:ℝ) ≤ ((347926118123/1000000000000:ℝ)/(80509732288863/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_736 (x : ℝ) (h₁ : (8235/2048:ℝ) ≤ x) (h₂ : x ≤ (16521/4096:ℝ)) : (3526053/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (329805869/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (26269421/250000000:ℝ) := by nlinarith
  have hc1 : (198896883129/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198896883129/200000000000:ℝ) ≤ taylorCos (26269421/250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (498912676339/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (329805869/5000000000:ℝ) + taylorErr ≤ (498912676339/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8239168807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8239168807/125000000000:ℝ) ≤ taylorSin (329805869/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (20976885387/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (26269421/250000000:ℝ) + taylorErr ≤ (20976885387/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (198896883129/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498912676339/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8239168807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (20976885387/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6316165894119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1267144829833/100000000000:ℝ) := by nlinarith
  have hp1 : (5226622797327/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10485614619663/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (689008440283/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (219955536089/100000000000:ℝ) := by nlinarith
  have hN : (23761970493/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (320131203954501/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (23761970493/62500000000:ℝ) (320131203954501/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3526053/2500000000000:ℝ) ≤ ((23761970493/62500000000:ℝ)/(320131203954501/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_737 (x : ℝ) (h₁ : (16471/4096:ℝ) ≤ x) (h₂ : x ≤ (32993/8192:ℝ)) : (15418319/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (333640821/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (431432097/5000000000:ℝ) := by nlinarith
  have hc1 : (498139816897/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498139816897/500000000000:ℝ) ≤ taylorCos (431432097/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997774504277/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (333640821/5000000000:ℝ) + taylorErr ≤ (997774504277/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (33339326729/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (33339326729/500000000000:ℝ) ≤ taylorSin (333640821/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (86179389471/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (431432097/5000000000:ℝ) + taylorErr ≤ (86179389471/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (498139816897/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997774504277/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (33339326729/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (86179389471/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1579137347329/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6326328516839/500000000000:ℝ) := by nlinarith
  have hp1 : (10453880278661/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20940129722567/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (87131332549/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (360921518987/200000000000:ℝ) := by nlinarith
  have hN : (396326816507/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (319179460023763/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (396326816507/1000000000000:ℝ) (319179460023763/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (15418319/10000000000000:ℝ) ≤ ((396326816507/1000000000000:ℝ)/(319179460023763/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_738 (x : ℝ) (h₁ : (2059/512:ℝ) ≤ x) (h₂ : x ≤ (33015/8192:ℝ)) : (16654831/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (947233137/10000000000:ℝ) := by nlinarith
  have hc1 : (995517098067/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995517098067/1000000000000:ℝ) ≤ taylorCos (947233137/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (47290864289/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (947233137/10000000000:ℝ) + taylorErr ≤ (47290864289/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (995517098067/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47290864289/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6316932884513/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3165273482003/250000000000:ℝ) := by nlinarith
  have hp1 : (2613628740667/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20954092770909/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (352546720937/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1981874315057/1000000000000:ℝ) := by nlinarith
  have hN : (412463814837/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (63921319781577/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (412463814837/1000000000000:ℝ) (63921319781577/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (16654831/10000000000000:ℝ) ≤ ((412463814837/1000000000000:ℝ)/(63921319781577/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_739 (x : ℝ) (h₁ : (2059/512:ℝ) ≤ x) (h₂ : x ≤ (16523/4096:ℝ)) : (16592229/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (133264581/1250000000:ℝ) := by nlinarith
  have hc1 : (248580588739/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (248580588739/250000000000:ℝ) ≤ taylorCos (133264581/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (53204911469/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (133264581/1250000000:ℝ) + taylorErr ≤ (53204911469/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (248580588739/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (53204911469/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6316932884513/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6336491139559/500000000000:ℝ) := by nlinarith
  have hp1 : (2613628740667/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5243441993847/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (352546720937/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (557953734151/250000000000:ℝ) := by nlinarith
  have hN : (412463814837/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (160104479846839/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (412463814837/1000000000000:ℝ) (160104479846839/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (16592229/10000000000000:ℝ) ≤ ((412463814837/1000000000000:ℝ)/(160104479846839/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_740 (x : ℝ) (h₁ : (2059/512:ℝ) ≤ x) (h₂ : x ≤ (16543/4096:ℝ)) : (16511887/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1219514727/10000000000:ℝ) := by nlinarith
  have hc1 : (992573128207/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (992573128207/1000000000000:ℝ) ≤ taylorCos (1219514727/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (30412354831/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1219514727/10000000000:ℝ) + taylorErr ≤ (30412354831/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (992573128207/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (30412354831/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6316932884513/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12688322086997/1000000000000:ℝ) := by nlinarith
  have hp1 : (2613628740667/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2624894417001/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (352546720937/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (63863376323/25000000000:ℝ) := by nlinarith
  have hN : (412463814837/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10030844836461/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (412463814837/1000000000000:ℝ) (10030844836461/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (16511887/10000000000000:ℝ) ≤ ((412463814837/1000000000000:ℝ)/(10030844836461/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_741 (x : ℝ) (h₁ : (2059/512:ℝ) ≤ x) (h₂ : x ≤ (8287/2048:ℝ)) : (4097079/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1457281749/10000000000:ℝ) := by nlinarith
  have hc1 : (494700212761/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494700212761/500000000000:ℝ) ≤ taylorCos (1457281749/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (29042585393/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6316932884513/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12712098789209/1000000000000:ℝ) := by nlinarith
  have hp1 : (2613628740667/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21038505744967/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (352546720937/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3055062998197/1000000000000:ℝ) := by nlinarith
  have hN : (412463814837/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (161097455626609/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (412463814837/1000000000000:ℝ) (161097455626609/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4097079/2500000000000:ℝ) ≤ ((412463814837/1000000000000:ℝ)/(161097455626609/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_742 (x : ℝ) (h₁ : (2059/512:ℝ) ≤ x) (h₂ : x ≤ (8307/2048:ℝ)) : (8115287/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1764077907/10000000000:ℝ) := by nlinarith
  have hc1 : (196896090621/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (196896090621/200000000000:ℝ) ≤ taylorCos (1764077907/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (175494255731/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6316932884513/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12742778404967/1000000000000:ℝ) := by nlinarith
  have hp1 : (2613628740667/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4217856093241/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (352546720937/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3701047579319/1000000000000:ℝ) := by nlinarith
  have hN : (412463814837/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (323756802956187/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (412463814837/1000000000000:ℝ) (323756802956187/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (8115287/5000000000000:ℝ) ≤ ((412463814837/1000000000000:ℝ)/(323756802956187/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_743 (x : ℝ) (h₁ : (2059/512:ℝ) ≤ x) (h₂ : x ≤ (4169/1024:ℝ)) : (999363/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2239611951/10000000000:ℝ) := by nlinarith
  have hc1 : (97502534279/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97502534279/100000000000:ℝ) ≤ taylorCos (2239611951/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (111046811651/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6316932884513/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12790331809391/1000000000000:ℝ) := by nlinarith
  have hp1 : (2613628740667/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21167981284123/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (352546720937/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (235063683069/50000000000:ℝ) := by nlinarith
  have hN : (412463814837/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326185175588639/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (412463814837/1000000000000:ℝ) (326185175588639/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (999363/625000000000:ℝ) ≤ ((412463814837/1000000000000:ℝ)/(326185175588639/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_744 (x : ℝ) (h₁ : (32951/8192:ℝ) ≤ x) (h₂ : x ≤ (16501/4096:ℝ)) : (21563547/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (70179621/1000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (897378761/10000000000:ℝ) := by nlinarith
  have hc1 : (19919525117/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19919525117/20000000000:ℝ) ≤ taylorCos (897378761/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997538423219/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (70179621/1000000000:ℝ) + taylorErr ≤ (997538423219/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35061012527/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35061012527/500000000000:ℝ) ≤ taylorSin (70179621/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (89617485361/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/10000000000:ℝ) + taylorErr ≤ (89617485361/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (19919525117/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997538423219/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (35061012527/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (89617485361/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3159137558851/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12656108490451/1000000000000:ℝ) := by nlinarith
  have hp1 : (20913472713383/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20945841878707/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1466495057573/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1877113677939/1000000000000:ℝ) := by nlinarith
  have hN : (234478317177/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (79838541061033/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (234478317177/500000000000:ℝ) (79838541061033/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (21563547/10000000000000:ℝ) ≤ ((234478317177/500000000000:ℝ)/(79838541061033/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_745 (x : ℝ) (h₁ : (32953/8192:ℝ) ≤ x) (h₂ : x ≤ (8251/2048:ℝ)) : (5767053/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (354733057/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (181009733/2000000000:ℝ) := by nlinarith
  have hc1 : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (497953613577/500000000000:ℝ) ≤ taylorCos (181009733/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997484346889/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (354733057/5000000000:ℝ) + taylorErr ≤ (997484346889/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35443553373/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35443553373/500000000000:ℝ) ≤ taylorSin (354733057/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (18076272631/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (181009733/2000000000:ℝ) + taylorErr ≤ (18076272631/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997484346889/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (35443553373/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (18076272631/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6318658612899/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2531375096169/200000000000:ℝ) := by nlinarith
  have hp1 : (20914742081397/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10473555623369/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1482585554489/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11832677929/6250000000:ℝ) := by nlinarith
  have hN : (1212753019/2500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (319392993875231/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1212753019/2500000000:ℝ) (319392993875231/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5767053/2500000000000:ℝ) ≤ ((1212753019/2500000000:ℝ)/(319392993875231/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_746 (x : ℝ) (h₁ : (32953/8192:ℝ) ≤ x) (h₂ : x ≤ (129/32:ℝ)) : (11506103/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (354733057/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997484346889/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (354733057/5000000000:ℝ) + taylorErr ≤ (997484346889/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35443553373/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35443553373/500000000000:ℝ) ≤ taylorSin (354733057/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997484346889/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (35443553373/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (98017142667/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6318658612899/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (791534086549/62500000000:ℝ) := by nlinarith
  have hp1 : (20914742081397/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20959804927047/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1482585554489/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2054420189807/1000000000000:ℝ) := by nlinarith
  have hN : (1212753019/2500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (79945354901627/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1212753019/2500000000:ℝ) (79945354901627/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11506103/5000000000000:ℝ) ≤ ((1212753019/2500000000:ℝ)/(79945354901627/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_747 (x : ℝ) (h₁ : (515/128:ℝ) ≤ x) (h₂ : x ≤ (2111/512:ℝ)) : (13104471/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1932815793/5000000000:ℝ) := by nlinarith
  have hc1 : (57888139991/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (57888139991/62500000000:ℝ) ≤ taylorCos (1932815793/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (377007412527/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1932815793/5000000000:ℝ) + taylorErr ≤ (377007412527/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (57888139991/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498645229471/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (377007412527/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12640001692177/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12952933772907/1000000000000:ℝ) := by nlinarith
  have hp1 : (10459592434723/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4287417461337/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1538910658071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8081940817609/1000000000000:ℝ) := by nlinarith
  have hN : (541620199129/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (33455698665063/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (541620199129/1000000000000:ℝ) (33455698665063/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13104471/5000000000000:ℝ) ≤ ((541620199129/1000000000000:ℝ)/(33455698665063/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_748 (x : ℝ) (h₁ : (515/128:ℝ) ≤ x) (h₂ : x ≤ (2131/512:ℝ)) : (25235977/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (636602027/1250000000:ℝ) := by nlinarith
  have hc1 : (174618995229/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (174618995229/200000000000:ℝ) ≤ taylorCos (636602027/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (48755016243/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/1250000000:ℝ) + taylorErr ≤ (48755016243/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (174618995229/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498645229471/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (48755016243/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12640001692177/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6537826117969/500000000000:ℝ) := by nlinarith
  have hp1 : (10459592434723/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21640186191637/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1538910658071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (10550676292749/1000000000000:ℝ) := by nlinarith
  have hN : (541620199129/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (340945362790381/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (541620199129/1000000000000:ℝ) (340945362790381/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (25235977/10000000000000:ℝ) ≤ ((541620199129/1000000000000:ℝ)/(340945362790381/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_749 (x : ℝ) (h₁ : (515/128:ℝ) ≤ x) (h₂ : x ≤ (1081/256:ℝ)) : (23815441/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (6994952393/10000000000:ℝ) := by nlinarith
  have hc1 : (191291815829/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (191291815829/250000000000:ℝ) ≤ taylorCos (6994952393/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (643831545169/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (6994952393/10000000000:ℝ) + taylorErr ≤ (643831545169/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (191291815829/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498645229471/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (643831545169/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12640001692177/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3316466463409/250000000000:ℝ) := by nlinarith
  have hp1 : (10459592434723/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21954989463313/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1538910658071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (7067657395167/500000000000:ℝ) := by nlinarith
  have hN : (541620199129/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (87741598423333/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (541620199129/1000000000000:ℝ) (87741598423333/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (23815441/10000000000000:ℝ) ≤ ((541620199129/1000000000000:ℝ)/(87741598423333/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_750 (x : ℝ) (h₁ : (515/128:ℝ) ≤ x) (h₂ : x ≤ (17/4:ℝ)) : (23206737/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (498645229471/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12640001692177/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13351768777757/1000000000000:ℝ) := by nlinarith
  have hp1 : (10459592434723/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11048579341389/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1538910658071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (15625050799431/1000000000000:ℝ) := by nlinarith
  have hN : (541620199129/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (177769729494687/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (541620199129/1000000000000:ℝ) (177769729494687/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (23206737/10000000000000:ℝ) ≤ ((541620199129/1000000000000:ℝ)/(177769729494687/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_751 (x : ℝ) (h₁ : (16481/4096:ℝ) ≤ x) (h₂ : x ≤ (33033/8192:ℝ)) : (6078023/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371990341/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (7939549/78125000:ℝ) := by nlinarith
  have hc1 : (994840495569/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (994840495569/1000000000000:ℝ) ≤ taylorCos (7939549/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (498616871147/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371990341/5000000000:ℝ) + taylorErr ≤ (498616871147/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (18582362953/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (18582362953/250000000000:ℝ) ≤ taylorSin (371990341/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (101451389023/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (7939549/78125000:ℝ) + taylorErr ≤ (101451389023/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (994840495569/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498616871147/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (18582362953/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (101451389023/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12640768682571/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12667996841557/1000000000000:ℝ) := by nlinarith
  have hp1 : (1046022711873/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20965517083187/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (194375736891/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (85079233187/40000000000:ℝ) := by nlinarith
  have hN : (278886076417/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (319956287955397/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (278886076417/500000000000:ℝ) (319956287955397/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6078023/2000000000000:ℝ) ≤ ((278886076417/500000000000:ℝ)/(319956287955397/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_752 (x : ℝ) (h₁ : (16481/4096:ℝ) ≤ x) (h₂ : x ≤ (2069/512:ℝ)) : (7532357/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371990341/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (644271931/5000000000:ℝ) := by nlinarith
  have hc1 : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198341950281/200000000000:ℝ) ≤ taylorCos (644271931/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (498616871147/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371990341/5000000000:ℝ) + taylorErr ≤ (498616871147/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (18582362953/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (18582362953/250000000000:ℝ) ≤ taylorSin (371990341/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (128498113073/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/5000000000:ℝ) + taylorErr ≤ (128498113073/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498616871147/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (18582362953/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (128498113073/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12640768682571/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6347612500271/500000000000:ℝ) := by nlinarith
  have hp1 : (1046022711873/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4202115929657/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (194375736891/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4319711743/1600000000:ℝ) := by nlinarith
  have hN : (278886076417/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (160668737814387/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (278886076417/500000000000:ℝ) (160668737814387/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7532357/2500000000000:ℝ) ≤ ((278886076417/500000000000:ℝ)/(160668737814387/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_753 (x : ℝ) (h₁ : (16483/4096:ℝ) ≤ x) (h₂ : x ≤ (8267/2048:ℝ)) : (6773707/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (75932049/1000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1150485591/10000000000:ℝ) := by nlinarith
  have hc1 : (198677841777/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198677841777/200000000000:ℝ) ≤ taylorCos (1150485591/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (997118549089/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (75932049/1000000000:ℝ) + taylorErr ≤ (997118549089/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (7585910117/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (7585910117/100000000000:ℝ) ≤ taylorSin (75932049/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (114794928877/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1150485591/10000000000:ℝ) + taylorErr ≤ (114794928877/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (198677841777/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997118549089/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (7585910117/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (114794928877/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12642302663359/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12681419173451/1000000000000:ℝ) := by nlinarith
  have hp1 : (1307687060843/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1311733188983/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (317439888151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2409285090159/1000000000000:ℝ) := by nlinarith
  have hN : (295040445833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (160318392252771/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (295040445833/500000000000:ℝ) (160318392252771/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6773707/2000000000000:ℝ) ≤ ((295040445833/500000000000:ℝ)/(160318392252771/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_754 (x : ℝ) (h₁ : (32973/8192:ℝ) ≤ x) (h₂ : x ≤ (129/32:ℝ)) : (20444851/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (786165153/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (249227828833/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (786165153/10000000000:ℝ) + taylorErr ≤ (249227828833/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (39267777879/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (39267777879/500000000000:ℝ) ≤ taylorSin (786165153/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249227828833/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (39267777879/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (98017142667/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6322493564869/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (791534086549/62500000000:ℝ) := by nlinarith
  have hp1 : (20927435761537/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20959804927047/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (821773899061/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2054420189807/1000000000000:ℝ) := by nlinarith
  have hN : (64663648279/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (79945354901627/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (64663648279/100000000000:ℝ) (79945354901627/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (20444851/5000000000000:ℝ) ≤ ((64663648279/100000000000:ℝ)/(79945354901627/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_755 (x : ℝ) (h₁ : (32975/8192:ℝ) ≤ x) (h₂ : x ≤ (16523/4096:ℝ)) : (4284463/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (793835057/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (133264581/1250000000:ℝ) := by nlinarith
  have hc1 : (248580588739/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (248580588739/250000000000:ℝ) ≤ taylorCos (133264581/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (99685078609/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (793835057/10000000000:ℝ) + taylorErr ≤ (99685078609/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79300153989/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79300153989/1000000000000:ℝ) ≤ taylorSin (793835057/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (53204911469/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (133264581/1250000000:ℝ) + taylorErr ≤ (53204911469/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (248580588739/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (99685078609/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (79300153989/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (53204911469/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3161438530033/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6336491139559/500000000000:ℝ) := by nlinarith
  have hp1 : (20928705129551/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5243441993847/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1659649539563/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (557953734151/250000000000:ℝ) := by nlinarith
  have hN : (662798753473/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (160104479846839/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (662798753473/1000000000000:ℝ) (160104479846839/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4284463/1000000000000:ℝ) ≤ ((662798753473/1000000000000:ℝ)/(160104479846839/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_756 (x : ℝ) (h₁ : (2061/512:ℝ) ≤ x) (h₂ : x ≤ (1033/256:ℝ)) : (43842579/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (797670009/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (138058271/1250000000:ℝ) := by nlinarith
  have hc1 : (248476741933/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (248476741933/250000000000:ℝ) ≤ taylorCos (138058271/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (996820301559/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (797670009/10000000000:ℝ) + taylorErr ≤ (996820301559/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79682435639/1000000000000:ℝ) ≤ taylorSin (797670009/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (27555552407/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/1250000000:ℝ) + taylorErr ≤ (27555552407/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (248476741933/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (996820301559/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (27555552407/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12646137615329/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12676817231087/1000000000000:ℝ) := by nlinarith
  have hp1 : (10464669906779/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10490057407771/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (83385038633/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2312474613219/1000000000000:ℝ) := by nlinarith
  have hN : (670880471101/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (320403390220769/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (670880471101/1000000000000:ℝ) (320403390220769/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (43842579/10000000000000:ℝ) ≤ ((670880471101/1000000000000:ℝ)/(320403390220769/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_757 (x : ℝ) (h₁ : (2061/512:ℝ) ≤ x) (h₂ : x ≤ (2071/512:ℝ)) : (43419407/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (797670009/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (56450493/400000000:ℝ) := by nlinarith
  have hc1 : (495029103999/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495029103999/500000000000:ℝ) ≤ taylorCos (56450493/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (996820301559/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (797670009/10000000000:ℝ) + taylorErr ≤ (996820301559/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79682435639/1000000000000:ℝ) ≤ taylorSin (797670009/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (140658241609/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/400000000:ℝ) + taylorErr ≤ (140658241609/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (495029103999/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (996820301559/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (140658241609/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12646137615329/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2541499369369/200000000000:ℝ) := by nlinarith
  have hp1 : (10464669906779/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1051544476839/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (83385038633/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2958167941717/1000000000000:ℝ) := by nlinarith
  have hN : (670880471101/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2515319939259/7812500000:ℝ) := by nlinarith
  have hfin := wfun_ge x (670880471101/1000000000000:ℝ) (2515319939259/7812500000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (43419407/10000000000000:ℝ) ≤ ((670880471101/1000000000000:ℝ)/(2515319939259/7812500000:ℝ))^2 := by norm_num
  linarith

theorem wc_758 (x : ℝ) (h₁ : (2061/512:ℝ) ≤ x) (h₂ : x ≤ (4147/1024:ℝ)) : (43209737/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (797670009/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (391165101/2500000000:ℝ) := by nlinarith
  have hc1 : (987784139377/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (987784139377/1000000000000:ℝ) ≤ taylorCos (391165101/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (996820301559/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (797670009/10000000000:ℝ) + taylorErr ≤ (996820301559/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79682435639/1000000000000:ℝ) ≤ taylorSin (797670009/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (9739274997/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (391165101/2500000000:ℝ) + taylorErr ≤ (9739274997/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (987784139377/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (996820301559/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (9739274997/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12646137615329/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3180709163681/250000000000:ℝ) := by nlinarith
  have hp1 : (10464669906779/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (105281384487/5000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (83385038633/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3281165937869/1000000000000:ℝ) := by nlinarith
  have hN : (670880471101/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (161370572542789/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (670880471101/1000000000000:ℝ) (161370572542789/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (43209737/10000000000000:ℝ) ≤ ((670880471101/1000000000000:ℝ)/(161370572542789/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_759 (x : ℝ) (h₁ : (2061/512:ℝ) ≤ x) (h₂ : x ≤ (519/128:ℝ)) : (10750333/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (797670009/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1718058483/10000000000:ℝ) := by nlinarith
  have hc1 : (985277640117/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (985277640117/1000000000000:ℝ) ≤ taylorCos (1718058483/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (996820301559/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (797670009/10000000000:ℝ) + taylorErr ≤ (996820301559/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79682435639/1000000000000:ℝ) ≤ taylorSin (797670009/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (996820301559/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (85480945539/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12646137615329/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12738176462603/1000000000000:ℝ) := by nlinarith
  have hp1 : (10464669906779/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21081664258019/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (83385038633/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3604161188623/1000000000000:ℝ) := by nlinarith
  have hN : (670880471101/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (323522279184827/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (670880471101/1000000000000:ℝ) (323522279184827/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10750333/2500000000000:ℝ) ≤ ((670880471101/1000000000000:ℝ)/(323522279184827/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_760 (x : ℝ) (h₁ : (2061/512:ℝ) ≤ x) (h₂ : x ≤ (2081/512:ℝ)) : (1064707/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (797670009/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (996820301559/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (797670009/10000000000:ℝ) + taylorErr ≤ (996820301559/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79682435639/1000000000000:ℝ) ≤ taylorSin (797670009/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (996820301559/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (201104637201/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12646137615329/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12768856078361/1000000000000:ℝ) := by nlinarith
  have hp1 : (10464669906779/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21132438979257/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (83385038633/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (265614467131/62500000000:ℝ) := by nlinarith
  have hN : (670880471101/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162543685549897/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (670880471101/1000000000000:ℝ) (162543685549897/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1064707/250000000000:ℝ) ≤ ((670880471101/1000000000000:ℝ)/(162543685549897/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_761 (x : ℝ) (h₁ : (8245/2048:ℝ) ≤ x) (h₂ : x ≤ (16561/4096:ℝ)) : (9557219/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (813009817/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (678786499/5000000000:ℝ) := by nlinarith
  have hc1 : (495399559797/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495399559797/500000000000:ℝ) ≤ taylorCos (678786499/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (99669689747/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (813009817/10000000000:ℝ) + taylorErr ≤ (99669689747/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8121144449/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8121144449/100000000000:ℝ) ≤ taylorSin (813009817/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (8458792749/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (678786499/5000000000:ℝ) + taylorErr ≤ (8458792749/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (495399559797/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (99669689747/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8121144449/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (8458792749/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12647671596117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1587765989261/125000000000:ℝ) := by nlinarith
  have hp1 : (10465939274793/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4204400792113/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1699908092901/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1422566197369/500000000000:ℝ) := by nlinarith
  have hN : (703211195431/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (80422026772927/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (703211195431/1000000000000:ℝ) (80422026772927/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9557219/2000000000000:ℝ) ≤ ((703211195431/1000000000000:ℝ)/(80422026772927/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_762 (x : ℝ) (h₁ : (8245/2048:ℝ) ≤ x) (h₂ : x ≤ (1037/256:ℝ)) : (9485773/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (813009817/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (99669689747/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (813009817/10000000000:ℝ) + taylorErr ≤ (99669689747/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8121144449/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8121144449/100000000000:ℝ) ≤ taylorSin (813009817/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (99669689747/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8121144449/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (31771629131/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12647671596117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127259046163/10000000000:ℝ) := by nlinarith
  have hp1 : (10465939274793/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265338592381/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1699908092901/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1672883850063/500000000000:ℝ) := by nlinarith
  have hN : (703211195431/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (80724324151583/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (703211195431/1000000000000:ℝ) (80724324151583/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9485773/2000000000000:ℝ) ≤ ((703211195431/1000000000000:ℝ)/(80724324151583/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_763 (x : ℝ) (h₁ : (8245/2048:ℝ) ≤ x) (h₂ : x ≤ (2079/512:ℝ)) : (11743211/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (813009817/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1902136177/10000000000:ℝ) := by nlinarith
  have hc1 : (981963866847/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981963866847/1000000000000:ℝ) ≤ taylorCos (1902136177/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (99669689747/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (813009817/10000000000:ℝ) + taylorErr ≤ (99669689747/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8121144449/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8121144449/100000000000:ℝ) ≤ taylorSin (813009817/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (99669689747/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8121144449/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (94534333207/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12647671596117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12756584232057/1000000000000:ℝ) := by nlinarith
  have hp1 : (10465939274793/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21112129090761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1699908092901/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3991642092351/1000000000000:ℝ) := by nlinarith
  have hN : (703211195431/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (324460882539131/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (703211195431/1000000000000:ℝ) (324460882539131/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11743211/2500000000000:ℝ) ≤ ((703211195431/1000000000000:ℝ)/(324460882539131/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_764 (x : ℝ) (h₁ : (4123/1024:ℝ) ≤ x) (h₂ : x ≤ (33055/8192:ℝ)) : (5270849/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (68789451/625000000:ℝ) := by nlinarith
  have hc1 : (248487291083/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (248487291083/250000000000:ℝ) ≤ taylorCos (68789451/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (5492052149/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (68789451/625000000:ℝ) + taylorErr ≤ (5492052149/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (248487291083/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124571393507/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (5492052149/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1581150697113/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1267643373589/100000000000:ℝ) := by nlinarith
  have hp1 : (20934417285613/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10489740065763/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (346423835219/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1152203989413/500000000000:ℝ) := by nlinarith
  have hN : (735548028039/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (320383944520821/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (735548028039/1000000000000:ℝ) (320383944520821/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5270849/1000000000000:ℝ) ≤ ((735548028039/1000000000000:ℝ)/(320383944520821/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_765 (x : ℝ) (h₁ : (4123/1024:ℝ) ≤ x) (h₂ : x ≤ (16543/4096:ℝ)) : (52510613/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1219514727/10000000000:ℝ) := by nlinarith
  have hc1 : (992573128207/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (992573128207/1000000000000:ℝ) ≤ taylorCos (1219514727/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (30412354831/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1219514727/10000000000:ℝ) + taylorErr ≤ (30412354831/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (992573128207/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124571393507/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (30412354831/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1581150697113/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12688322086997/1000000000000:ℝ) := by nlinarith
  have hp1 : (20934417285613/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2624894417001/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (346423835219/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (63863376323/25000000000:ℝ) := by nlinarith
  have hN : (735548028039/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10030844836461/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (735548028039/1000000000000:ℝ) (10030844836461/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (52510613/10000000000000:ℝ) ≤ ((735548028039/1000000000000:ℝ)/(10030844836461/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_766 (x : ℝ) (h₁ : (8247/2048:ℝ) ≤ x) (h₂ : x ≤ (4149/1024:ℝ)) : (6897/1220703125:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (406504909/2500000000:ℝ) := by nlinarith
  have hc1 : (493404699769/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493404699769/500000000000:ℝ) ≤ taylorCos (406504909/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (199288610723/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/10000000000:ℝ) + taylorErr ≤ (199288610723/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42134442649/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42134442649/500000000000:ℝ) ≤ taylorSin (843689433/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (1295091169/8000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (406504909/2500000000:ℝ) + taylorErr ≤ (1295091169/8000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (493404699769/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199288610723/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (42134442649/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1295091169/8000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3162684889423/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3182243144469/250000000000:ℝ) := by nlinarith
  have hp1 : (20936956021641/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1316651990103/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (441083486369/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1705184365029/500000000000:ℝ) := by nlinarith
  have hN : (767890891861/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (323053485776639/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (767890891861/1000000000000:ℝ) (323053485776639/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6897/1220703125:ℝ) ≤ ((767890891861/1000000000000:ℝ)/(323053485776639/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_767 (x : ℝ) (h₁ : (32993/8192:ℝ) ≤ x) (h₂ : x ≤ (4133/1024:ℝ)) : (63585659/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (862864193/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (141893223/1250000000:ℝ) := by nlinarith
  have hc1 : (7762219791/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7762219791/7812500000:ℝ) ≤ taylorCos (141893223/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (996279638327/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (862864193/10000000000:ℝ) + taylorErr ≤ (996279638327/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (86179384847/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (86179384847/1000000000000:ℝ) ≤ taylorSin (862864193/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (14158869317/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (141893223/1250000000:ℝ) + taylorErr ≤ (14158869317/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (7762219791/7812500000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (996279638327/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (86179384847/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (14158869317/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12652657033677/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12679885192663/1000000000000:ℝ) := by nlinarith
  have hp1 : (5235032360419/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10492596143833/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (18046074739/10000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1188506380773/500000000000:ℝ) := by nlinarith
  have hN : (808327835573/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (320558976998229/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (808327835573/1000000000000:ℝ) (320558976998229/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (63585659/10000000000000:ℝ) ≤ ((808327835573/1000000000000:ℝ)/(320558976998229/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_768 (x : ℝ) (h₁ : (16501/4096:ℝ) ≤ x) (h₂ : x ≤ (2069/512:ℝ)) : (75190749/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (22434469/250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (644271931/5000000000:ℝ) := by nlinarith
  have hc1 : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198341950281/200000000000:ℝ) ≤ taylorCos (644271931/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (995976260383/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (22434469/250000000:ℝ) + taylorErr ≤ (995976260383/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (89617480737/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (89617480737/1000000000000:ℝ) ≤ taylorSin (22434469/250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (128498113073/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/5000000000:ℝ) + taylorErr ≤ (128498113073/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995976260383/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (89617480737/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (128498113073/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (253122169809/20000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6347612500271/500000000000:ℝ) := by nlinarith
  have hp1 : (20945841597739/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4202115929657/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (375422711181/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4319711743/1600000000:ℝ) := by nlinarith
  have hN : (440568647761/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (160668737814387/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (440568647761/500000000000:ℝ) (160668737814387/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (75190749/10000000000000:ℝ) ≤ ((440568647761/500000000000:ℝ)/(160668737814387/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_769 (x : ℝ) (h₁ : (16503/4096:ℝ) ≤ x) (h₂ : x ≤ (8277/2048:ℝ)) : (80777393/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (114089821/1250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (130388367/1000000000:ℝ) := by nlinarith
  have hc1 : (991511471053/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (991511471053/1000000000000:ℝ) ≤ taylorCos (130388367/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (7966700937/8000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (114089821/1250000000:ℝ) + taylorErr ≤ (7966700937/8000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22786295789/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22786295789/250000000000:ℝ) ≤ taylorSin (114089821/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (65009612507/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/1000000000:ℝ) + taylorErr ≤ (65009612507/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (991511471053/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (7966700937/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22786295789/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (65009612507/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6328821235619/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1269675898133/100000000000:ℝ) := by nlinarith
  have hp1 : (20948380333767/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21013118384347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (954671981171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2732109367461/1000000000000:ℝ) := by nlinarith
  have hN : (913506345217/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (321415377259969/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (913506345217/1000000000000:ℝ) (321415377259969/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (80777393/10000000000000:ℝ) ≤ ((913506345217/1000000000000:ℝ)/(321415377259969/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_770 (x : ℝ) (h₁ : (16503/4096:ℝ) ≤ x) (h₂ : x ≤ (8287/2048:ℝ)) : (5024187/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (114089821/1250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1457281749/10000000000:ℝ) := by nlinarith
  have hc1 : (494700212761/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494700212761/500000000000:ℝ) ≤ taylorCos (1457281749/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (7966700937/8000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (114089821/1250000000:ℝ) + taylorErr ≤ (7966700937/8000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22786295789/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22786295789/250000000000:ℝ) ≤ taylorSin (114089821/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (7966700937/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22786295789/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (29042585393/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6328821235619/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12712098789209/1000000000000:ℝ) := by nlinarith
  have hp1 : (20948380333767/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21038505744967/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (954671981171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3055062998197/1000000000000:ℝ) := by nlinarith
  have hN : (913506345217/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (161097455626609/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (913506345217/1000000000000:ℝ) (161097455626609/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5024187/625000000000:ℝ) ≤ ((913506345217/1000000000000:ℝ)/(161097455626609/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_771 (x : ℝ) (h₁ : (33015/8192:ℝ) ≤ x) (h₂ : x ≤ (16543/4096:ℝ)) : (94426383/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (59202071/625000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1219514727/10000000000:ℝ) := by nlinarith
  have hc1 : (992573128207/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (992573128207/1000000000000:ℝ) ≤ taylorCos (1219514727/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (4977585513/5000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (59202071/625000000:ℝ) + taylorErr ≤ (4977585513/5000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (47290861977/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (47290861977/500000000000:ℝ) ≤ taylorSin (59202071/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (30412354831/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1219514727/10000000000:ℝ) + taylorErr ≤ (30412354831/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (992573128207/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (4977585513/5000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (47290861977/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (30412354831/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12661093928011/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12688322086997/1000000000000:ℝ) := by nlinarith
  have hp1 : (2095409248983/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2624894417001/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1981874191579/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (63863376323/25000000000:ℝ) := by nlinarith
  have hN : (986357088979/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10030844836461/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (986357088979/1000000000000:ℝ) (10030844836461/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (94426383/10000000000000:ℝ) ≤ ((986357088979/1000000000000:ℝ)/(10030844836461/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_772 (x : ℝ) (h₁ : (4127/1024:ℝ) ≤ x) (h₂ : x ≤ (4147/1024:ℝ)) : (18988477/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (118883511/1250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (391165101/2500000000:ℝ) := by nlinarith
  have hc1 : (987784139377/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (987784139377/1000000000000:ℝ) ≤ taylorCos (391165101/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (995480757759/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (118883511/1250000000:ℝ) + taylorErr ≤ (995480757759/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (94963493019/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (94963493019/1000000000000:ℝ) ≤ taylorSin (118883511/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (9739274997/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (391165101/2500000000:ℝ) + taylorErr ≤ (9739274997/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (987784139377/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995480757759/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (94963493019/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (9739274997/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1582684677901/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3180709163681/250000000000:ℝ) := by nlinarith
  have hp1 : (20954727173837/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (105281384487/5000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1989934087687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3281165937869/1000000000000:ℝ) := by nlinarith
  have hN : (124306666241/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (161370572542789/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (124306666241/125000000000:ℝ) (161370572542789/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (18988477/2000000000000:ℝ) ≤ ((124306666241/125000000000:ℝ)/(161370572542789/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_773 (x : ℝ) (h₁ : (4127/1024:ℝ) ≤ x) (h₂ : x ≤ (2089/512:ℝ)) : (92147329/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (118883511/1250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2515728493/10000000000:ℝ) := by nlinarith
  have hc1 : (968522091991/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968522091991/1000000000000:ℝ) ≤ taylorCos (2515728493/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (995480757759/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (118883511/1250000000:ℝ) + taylorErr ≤ (995480757759/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (94963493019/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (94963493019/1000000000000:ℝ) ≤ taylorSin (118883511/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (62231902023/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2515728493/10000000000:ℝ) + taylorErr ≤ (62231902023/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (968522091991/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995480757759/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (94963493019/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (62231902023/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1582684677901/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12817943463573/1000000000000:ℝ) := by nlinarith
  have hp1 : (20954727173837/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10606839266619/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1989934087687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (330041891007/62500000000:ℝ) := by nlinarith
  have hN : (124306666241/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81899837317677/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (124306666241/125000000000:ℝ) (81899837317677/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (92147329/10000000000000:ℝ) ≤ ((124306666241/125000000000:ℝ)/(81899837317677/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_774 (x : ℝ) (h₁ : (129/32:ℝ) ≤ x) (h₂ : x ≤ (16563/4096:ℝ)) : (108368853/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (686456403/5000000000:ℝ) := by nlinarith
  have hc1 : (198118068789/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198118068789/200000000000:ℝ) ≤ taylorCos (686456403/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (68430195491/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (686456403/5000000000:ℝ) + taylorErr ≤ (68430195491/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (198118068789/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (68430195491/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12664545384783/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (101629295159/8000000000:ℝ) := by nlinarith
  have hp1 : (20959804645891/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (168196341573/8000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (205442006533/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1438713566839/500000000000:ℝ) := by nlinarith
  have hN : (1059235336393/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (321766051078599/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1059235336393/1000000000000:ℝ) (321766051078599/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (108368853/10000000000000:ℝ) ≤ ((1059235336393/1000000000000:ℝ)/(321766051078599/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_775 (x : ℝ) (h₁ : (129/32:ℝ) ≤ x) (h₂ : x ≤ (16583/4096:ℝ)) : (107845387/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (381577721/2500000000:ℝ) := by nlinarith
  have hc1 : (494187234373/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494187234373/500000000000:ℝ) ≤ taylorCos (381577721/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (38009789649/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12664545384783/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6359500851377/500000000000:ℝ) := by nlinarith
  have hp1 : (20959804645891/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5262482514311/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (205442006533/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3200413654409/1000000000000:ℝ) := by nlinarith
  have hN : (1059235336393/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (322546008629319/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1059235336393/1000000000000:ℝ) (322546008629319/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (107845387/10000000000000:ℝ) ≤ ((1059235336393/1000000000000:ℝ)/(322546008629319/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_776 (x : ℝ) (h₁ : (129/32:ℝ) ≤ x) (h₂ : x ≤ (8307/2048:ℝ)) : (428161/40000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1764077907/10000000000:ℝ) := by nlinarith
  have hc1 : (196896090621/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (196896090621/200000000000:ℝ) ≤ taylorCos (1764077907/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (175494255731/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12664545384783/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12742778404967/1000000000000:ℝ) := by nlinarith
  have hp1 : (20959804645891/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4217856093241/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (205442006533/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3701047579319/1000000000000:ℝ) := by nlinarith
  have hN : (1059235336393/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (323756802956187/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1059235336393/1000000000000:ℝ) (323756802956187/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (428161/40000000000:ℝ) ≤ ((1059235336393/1000000000000:ℝ)/(323756802956187/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_777 (x : ℝ) (h₁ : (4129/1024:ℝ) ≤ x) (h₂ : x ≤ (1045/256:ℝ)) : (58750599/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (644271931/2500000000:ℝ) := by nlinarith
  have hc1 : (483488234387/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483488234387/500000000000:ℝ) ≤ taylorCos (644271931/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (994879333057/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/250000000:ℝ) + taylorErr ≤ (994879333057/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (25267465123/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (25267465123/250000000000:ℝ) ≤ taylorSin (25310683/250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (254865661901/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/2500000000:ℝ) + taylorErr ≤ (254865661901/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (483488234387/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (994879333057/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (25267465123/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (254865661901/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12667613346359/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3206019846681/250000000000:ℝ) := by nlinarith
  have hp1 : (20964882117947/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5305958369371/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (529729427723/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1352306591829/250000000000:ℝ) := by nlinarith
  have hN : (224807675567/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327914024233999/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (224807675567/200000000000:ℝ) (327914024233999/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (58750599/5000000000000:ℝ) ≤ ((224807675567/200000000000:ℝ)/(327914024233999/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_778 (x : ℝ) (h₁ : (4129/1024:ℝ) ≤ x) (h₂ : x ≤ (525/128:ℝ)) : (7204521/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3190680039/10000000000:ℝ) := by nlinarith
  have hc1 : (37981127133/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (37981127133/40000000000:ℝ) ≤ taylorCos (3190680039/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (994879333057/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/250000000:ℝ) + taylorErr ≤ (994879333057/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (25267465123/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (25267465123/250000000000:ℝ) ≤ taylorSin (25310683/250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (994879333057/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (25267465123/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7842043567/25000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12667613346359/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (20133497841/1562500000:ℝ) := by nlinarith
  have hp1 : (20964882117947/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21325382919961/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (529729427723/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1672345819413/250000000000:ℝ) := by nlinarith
  have hN : (224807675567/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (165534528384431/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (224807675567/200000000000:ℝ) (165534528384431/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7204521/625000000000:ℝ) ≤ ((224807675567/200000000000:ℝ)/(165534528384431/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_779 (x : ℝ) (h₁ : (16521/4096:ℝ) ≤ x) (h₂ : x ≤ (1037/256:ℝ)) : (17410303/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1050776839/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (49724221009/50000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1050776839/10000000000:ℝ) + taylorErr ≤ (49724221009/50000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (104884422311/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (104884422311/1000000000000:ℝ) ≤ taylorSin (1050776839/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (49724221009/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (104884422311/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (31771629131/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12671448298329/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127259046163/10000000000:ℝ) := by nlinarith
  have hp1 : (20971228958017/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265338592381/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2199555234413/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1672883850063/500000000000:ℝ) := by nlinarith
  have hN : (1205070814233/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (80724324151583/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1205070814233/1000000000000:ℝ) (80724324151583/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (17410303/1250000000000:ℝ) ≤ ((1205070814233/1000000000000:ℝ)/(80724324151583/250000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
