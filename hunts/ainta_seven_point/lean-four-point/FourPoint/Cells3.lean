import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_180 (x : ℝ) (h₁ : (4057/2048:ℝ) ≤ x) (h₂ : x ≤ (2031/1024:ℝ)) : (2005535413/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (521553467/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (149563127/2500000000:ℝ) := by nlinarith
  have hc1 : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499105500547/500000000000:ℝ) ≤ taylorCos (149563127/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998640220447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (521553467/10000000000:ℝ) + taylorErr ≤ (998640220447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5213170233/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5213170233/100000000000:ℝ) ≤ taylorSin (521553467/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (59789573081/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (149563127/2500000000:ℝ) + taylorErr ≤ (59789573081/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998640220447/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59789573081/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5213170233/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1555840014113/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (778878745049/125000000000:ℝ) := by nlinarith
  have hp1 : (10299652064969/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10312345883439/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-123314151567/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-536938395553/1000000000000:ℝ) := by nlinarith
  have hN : (1535149396647/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38325734367303/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1535149396647/1000000000000:ℝ) (38325734367303/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2005535413/5000000000000:ℝ) ≤ ((1535149396647/1000000000000:ℝ)/(38325734367303/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_181 (x : ℝ) (h₁ : (32461/16384:ℝ) ≤ x) (h₂ : x ≤ (16233/8192:ℝ)) : (4343199033/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (579077747/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (73583141/1250000000:ℝ) := by nlinarith
  have hc1 : (249566966213/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249566966213/250000000000:ℝ) ≤ taylorCos (73583141/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998323815553/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (579077747/10000000000:ℝ) + taylorErr ≤ (998323815553/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57875414073/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57875414073/1000000000000:ℝ) ≤ taylorSin (579077747/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (3677032683/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (73583141/1250000000:ℝ) + taylorErr ≤ (3677032683/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249566966213/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998323815553/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-3677032683/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-57875414073/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1556079698611/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6225277532437/1000000000000:ℝ) := by nlinarith
  have hp1 : (5150619387493/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5151412811603/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-606141224701/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-596188459567/1000000000000:ℝ) := by nlinarith
  have hN : (1594456324419/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7650816071173/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1594456324419/1000000000000:ℝ) (7650816071173/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4343199033/10000000000000:ℝ) ≤ ((1594456324419/1000000000000:ℝ)/(7650816071173/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_182 (x : ℝ) (h₁ : (16233/8192:ℝ) ≤ x) (h₂ : x ≤ (32471/16384:ℝ)) : (2143882477/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (569490367/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (144769437/2500000000:ℝ) := by nlinarith
  have hc1 : (998323811023/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998323811023/1000000000000:ℝ) ≤ taylorCos (144769437/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998378844087/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (569490367/10000000000:ℝ) + taylorErr ≤ (998378844087/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (11383651329/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (11383651329/200000000000:ℝ) ≤ taylorSin (569490367/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (28937709349/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (144769437/2500000000:ℝ) + taylorErr ≤ (28937709349/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998323811023/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998378844087/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-28937709349/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-11383651329/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1556319383109/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (622623627043/100000000000:ℝ) := by nlinarith
  have hp1 : (5151412742501/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5152206166623/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-37273261139/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-586418865123/1000000000000:ℝ) := by nlinarith
  have hN : (792371338073/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76532036190437/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (792371338073/500000000000:ℝ) (76532036190437/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2143882477/5000000000000:ℝ) ≤ ((792371338073/500000000000:ℝ)/(76532036190437/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_183 (x : ℝ) (h₁ : (16233/8192:ℝ) ≤ x) (h₂ : x ≤ (8119/4096:ℝ)) : (4231923619/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (559902987/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (144769437/2500000000:ℝ) := by nlinarith
  have hc1 : (998323811023/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998323811023/1000000000000:ℝ) ≤ taylorCos (144769437/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (249608238733/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (559902987/10000000000:ℝ) + taylorErr ≤ (249608238733/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (55961046899/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (55961046899/1000000000000:ℝ) ≤ taylorSin (559902987/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (28937709349/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (144769437/2500000000:ℝ) + taylorErr ≤ (28937709349/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998323811023/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249608238733/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-28937709349/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-55961046899/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1556319383109/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3113597504211/500000000000:ℝ) := by nlinarith
  have hp1 : (5151412742501/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2576499760821/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-149116002433/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-288278450079/500000000000:ℝ) := by nlinarith
  have hN : (1574880711181/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9569489418229/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1574880711181/1000000000000:ℝ) (9569489418229/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4231923619/10000000000000:ℝ) ≤ ((1574880711181/1000000000000:ℝ)/(9569489418229/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_184 (x : ℝ) (h₁ : (32471/16384:ℝ) ≤ x) (h₂ : x ≤ (8119/4096:ℝ)) : (4232696597/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (559902987/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (8898287/156250000:ℝ) := by nlinarith
  have hc1 : (998378839557/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998378839557/1000000000000:ℝ) ≤ taylorCos (8898287/156250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (249608238733/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (559902987/10000000000:ℝ) + taylorErr ≤ (249608238733/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (55961046899/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (55961046899/1000000000000:ℝ) ≤ taylorSin (559902987/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (56918261269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (8898287/156250000:ℝ) + taylorErr ≤ (56918261269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998378839557/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249608238733/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-56918261269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-55961046899/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6226236270429/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3113597504211/500000000000:ℝ) := by nlinarith
  have hp1 : (10304412195021/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2576499760821/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-73324943273/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-18020177941/31250000000:ℝ) := by nlinarith
  have hN : (1575024533669/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9569489418229/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1575024533669/1000000000000:ℝ) (9569489418229/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4232696597/10000000000000:ℝ) ≤ ((1575024533669/1000000000000:ℝ)/(9569489418229/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_185 (x : ℝ) (h₁ : (8119/4096:ℝ) ≤ x) (h₂ : x ≤ (32481/16384:ℝ)) : (2088996909/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (550315607/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (139975747/2500000000:ℝ) := by nlinarith
  have hc1 : (499216475201/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499216475201/500000000000:ℝ) ≤ taylorCos (139975747/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998486148039/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (550315607/10000000000:ℝ) + taylorErr ≤ (998486148039/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27501892857/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27501892857/500000000000:ℝ) ≤ taylorSin (550315607/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (55961051523/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (139975747/2500000000:ℝ) + taylorErr ≤ (55961051523/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499216475201/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998486148039/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-55961051523/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27501892857/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6227195008421/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1245630749283/200000000000:ℝ) := by nlinarith
  have hp1 : (10305998905037/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10307585753323/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-28841166871/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-566868955341/1000000000000:ℝ) := by nlinarith
  have hN : (1565301905743/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76579798177967/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1565301905743/1000000000000:ℝ) (76579798177967/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2088996909/5000000000000:ℝ) ≤ ((1565301905743/1000000000000:ℝ)/(76579798177967/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_186 (x : ℝ) (h₁ : (8119/4096:ℝ) ≤ x) (h₂ : x ≤ (16243/8192:ℝ)) : (4122919829/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (540728227/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (139975747/2500000000:ℝ) := by nlinarith
  have hc1 : (499216475201/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499216475201/500000000000:ℝ) ≤ taylorCos (139975747/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998538423359/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (540728227/10000000000:ℝ) + taylorErr ≤ (998538423359/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (54046473971/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (54046473971/1000000000000:ℝ) ≤ taylorSin (540728227/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (55961051523/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (139975747/2500000000:ℝ) + taylorErr ≤ (55961051523/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499216475201/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998538423359/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-55961051523/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-54046473971/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6227195008421/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6229112484407/1000000000000:ℝ) := by nlinarith
  have hp1 : (10305998905037/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10309172463361/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-288456065691/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-278501450783/500000000000:ℝ) := by nlinarith
  have hN : (24303685187/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76603684686791/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (24303685187/15625000000:ℝ) (76603684686791/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4122919829/10000000000000:ℝ) ≤ ((24303685187/15625000000:ℝ)/(76603684686791/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_187 (x : ℝ) (h₁ : (8119/4096:ℝ) ≤ x) (h₂ : x ≤ (2031/1024:ℝ)) : (4013960191/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (521553467/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (139975747/2500000000:ℝ) := by nlinarith
  have hc1 : (499216475201/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499216475201/500000000000:ℝ) ≤ taylorCos (139975747/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998640220447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (521553467/10000000000:ℝ) + taylorErr ≤ (998640220447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5213170233/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5213170233/100000000000:ℝ) ≤ taylorSin (521553467/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (55961051523/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (139975747/2500000000:ℝ) + taylorErr ≤ (55961051523/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499216475201/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998640220447/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-55961051523/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5213170233/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6227195008421/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (778878745049/125000000000:ℝ) := by nlinarith
  have hp1 : (10305998905037/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10312345883439/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-577089719307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-53726926713/100000000000:ℝ) := by nlinarith
  have hN : (383925554383/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38325734367303/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (383925554383/250000000000:ℝ) (38325734367303/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4013960191/10000000000000:ℝ) ≤ ((383925554383/250000000000:ℝ)/(38325734367303/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_188 (x : ℝ) (h₁ : (32481/16384:ℝ) ≤ x) (h₂ : x ≤ (16243/8192:ℝ)) : (2061828237/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (540728227/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (68789451/1250000000:ℝ) := by nlinarith
  have hc1 : (998486143509/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998486143509/1000000000000:ℝ) ≤ taylorCos (68789451/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998538423359/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (540728227/10000000000:ℝ) + taylorErr ≤ (998538423359/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (54046473971/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (54046473971/1000000000000:ℝ) ≤ taylorSin (540728227/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (27501895169/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (68789451/1250000000:ℝ) + taylorErr ≤ (27501895169/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998486143509/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998538423359/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27501895169/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-54046473971/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3114076873207/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6229112484407/1000000000000:ℝ) := by nlinarith
  have hp1 : (644224100941/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10309172463361/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-567043560733/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-557088657647/1000000000000:ℝ) := by nlinarith
  have hN : (388893700289/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76603684686791/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (388893700289/250000000000:ℝ) (76603684686791/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2061828237/5000000000000:ℝ) ≤ ((388893700289/250000000000:ℝ)/(76603684686791/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_189 (x : ℝ) (h₁ : (16243/8192:ℝ) ≤ x) (h₂ : x ≤ (32491/16384:ℝ)) : (203484221/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (531140847/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (135182057/2500000000:ℝ) := by nlinarith
  have hc1 : (998538418829/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998538418829/1000000000000:ℝ) ≤ taylorCos (135182057/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (249647445211/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (531140847/10000000000:ℝ) + taylorErr ≤ (249647445211/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1061782251/20000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1061782251/20000000000:ℝ) ≤ taylorSin (531140847/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (10809295719/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (135182057/2500000000:ℝ) + taylorErr ≤ (10809295719/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998538418829/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249647445211/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-10809295719/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1061782251/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3114556242203/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1946897257/312500000:ℝ) := by nlinarith
  have hp1 : (644323270317/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10310759173401/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-139315056241/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-547304809863/1000000000000:ℝ) := by nlinarith
  have hN : (386460807173/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38313787436177/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (386460807173/250000000000:ℝ) (38313787436177/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (203484221/500000000000:ℝ) ≤ ((386460807173/250000000000:ℝ)/(38313787436177/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_190 (x : ℝ) (h₁ : (16243/8192:ℝ) ≤ x) (h₂ : x ≤ (2031/1024:ℝ)) : (2007688237/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (521553467/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (135182057/2500000000:ℝ) := by nlinarith
  have hc1 : (998538418829/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998538418829/1000000000000:ℝ) ≤ taylorCos (135182057/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998640220447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (521553467/10000000000:ℝ) + taylorErr ≤ (998640220447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5213170233/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5213170233/100000000000:ℝ) ≤ taylorSin (521553467/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (10809295719/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (135182057/2500000000:ℝ) + taylorErr ≤ (10809295719/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998538418829/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998640220447/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-10809295719/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5213170233/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3114556242203/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (778878745049/125000000000:ℝ) := by nlinarith
  have hp1 : (644323270317/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10312345883439/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-278672990527/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-537434702919/1000000000000:ℝ) := by nlinarith
  have hN : (383993280437/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38325734367303/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (383993280437/250000000000:ℝ) (38325734367303/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2007688237/5000000000000:ℝ) ≤ ((383993280437/250000000000:ℝ)/(38325734367303/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_191 (x : ℝ) (h₁ : (32491/16384:ℝ) ≤ x) (h₂ : x ≤ (2031/1024:ℝ)) : (401607751/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (521553467/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (33196303/625000000:ℝ) := by nlinarith
  have hc1 : (199717955263/200000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199717955263/200000000000:ℝ) ≤ taylorCos (33196303/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998640220447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (521553467/10000000000:ℝ) + taylorErr ≤ (998640220447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5213170233/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5213170233/100000000000:ℝ) ≤ taylorSin (521553467/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (26544558587/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (33196303/625000000:ℝ) + taylorErr ≤ (26544558587/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (199717955263/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998640220447/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26544558587/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5213170233/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6230071222399/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (778878745049/125000000000:ℝ) := by nlinarith
  have hp1 : (10310759035091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10312345883439/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-109494667789/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-537517420813/1000000000000:ℝ) := by nlinarith
  have hN : (192013399641/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38325734367303/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (192013399641/125000000000:ℝ) (38325734367303/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (401607751/1000000000000:ℝ) ≤ ((192013399641/125000000000:ℝ)/(38325734367303/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_192 (x : ℝ) (h₁ : (2031/1024:ℝ) ≤ x) (h₂ : x ≤ (32501/16384:ℝ)) : (3962835597/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (511966087/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998689742121/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (511966087/10000000000:ℝ) + taylorErr ≤ (998689742121/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1599195131/31250000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1599195131/31250000000:ℝ) ≤ taylorSin (511966087/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998689742121/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1599195131/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (389499293649/62500000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10313932593477/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-537682911507/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-65965812419/125000000000:ℝ) := by nlinarith
  have hN : (1526366715269/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19168841568393/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1526366715269/1000000000000:ℝ) (19168841568393/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3962835597/10000000000000:ℝ) ≤ ((1526366715269/1000000000000:ℝ)/(19168841568393/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_193 (x : ℝ) (h₁ : (2031/1024:ℝ) ≤ x) (h₂ : x ≤ (16253/8192:ℝ)) : (1954646193/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (125594677/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124842293227/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (125594677/2500000000:ℝ) + taylorErr ≤ (124842293227/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (12554184779/250000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (12554184779/250000000000:ℝ) ≤ taylorSin (125594677/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124842293227/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-12554184779/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6232947436377/1000000000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10315519303517/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-53776562941/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-129463093989/250000000000:ℝ) := by nlinarith
  have hN : (1516492591873/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38349633744639/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1516492591873/1000000000000:ℝ) (38349633744639/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1954646193/5000000000000:ℝ) ≤ ((1516492591873/1000000000000:ℝ)/(38349633744639/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_194 (x : ℝ) (h₁ : (2031/1024:ℝ) ≤ x) (h₂ : x ≤ (8129/4096:ℝ)) : (3803388551/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (120800987/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998832799117/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (120800987/2500000000:ℝ) + taylorErr ≤ (998832799117/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (48301591169/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (48301591169/1000000000000:ℝ) ≤ taylorSin (120800987/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998832799117/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-48301591169/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3117432456181/500000000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5159346361797/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-107586213043/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-498102708173/1000000000000:ℝ) := by nlinarith
  have hN : (149674292409/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38373540475403/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (149674292409/100000000000:ℝ) (38373540475403/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3803388551/10000000000000:ℝ) ≤ ((149674292409/100000000000:ℝ)/(38373540475403/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_195 (x : ℝ) (h₁ : (2031/1024:ℝ) ≤ x) (h₂ : x ≤ (4067/2048:ℝ)) : (71925891/200000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499505344059/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/2500000000:ℝ) + taylorErr ≤ (499505344059/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5558846193/125000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5558846193/125000000000:ℝ) ≤ taylorSin (111213607/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499505344059/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5558846193/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6238699864331/1000000000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2581259890937/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-269130968413/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-28662371943/62500000000:ℝ) := by nlinarith
  have hN : (291447633401/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9605343999301/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (291447633401/200000000000:ℝ) (9605343999301/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (71925891/200000000000:ℝ) ≤ ((291447633401/200000000000:ℝ)/(9605343999301/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_196 (x : ℝ) (h₁ : (2031/1024:ℝ) ≤ x) (h₂ : x ≤ (509/256:ℝ)) : (400103387/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999322386851/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6246369768271/1000000000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5168866622029/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-33682730003/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-75913757093/200000000000:ℝ) := by nlinarith
  have hN : (689104500691/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3851713528197/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (689104500691/500000000000:ℝ) (3851713528197/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (400103387/1250000000000:ℝ) ≤ ((689104500691/500000000000:ℝ)/(3851713528197/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_197 (x : ℝ) (h₁ : (32501/16384:ℝ) ≤ x) (h₂ : x ≤ (16253/8192:ℝ)) : (488744817/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (125594677/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (63995761/1250000000:ℝ) := by nlinarith
  have hc1 : (124836217199/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124836217199/125000000000:ℝ) ≤ taylorCos (63995761/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124842293227/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (125594677/2500000000:ℝ) + taylorErr ≤ (124842293227/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (12554184779/250000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (12554184779/250000000000:ℝ) ≤ taylorSin (125594677/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (3198390551/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (63995761/1250000000:ℝ) + taylorErr ≤ (3198390551/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124836217199/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124842293227/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-3198390551/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-12554184779/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231988698383/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6232947436377/1000000000000:ℝ) := by nlinarith
  have hp1 : (2578483113781/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10315519303517/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-105577790301/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-517932055359/1000000000000:ℝ) := by nlinarith
  have hN : (1516621792951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38349633744639/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1516621792951/1000000000000:ℝ) (38349633744639/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (488744817/1250000000000:ℝ) ≤ ((1516621792951/1000000000000:ℝ)/(38349633744639/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_198 (x : ℝ) (h₁ : (16253/8192:ℝ) ≤ x) (h₂ : x ≤ (32511/16384:ℝ)) : (3857446169/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (15399729/312500000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (502378709/10000000000:ℝ) := by nlinarith
  have hc1 : (998738341287/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998738341287/1000000000000:ℝ) ≤ taylorCos (502378709/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499393015749/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (15399729/312500000:ℝ) + taylorErr ≤ (499393015749/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (49259187781/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (49259187781/1000000000000:ℝ) ≤ taylorSin (15399729/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (2510837187/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (502378709/10000000000:ℝ) + taylorErr ≤ (2510837187/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998738341287/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499393015749/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2510837187/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-49259187781/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (779118429547/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6233906174369/1000000000000:ℝ) := by nlinarith
  have hp1 : (10315519165143/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2063421202711/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-259045734411/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-254067047807/500000000000:ℝ) := by nlinarith
  have hN : (1506872436901/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9590396547709/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1506872436901/1000000000000:ℝ) (9590396547709/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3857446169/10000000000000:ℝ) ≤ ((1506872436901/1000000000000:ℝ)/(9590396547709/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_199 (x : ℝ) (h₁ : (16253/8192:ℝ) ≤ x) (h₂ : x ≤ (8129/4096:ℝ)) : (1902333181/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (120800987/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (502378709/10000000000:ℝ) := by nlinarith
  have hc1 : (998738341287/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998738341287/1000000000000:ℝ) ≤ taylorCos (502378709/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998832799117/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (120800987/2500000000:ℝ) + taylorErr ≤ (998832799117/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (48301591169/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (48301591169/1000000000000:ℝ) ≤ taylorSin (120800987/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (2510837187/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (502378709/10000000000:ℝ) + taylorErr ≤ (2510837187/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998738341287/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998832799117/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2510837187/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-48301591169/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (779118429547/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3117432456181/500000000000:ℝ) := by nlinarith
  have hp1 : (10315519165143/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5159346361797/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-518171148233/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-49825598941/100000000000:ℝ) := by nlinarith
  have hN : (1496994330697/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38373540475403/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1496994330697/1000000000000:ℝ) (38373540475403/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1902333181/5000000000000:ℝ) ≤ ((1496994330697/1000000000000:ℝ)/(38373540475403/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_200 (x : ℝ) (h₁ : (32511/16384:ℝ) ≤ x) (h₂ : x ≤ (8129/4096:ℝ)) : (951324587/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (120800987/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (492791329/10000000000:ℝ) := by nlinarith
  have hc1 : (998786026969/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998786026969/1000000000000:ℝ) ≤ taylorCos (492791329/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998832799117/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (120800987/2500000000:ℝ) + taylorErr ≤ (998832799117/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (48301591169/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (48301591169/1000000000000:ℝ) ≤ taylorSin (120800987/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (24629596203/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (492791329/10000000000:ℝ) + taylorErr ≤ (24629596203/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998786026969/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998832799117/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24629596203/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-48301591169/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (194809567949/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3117432456181/500000000000:ℝ) := by nlinarith
  have hp1 : (10317105875159/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5159346361797/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2033161881/4000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-498332630029/1000000000000:ℝ) := by nlinarith
  have hN : (748559328499/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38373540475403/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (748559328499/500000000000:ℝ) (38373540475403/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (951324587/2500000000000:ℝ) ≤ ((748559328499/500000000000:ℝ)/(38373540475403/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_201 (x : ℝ) (h₁ : (8129/4096:ℝ) ≤ x) (h₂ : x ≤ (32521/16384:ℝ)) : (3753514923/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (59202071/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (483203949/10000000000:ℝ) := by nlinarith
  have hc1 : (998832794587/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998832794587/1000000000000:ℝ) ≤ taylorCos (483203949/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (99887864863/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (59202071/1250000000:ℝ) + taylorErr ≤ (99887864863/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (47343950159/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (47343950159/1000000000000:ℝ) ≤ taylorSin (59202071/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (48301595793/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (483203949/10000000000:ℝ) + taylorErr ≤ (48301595793/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998832794587/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (99887864863/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-48301595793/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-47343950159/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6234864912361/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3117911825177/500000000000:ℝ) := by nlinarith
  have hp1 : (5159346292589/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (322508732301/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-19939438627/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-244263833729/500000000000:ℝ) := by nlinarith
  have hN : (297472092409/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76770993196629/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (297472092409/200000000000:ℝ) (76770993196629/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3753514923/10000000000000:ℝ) ≤ ((297472092409/200000000000:ℝ)/(76770993196629/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_202 (x : ℝ) (h₁ : (8129/4096:ℝ) ≤ x) (h₂ : x ≤ (16263/8192:ℝ)) : (1850748599/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (116007297/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (483203949/10000000000:ℝ) := by nlinarith
  have hc1 : (998832794587/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998832794587/1000000000000:ℝ) ≤ taylorCos (483203949/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199784715999/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (116007297/2500000000:ℝ) + taylorErr ≤ (199784715999/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (46386265631/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (46386265631/1000000000000:ℝ) ≤ taylorSin (116007297/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (48301595793/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (483203949/10000000000:ℝ) + taylorErr ≤ (48301595793/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998832794587/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199784715999/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-48301595793/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-46386265631/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6234864912361/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6236782388347/1000000000000:ℝ) := by nlinarith
  have hp1 : (5159346292589/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1290233267959/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-249281303151/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-23932280761/50000000000:ℝ) := by nlinarith
  have hN : (1477478409807/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76794909119191/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1477478409807/1000000000000:ℝ) (76794909119191/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1850748599/5000000000000:ℝ) ≤ ((1477478409807/1000000000000:ℝ)/(76794909119191/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_203 (x : ℝ) (h₁ : (8129/4096:ℝ) ≤ x) (h₂ : x ≤ (4067/2048:ℝ)) : (359863857/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (483203949/10000000000:ℝ) := by nlinarith
  have hc1 : (998832794587/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998832794587/1000000000000:ℝ) ≤ taylorCos (483203949/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499505344059/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/2500000000:ℝ) + taylorErr ≤ (499505344059/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5558846193/125000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5558846193/125000000000:ℝ) ≤ taylorSin (111213607/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (48301595793/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (483203949/10000000000:ℝ) + taylorErr ≤ (48301595793/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998832794587/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499505344059/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-48301595793/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5558846193/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6234864912361/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6238699864331/1000000000000:ℝ) := by nlinarith
  have hp1 : (5159346292589/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2581259890937/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-99743177511/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-9177603999/20000000000:ℝ) := by nlinarith
  have hN : (1457712994537/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9605343999301/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1457712994537/1000000000000:ℝ) (9605343999301/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (359863857/1000000000000:ℝ) ≤ ((1457712994537/1000000000000:ℝ)/(9605343999301/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_204 (x : ℝ) (h₁ : (32521/16384:ℝ) ≤ x) (h₂ : x ≤ (16263/8192:ℝ)) : (3702095739/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (116007297/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (473616569/10000000000:ℝ) := by nlinarith
  have hc1 : (998878644101/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998878644101/1000000000000:ℝ) ≤ taylorCos (473616569/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199784715999/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (116007297/2500000000:ℝ) + taylorErr ≤ (199784715999/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (46386265631/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (46386265631/1000000000000:ℝ) ≤ taylorSin (116007297/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (47343954783/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (473616569/10000000000:ℝ) + taylorErr ≤ (47343954783/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998878644101/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199784715999/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-47343954783/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-46386265631/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6235823650353/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6236782388347/1000000000000:ℝ) := by nlinarith
  have hp1 : (5160139647597/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1290233267959/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-488677963983/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-119679804193/250000000000:ℝ) := by nlinarith
  have hN : (1477597860873/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76794909119191/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1477597860873/1000000000000:ℝ) (76794909119191/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3702095739/10000000000000:ℝ) ≤ ((1477597860873/1000000000000:ℝ)/(76794909119191/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_205 (x : ℝ) (h₁ : (16263/8192:ℝ) ≤ x) (h₂ : x ≤ (32531/16384:ℝ)) : (3651040643/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (28402613/625000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (464029189/10000000000:ℝ) := by nlinarith
  have hc1 : (499461787733/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499461787733/500000000000:ℝ) ≤ taylorCos (464029189/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (249741898293/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (28402613/625000000:ℝ) + taylorErr ≤ (249741898293/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22714269233/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22714269233/500000000000:ℝ) ≤ taylorSin (28402613/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (9277254051/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (464029189/10000000000:ℝ) + taylorErr ≤ (9277254051/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499461787733/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249741898293/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-9277254051/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-22714269233/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3118391194173/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6237741126339/1000000000000:ℝ) := by nlinarith
  have hp1 : (10321866005213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1032345285371/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-478866474037/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-234453643429/500000000000:ℝ) := by nlinarith
  have hN : (366957715581/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38409414359221/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (366957715581/250000000000:ℝ) (38409414359221/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3651040643/10000000000000:ℝ) ≤ ((366957715581/250000000000:ℝ)/(38409414359221/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_206 (x : ℝ) (h₁ : (16263/8192:ℝ) ≤ x) (h₂ : x ≤ (4067/2048:ℝ)) : (719956733/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (464029189/10000000000:ℝ) := by nlinarith
  have hc1 : (499461787733/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499461787733/500000000000:ℝ) ≤ taylorCos (464029189/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499505344059/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/2500000000:ℝ) + taylorErr ≤ (499505344059/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5558846193/125000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5558846193/125000000000:ℝ) ≤ taylorSin (111213607/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (9277254051/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (464029189/10000000000:ℝ) + taylorErr ≤ (9277254051/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499461787733/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499505344059/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-9277254051/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5558846193/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3118391194173/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6238699864331/1000000000000:ℝ) := by nlinarith
  have hp1 : (10321866005213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2581259890937/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-239470037799/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-459021324381/1000000000000:ℝ) := by nlinarith
  have hN : (1457944899847/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9605343999301/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1457944899847/1000000000000:ℝ) (9605343999301/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (719956733/2000000000000:ℝ) ≤ ((1457944899847/1000000000000:ℝ)/(9605343999301/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_207 (x : ℝ) (h₁ : (32531/16384:ℝ) ≤ x) (h₂ : x ≤ (4067/2048:ℝ)) : (3600349479/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (454441809/10000000000:ℝ) := by nlinarith
  have hc1 : (998967588643/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998967588643/1000000000000:ℝ) ≤ taylorCos (454441809/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499505344059/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/2500000000:ℝ) + taylorErr ≤ (499505344059/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5558846193/125000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5558846193/125000000000:ℝ) ≤ taylorSin (111213607/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (4542854309/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (454441809/10000000000:ℝ) + taylorErr ≤ (4542854309/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998967588643/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499505344059/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4542854309/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5558846193/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3118870563169/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6238699864331/1000000000000:ℝ) := by nlinarith
  have hp1 : (10323452715229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2581259890937/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-58631438091/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-459091886597/1000000000000:ℝ) := by nlinarith
  have hN : (36451486881/25000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9605343999301/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (36451486881/25000000000:ℝ) (9605343999301/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3600349479/10000000000000:ℝ) ≤ ((36451486881/25000000000:ℝ)/(9605343999301/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_208 (x : ℝ) (h₁ : (4067/2048:ℝ) ≤ x) (h₂ : x ≤ (16273/8192:ℝ)) : (699904903/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (106419917/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (444854429/10000000000:ℝ) := by nlinarith
  have hc1 : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99901068359/100000000000:ℝ) ≤ taylorCos (444854429/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499547061583/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (106419917/2500000000:ℝ) + taylorErr ≤ (499547061583/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42555109951/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42555109951/1000000000000:ℝ) ≤ taylorSin (106419917/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (5558846771/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (444854429/10000000000:ℝ) + taylorErr ≤ (5558846771/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499547061583/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5558846771/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-42555109951/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (623869986433/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1560154335079/250000000000:ℝ) := by nlinarith
  have hp1 : (5162519712623/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (413128519353/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-459303627163/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-439383187989/1000000000000:ℝ) := by nlinarith
  have hN : (1438393871579/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38445304788253/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1438393871579/1000000000000:ℝ) (38445304788253/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (699904903/2000000000000:ℝ) ≤ ((1438393871579/1000000000000:ℝ)/(38445304788253/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_209 (x : ℝ) (h₁ : (4067/2048:ℝ) ≤ x) (h₂ : x ≤ (8139/4096:ℝ)) : (339970037/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (101626227/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (444854429/10000000000:ℝ) := by nlinarith
  have hc1 : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99901068359/100000000000:ℝ) ≤ taylorCos (444854429/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999173884831/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (101626227/2500000000:ℝ) + taylorErr ≤ (999173884831/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8127858779/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8127858779/200000000000:ℝ) ≤ taylorSin (101626227/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (5558846771/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (444854429/10000000000:ℝ) + taylorErr ≤ (5558846771/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999173884831/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5558846771/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-8127858779/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (623869986433/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6242534816301/1000000000000:ℝ) := by nlinarith
  have hp1 : (5162519712623/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10331386403903/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-459444751611/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-163907153/390625000:ℝ) := by nlinarith
  have hN : (141861299527/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76938481865461/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (141861299527/100000000000:ℝ) (76938481865461/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (339970037/1000000000000:ℝ) ≤ ((141861299527/100000000000:ℝ)/(76938481865461/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_210 (x : ℝ) (h₁ : (4067/2048:ℝ) ≤ x) (h₂ : x ≤ (509/256:ℝ)) : (3204719257/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (444854429/10000000000:ℝ) := by nlinarith
  have hc1 : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99901068359/100000000000:ℝ) ≤ taylorCos (444854429/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (5558846771/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (444854429/10000000000:ℝ) + taylorErr ≤ (5558846771/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999322386851/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5558846771/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (623869986433/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6246369768271/1000000000000:ℝ) := by nlinarith
  have hp1 : (5162519712623/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5168866622029/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-229863500253/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-380036004551/1000000000000:ℝ) := by nlinarith
  have hN : (1379046688141/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3851713528197/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1379046688141/1000000000000:ℝ) (3851713528197/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3204719257/10000000000000:ℝ) ≤ ((1379046688141/1000000000000:ℝ)/(3851713528197/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_211 (x : ℝ) (h₁ : (16273/8192:ℝ) ≤ x) (h₂ : x ≤ (8139/4096:ℝ)) : (42508981/125000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (101626227/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (425679669/10000000000:ℝ) := by nlinarith
  have hc1 : (999094118637/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999094118637/1000000000000:ℝ) ≤ taylorCos (425679669/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999173884831/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (101626227/2500000000:ℝ) + taylorErr ≤ (999173884831/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8127858779/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8127858779/200000000000:ℝ) ≤ taylorSin (101626227/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (1702204583/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (425679669/10000000000:ℝ) + taylorErr ≤ (1702204583/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999094118637/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999173884831/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1702204583/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-8127858779/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1248123468063/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6242534816301/1000000000000:ℝ) := by nlinarith
  have hp1 : (10328212845281/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10331386403903/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-439653332137/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-419731277229/1000000000000:ℝ) := by nlinarith
  have hN : (709412697933/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76938481865461/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (709412697933/500000000000:ℝ) (76938481865461/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (42508981/125000000000:ℝ) ≤ ((709412697933/500000000000:ℝ)/(76938481865461/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_212 (x : ℝ) (h₁ : (8139/4096:ℝ) ≤ x) (h₂ : x ≤ (16283/8192:ℝ)) : (3303364277/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (96832537/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (406504909/10000000000:ℝ) := by nlinarith
  have hc1 : (999173880303/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999173880303/1000000000000:ℝ) ≤ taylorCos (406504909/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999249972821/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (96832537/2500000000:ℝ) + taylorErr ≤ (999249972821/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1936166421/50000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1936166421/50000000000:ℝ) ≤ taylorSin (96832537/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (40639298519/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (406504909/10000000000:ℝ) + taylorErr ≤ (40639298519/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999173880303/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999249972821/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-40639298519/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1936166421/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (62425348163/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3122226146143/500000000000:ℝ) := by nlinarith
  have hp1 : (2582846566329/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10334559823981/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1679957047/4000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-80013132677/200000000000:ℝ) := by nlinarith
  have hN : (174904942961/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9623296107659/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (174904942961/125000000000:ℝ) (9623296107659/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3303364277/10000000000000:ℝ) ≤ ((174904942961/125000000000:ℝ)/(9623296107659/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_213 (x : ℝ) (h₁ : (8139/4096:ℝ) ≤ x) (h₂ : x ≤ (509/256:ℝ)) : (3206563771/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (406504909/10000000000:ℝ) := by nlinarith
  have hc1 : (999173880303/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999173880303/1000000000000:ℝ) ≤ taylorCos (406504909/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (40639298519/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (406504909/10000000000:ℝ) + taylorErr ≤ (40639298519/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999173880303/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999322386851/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-40639298519/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (62425348163/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6246369768271/1000000000000:ℝ) := by nlinarith
  have hp1 : (2582846566329/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5168866622029/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-105029556829/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-190134807047/500000000000:ℝ) := by nlinarith
  have hN : (1379443494397/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3851713528197/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1379443494397/1000000000000:ℝ) (3851713528197/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3206563771/10000000000000:ℝ) ≤ ((1379443494397/1000000000000:ℝ)/(3851713528197/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_214 (x : ℝ) (h₁ : (16283/8192:ℝ) ≤ x) (h₂ : x ≤ (509/256:ℝ)) : (641492121/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (387330149/10000000000:ℝ) := by nlinarith
  have hc1 : (249812492073/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249812492073/250000000000:ℝ) ≤ taylorCos (387330149/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (9680833261/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (387330149/10000000000:ℝ) + taylorErr ≤ (9680833261/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249812492073/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999322386851/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-9680833261/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1248890458457/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6246369768271/1000000000000:ℝ) := by nlinarith
  have hp1 : (10334559685351/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5168866622029/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-40031148733/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-190193209433/500000000000:ℝ) := by nlinarith
  have hN : (689818193579/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3851713528197/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (689818193579/500000000000:ℝ) (3851713528197/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (641492121/2000000000000:ℝ) ≤ ((689818193579/500000000000:ℝ)/(3851713528197/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_215 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (16293/8192:ℝ)) : (1556503067/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (348980629/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999391126663/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (348980629/10000000000:ℝ) + taylorErr ≤ (999391126663/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (34890977491/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (34890977491/1000000000000:ℝ) ≤ taylorSin (348980629/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999391126663/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-34890977491/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (195258976383/31250000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1292613333017/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-95155020333/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-360693613087/1000000000000:ℝ) := by nlinarith
  have hN : (136001599541/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15416437394693/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (136001599541/100000000000:ℝ) (15416437394693/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1556503067/5000000000000:ℝ) ≤ ((136001599541/100000000000:ℝ)/(15416437394693/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_216 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (8149/4096:ℝ)) : (1509609143/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (329805869/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999456192001/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (329805869/10000000000:ℝ) + taylorErr ≤ (999456192001/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (32974606027/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (32974606027/1000000000000:ℝ) ≤ taylorSin (329805869/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999456192001/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-32974606027/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6250204720241/1000000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10344080084213/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-380736886119/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-170441338181/500000000000:ℝ) := by nlinarith
  have hN : (268041011737/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38565059044923/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (268041011737/200000000000:ℝ) (38565059044923/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1509609143/5000000000000:ℝ) ≤ ((268041011737/200000000000:ℝ)/(38565059044923/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_217 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (4077/2048:ℝ)) : (2836262683/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (291456349/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999575298311/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (291456349/10000000000:ℝ) + taylorErr ≤ (999575298311/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (227668019/7812500000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (227668019/7812500000:ℝ) ≤ taylorSin (291456349/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999575298311/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-227668019/7812500000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (625403967221/100000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10350426924367/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-76194099139/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-150628557891/500000000000:ℝ) := by nlinarith
  have hN : (260115899621/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38613012221577/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (260115899621/200000000000:ℝ) (38613012221577/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2836262683/10000000000000:ℝ) ≤ ((260115899621/200000000000:ℝ)/(38613012221577/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_218 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (2041/1024:ℝ)) : (248869577/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499884703807/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125234191523/20000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10363120604677/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-190718857423/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-27749160859/125000000000:ℝ) := by nlinarith
  have hN : (244263133839/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38709006816049/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (244263133839/200000000000:ℝ) (38709006816049/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (248869577/1000000000000:ℝ) ≤ ((244263133839/200000000000:ℝ)/(38709006816049/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_219 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (1023/512:ℝ)) : (1865845891/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1227176467/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6277049384029/1000000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10388507965297/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-95593038287/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-12686222789/200000000000:ℝ) := by nlinarith
  have hN : (265688374067/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38901348969539/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (265688374067/250000000000:ℝ) (38901348969539/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1865845891/10000000000000:ℝ) ≤ ((265688374067/250000000000:ℝ)/(38901348969539/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_220 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (410811713/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-95686482117/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (999322358801/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (999322358801/1000000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (410811713/2500000000000:ℝ) ≤ ((999322358801/1000000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_221 (x : ℝ) (h₁ : (16293/8192:ℝ) ≤ x) (h₂ : x ≤ (8149/4096:ℝ)) : (377499941/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (329805869/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (34898063/1000000000:ℝ) := by nlinarith
  have hc1 : (124923890267/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124923890267/125000000000:ℝ) ≤ taylorCos (34898063/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999456192001/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (329805869/10000000000:ℝ) + taylorErr ≤ (999456192001/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (32974606027/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (32974606027/1000000000000:ℝ) ≤ taylorSin (329805869/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (6978196423/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (34898063/1000000000:ℝ) + taylorErr ≤ (6978196423/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124923890267/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999456192001/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6978196423/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-32974606027/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1249657448851/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6250204720241/1000000000000:ℝ) := by nlinarith
  have hp1 : (10340906525421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10344080084213/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-72183022643/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-340987318637/1000000000000:ℝ) := by nlinarith
  have hN : (1340378440773/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38565059044923/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1340378440773/1000000000000:ℝ) (38565059044923/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (377499941/1250000000000:ℝ) ≤ ((1340378440773/1000000000000:ℝ)/(38565059044923/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_222 (x : ℝ) (h₁ : (8149/4096:ℝ) ≤ x) (h₂ : x ≤ (16303/8192:ℝ)) : (1464219713/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (310631109/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (32980587/1000000000:ℝ) := by nlinarith
  have hc1 : (499728093737/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499728093737/500000000000:ℝ) ≤ taylorCos (32980587/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499758791313/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (310631109/10000000000:ℝ) + taylorErr ≤ (499758791313/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (15529056663/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (15529056663/500000000000:ℝ) ≤ taylorSin (310631109/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (32974610651/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (32980587/1000000000:ℝ) + taylorErr ≤ (32974610651/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499728093737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499758791313/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32974610651/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-15529056663/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (78127559003/12500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (250084887849/40000000000:ℝ) := by nlinarith
  have hp1 : (646504996591/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10347253504289/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-85299163903/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-321267607199/1000000000000:ℝ) := by nlinarith
  have hN : (1320723794673/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77178063913059/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1320723794673/1000000000000:ℝ) (77178063913059/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1464219713/5000000000000:ℝ) ≤ ((1320723794673/1000000000000:ℝ)/(77178063913059/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_223 (x : ℝ) (h₁ : (8149/4096:ℝ) ≤ x) (h₂ : x ≤ (4077/2048:ℝ)) : (354706643/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (291456349/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (32980587/1000000000:ℝ) := by nlinarith
  have hc1 : (499728093737/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499728093737/500000000000:ℝ) ≤ taylorCos (32980587/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999575298311/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (291456349/10000000000:ℝ) + taylorErr ≤ (999575298311/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (227668019/7812500000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (227668019/7812500000:ℝ) ≤ taylorSin (291456349/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (32974610651/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (32980587/1000000000:ℝ) + taylorErr ≤ (32974610651/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499728093737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999575298311/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32974610651/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-227668019/7812500000:ℝ) := by rw [hsx]; linarith
  have hb1 : (78127559003/12500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (625403967221/100000000000:ℝ) := by nlinarith
  have hp1 : (646504996591/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10350426924367/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-341301297903/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-301442072263/1000000000000:ℝ) := by nlinarith
  have hN : (1300898259737/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38613012221577/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1300898259737/1000000000000:ℝ) (38613012221577/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (354706643/1250000000000:ℝ) ≤ ((1300898259737/1000000000000:ℝ)/(38613012221577/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_224 (x : ℝ) (h₁ : (16303/8192:ℝ) ≤ x) (h₂ : x ≤ (4077/2048:ℝ)) : (2838324453/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (291456349/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (31063111/1000000000:ℝ) := by nlinarith
  have hc1 : (499758789049/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499758789049/500000000000:ℝ) ≤ taylorCos (31063111/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999575298311/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (291456349/10000000000:ℝ) + taylorErr ≤ (999575298311/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (227668019/7812500000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (227668019/7812500000:ℝ) ≤ taylorSin (291456349/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (621162359/20000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (31063111/1000000000:ℝ) + taylorErr ≤ (621162359/20000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499758789049/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999575298311/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-621162359/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-227668019/7812500000:ℝ) := by rw [hsx]; linarith
  have hb1 : (24422352329/3906250000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (625403967221/100000000000:ℝ) := by nlinarith
  have hp1 : (1034725336549/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10350426924367/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1285859121/4000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-301534550503/1000000000000:ℝ) := by nlinarith
  have hN : (1301052128601/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38613012221577/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1301052128601/1000000000000:ℝ) (38613012221577/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2838324453/10000000000000:ℝ) ≤ ((1301052128601/1000000000000:ℝ)/(38613012221577/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_225 (x : ℝ) (h₁ : (4077/2048:ℝ) ≤ x) (h₂ : x ≤ (8159/4096:ℝ)) : (2661857281/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (5829127/200000000:ℝ) := by nlinarith
  have hc1 : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124946911723/125000000000:ℝ) ≤ taylorCos (5829127/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (39987188161/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/1000000000:ℝ) + taylorErr ≤ (39987188161/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (12653989179/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (12653989179/500000000000:ℝ) ≤ taylorSin (25310683/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (29141511057/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5829127/200000000:ℝ) + taylorErr ≤ (29141511057/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (39987188161/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-29141511057/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-12653989179/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6254039672209/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (312893731209/50000000000:ℝ) := by nlinarith
  have hp1 : (414017071421/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5178386882261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-150906018587/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-65487094271/250000000000:ℝ) := by nlinarith
  have hN : (315380917717/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9665248702989/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (315380917717/250000000000:ℝ) (9665248702989/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2661857281/10000000000000:ℝ) ≤ ((315380917717/250000000000:ℝ)/(9665248702989/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_226 (x : ℝ) (h₁ : (4077/2048:ℝ) ≤ x) (h₂ : x ≤ (2041/1024:ℝ)) : (1245418929/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (5829127/200000000:ℝ) := by nlinarith
  have hc1 : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124946911723/125000000000:ℝ) ≤ taylorCos (5829127/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (29141511057/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5829127/200000000:ℝ) + taylorErr ≤ (29141511057/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499884703807/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-29141511057/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6254039672209/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125234191523/20000000000:ℝ) := by nlinarith
  have hp1 : (414017071421/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10363120604677/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-301996993687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-222265871949/1000000000000:ℝ) := by nlinarith
  have hN : (1221841165733/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38709006816049/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1221841165733/1000000000000:ℝ) (38709006816049/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1245418929/5000000000000:ℝ) ≤ ((1221841165733/1000000000000:ℝ)/(38709006816049/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_227 (x : ℝ) (h₁ : (8159/4096:ℝ) ≤ x) (h₂ : x ≤ (2041/1024:ℝ)) : (1245909663/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (253106831/10000000000:ℝ) := by nlinarith
  have hc1 : (499839849749/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499839849749/500000000000:ℝ) ≤ taylorCos (253106831/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (12653991491/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (253106831/10000000000:ℝ) + taylorErr ≤ (12653991491/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499839849749/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499884703807/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12653991491/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6257874624179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125234191523/20000000000:ℝ) := by nlinarith
  have hp1 : (2071354725119/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10363120604677/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8195927497/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-27800270561/125000000000:ℝ) := by nlinarith
  have hN : (611040931993/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38709006816049/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (611040931993/500000000000:ℝ) (38709006816049/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1245909663/5000000000000:ℝ) ≤ ((611040931993/500000000000:ℝ)/(38709006816049/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_228 (x : ℝ) (h₁ : (2041/1024:ℝ) ≤ x) (h₂ : x ≤ (8169/4096:ℝ)) : (2327527631/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (17640779/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (214757311/10000000000:ℝ) := by nlinarith
  have hc1 : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62485587693/62500000000:ℝ) ≤ taylorCos (214757311/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199968881551/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (17640779/1000000000:ℝ) + taylorErr ≤ (199968881551/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (551245681/31250000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (551245681/31250000000:ℝ) ≤ taylorSin (17640779/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (21474082607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (214757311/10000000000:ℝ) + taylorErr ≤ (21474082607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199968881551/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21474082607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-551245681/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6261709576149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6265544528119/1000000000000:ℝ) := by nlinarith
  have hp1 : (2072624093133/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10369467444831/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-222674800501/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-45701003187/250000000000:ℝ) := by nlinarith
  have hN : (295643353959/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19378524116921/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (295643353959/250000000000:ℝ) (19378524116921/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2327527631/10000000000000:ℝ) ≤ ((295643353959/250000000000:ℝ)/(19378524116921/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_229 (x : ℝ) (h₁ : (2041/1024:ℝ) ≤ x) (h₂ : x ≤ (4087/2048:ℝ)) : (1084176557/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (13805827/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (214757311/10000000000:ℝ) := by nlinarith
  have hc1 : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62485587693/62500000000:ℝ) ≤ taylorCos (214757311/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499952351673/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (13805827/1000000000:ℝ) + taylorErr ≤ (499952351673/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (552215447/40000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (552215447/40000000000:ℝ) ≤ taylorSin (13805827/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (21474082607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (214757311/10000000000:ℝ) + taylorErr ≤ (21474082607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499952351673/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21474082607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-552215447/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6261709576149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6269379480089/1000000000000:ℝ) := by nlinarith
  have hp1 : (2072624093133/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5187907142493/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-222811093071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-71533440003/500000000000:ℝ) := by nlinarith
  have hN : (571418141547/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77610238130723/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (571418141547/500000000000:ℝ) (77610238130723/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1084176557/5000000000000:ℝ) ≤ ((571418141547/500000000000:ℝ)/(77610238130723/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_230 (x : ℝ) (h₁ : (2041/1024:ℝ) ≤ x) (h₂ : x ≤ (1023/512:ℝ)) : (1867963109/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (214757311/10000000000:ℝ) := by nlinarith
  have hc1 : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62485587693/62500000000:ℝ) ≤ taylorCos (214757311/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (21474082607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (214757311/10000000000:ℝ) + taylorErr ≤ (21474082607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21474082607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1227176467/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6261709576149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6277049384029/1000000000000:ℝ) := by nlinarith
  have hp1 : (2072624093133/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10388507965297/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-223083678211/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-317934439/5000000000:ℝ) := by nlinarith
  have hN : (132919536361/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38901348969539/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (132919536361/125000000000:ℝ) (38901348969539/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1867963109/10000000000000:ℝ) ≤ ((132919536361/125000000000:ℝ)/(38901348969539/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_231 (x : ℝ) (h₁ : (8169/4096:ℝ) ≤ x) (h₂ : x ≤ (4087/2048:ℝ)) : (2168970253/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (13805827/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (176407791/10000000000:ℝ) := by nlinarith
  have hc1 : (999844403229/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999844403229/1000000000000:ℝ) ≤ taylorCos (176407791/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499952351673/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (13805827/1000000000:ℝ) + taylorErr ≤ (499952351673/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (552215447/40000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (552215447/40000000000:ℝ) ≤ taylorSin (13805827/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (17639866417/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (176407791/10000000000:ℝ) + taylorErr ≤ (17639866417/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999844403229/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499952351673/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-17639866417/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-552215447/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3132772264059/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6269379480089/1000000000000:ℝ) := by nlinarith
  have hp1 : (10369467305733/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5187907142493/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-36605595591/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-17894312573/125000000000:ℝ) := by nlinarith
  have hN : (1142998903813/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77610238130723/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1142998903813/1000000000000:ℝ) (77610238130723/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2168970253/10000000000000:ℝ) ≤ ((1142998903813/1000000000000:ℝ)/(77610238130723/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_232 (x : ℝ) (h₁ : (4087/2048:ℝ) ≤ x) (h₂ : x ≤ (1023/512:ℝ)) : (1868712167/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (138058271/10000000000:ℝ) := by nlinarith
  have hc1 : (999904698821/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999904698821/1000000000000:ℝ) ≤ taylorCos (138058271/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (13805390799/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/10000000000:ℝ) + taylorErr ≤ (13805390799/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999904698821/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13805390799/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1227176467/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (783672435011/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6277049384029/1000000000000:ℝ) := by nlinarith
  have hp1 : (10375814145803/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10388507965297/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3585435307/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7958096841/125000000000:ℝ) := by nlinarith
  have hN : (1063569473549/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38901348969539/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1063569473549/1000000000000:ℝ) (38901348969539/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1868712167/10000000000000:ℝ) ≤ ((1063569473549/1000000000000:ℝ)/(38901348969539/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_233 (x : ℝ) (h₁ : (1023/512:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (822707073/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/78125000:ℝ) := by nlinarith
  have hc1 : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49999058651/50000000000:ℝ) ≤ taylorCos (479369/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (76698587/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/78125000:ℝ) + taylorErr ≤ (76698587/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-76698587/12500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1569262346007/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (1298563478243/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-63805020149/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (499990574749/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499990574749/500000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (822707073/5000000000000:ℝ) ≤ ((499990574749/500000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_234 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (4097/2048:ℝ)) : (1591808227/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/312500000:ℝ) := by nlinarith
  have hc1 : (99999882119/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99999882119/100000000000:ℝ) ≤ taylorCos (479369/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1533982461/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/312500000:ℝ) + taylorErr ≤ (1533982461/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (99999882119/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1533982461/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6283185307179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (196397477749/31250000000:ℝ) := by nlinarith
  have hp1 : (5199331385027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5200600822803/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2941/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (7977630449/500000000000:ℝ) := by nlinarith
  have hN : (246010890073/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15599078611423/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (246010890073/250000000000:ℝ) (15599078611423/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1591808227/10000000000000:ℝ) ≤ ((246010890073/250000000000:ℝ)/(15599078611423/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_235 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (2051/1024:ℝ)) : (1337086167/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1438107/156250000:ℝ) := by nlinarith
  have hc1 : (999957642289/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999957642289/1000000000000:ℝ) ≤ taylorCos (1438107/156250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (9203757117/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1438107/156250000:ℝ) + taylorErr ≤ (9203757117/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999957642289/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (9203757117/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6283185307179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6292389191907/1000000000000:ℝ) := by nlinarith
  have hp1 : (5199331385027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5206947662957/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-23557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (47923481611/500000000000:ℝ) := by nlinarith
  have hN : (904110679067/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78188323484857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (904110679067/1000000000000:ℝ) (78188323484857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1337086167/10000000000000:ℝ) ≤ ((904110679067/1000000000000:ℝ)/(78188323484857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_236 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (24541230879/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (245436927/10000000000:ℝ) + taylorErr ≤ (24541230879/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6283185307179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/500000000000:ℝ) := by nlinarith
  have hp1 : (5199331385027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11807/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (128096423311/500000000000:ℝ) := by nlinarith
  have hN : (74350596981/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78574890269483/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (74350596981/100000000000:ℝ) (78574890269483/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (179073511/2000000000000:ℝ) ≤ ((74350596981/100000000000:ℝ)/(78574890269483/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_237 (x : ℝ) (h₁ : (4097/2048:ℝ) ≤ x) (h₂ : x ≤ (2051/1024:ℝ)) : (1337086167/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (15339807/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1438107/156250000:ℝ) := by nlinarith
  have hc1 : (999957642289/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999957642289/1000000000000:ℝ) ≤ taylorCos (1438107/156250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499999412857/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (15339807/10000000000:ℝ) + taylorErr ≤ (499999412857/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (383494459/250000000000:ℝ) ≤ taylorSin (15339807/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (9203757117/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1438107/156250000:ℝ) + taylorErr ≤ (9203757117/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999957642289/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499999412857/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (9203757117/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6284719287967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6292389191907/1000000000000:ℝ) := by nlinarith
  have hp1 : (5200600753041/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5206947662957/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (7977606289/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (47923481611/500000000000:ℝ) := by nlinarith
  have hN : (904110679067/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78188323484857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (904110679067/1000000000000:ℝ) (78188323484857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1337086167/10000000000000:ℝ) ≤ ((904110679067/1000000000000:ℝ)/(78188323484857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_238 (x : ℝ) (h₁ : (2051/1024:ℝ) ≤ x) (h₂ : x ≤ (4107/2048:ℝ)) : (1104977691/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (92038847/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (168737887/10000000000:ℝ) := by nlinarith
  have hc1 : (999857638743/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999857638743/1000000000000:ℝ) ≤ taylorCos (168737887/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499978823407/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (92038847/10000000000:ℝ) + taylorErr ≤ (499978823407/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9203752493/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9203752493/1000000000000:ℝ) ≤ taylorSin (92038847/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (16872990243/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (168737887/10000000000:ℝ) + taylorErr ≤ (16872990243/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999857638743/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499978823407/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (9203752493/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (16872990243/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3146194595953/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6300059095847/1000000000000:ℝ) := by nlinarith
  have hp1 : (10413895186221/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (417063560249/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (47923456891/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (17592773457/100000000000:ℝ) := by nlinarith
  have hN : (823929904173/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7838148922233/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (823929904173/1000000000000:ℝ) (7838148922233/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1104977691/10000000000000:ℝ) ≤ ((823929904173/1000000000000:ℝ)/(7838148922233/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_239 (x : ℝ) (h₁ : (2051/1024:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (92038847/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499978823407/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (92038847/10000000000:ℝ) + taylorErr ≤ (499978823407/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9203752493/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9203752493/1000000000000:ℝ) ≤ taylorSin (92038847/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (24541230879/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (245436927/10000000000:ℝ) + taylorErr ≤ (24541230879/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499978823407/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (9203752493/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3146194595953/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/500000000000:ℝ) := by nlinarith
  have hp1 : (10413895186221/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (47923456891/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (128096423311/500000000000:ℝ) := by nlinarith
  have hN : (74350596981/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78574890269483/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (74350596981/100000000000:ℝ) (78574890269483/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (179073511/2000000000000:ℝ) ≤ ((74350596981/100000000000:ℝ)/(78574890269483/1000000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
