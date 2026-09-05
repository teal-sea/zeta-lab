import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_1380 (x : ℝ) (h₁ : (10363/2048:ℝ) ≤ x) (h₂ : x ≤ (5217/1024:ℝ)) : (298692789/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1886796369/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2975922729/10000000000:ℝ) := by nlinarith
  have hc1 : (956045249073/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956045249073/1000000000000:ℝ) ≤ taylorCos (2975922729/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (98225274363/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1886796369/10000000000:ℝ) + taylorErr ≤ (98225274363/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (187562126311/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (187562126311/1000000000000:ℝ) ≤ taylorSin (1886796369/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-98225274363/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-956045249073/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73304791251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-187562126311/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7948321452429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16005555540799/1000000000000:ℝ) := by nlinarith
  have hp1 : (13154460728281/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5297834413973/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3883566457987/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4934557249341/1000000000000:ℝ) := by nlinarith
  have hN : (3952304505711/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127838904084801/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3952304505711/1000000000000:ℝ) (127838904084801/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (298692789/5000000000000:ℝ) ≤ ((3952304505711/1000000000000:ℝ)/(127838904084801/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1381 (x : ℝ) (h₁ : (10363/2048:ℝ) ≤ x) (h₂ : x ≤ (5227/1024:ℝ)) : (592818281/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1886796369/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3282718887/10000000000:ℝ) := by nlinarith
  have hc1 : (946600910791/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (946600910791/1000000000000:ℝ) ≤ taylorCos (3282718887/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (98225274363/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1886796369/10000000000:ℝ) + taylorErr ≤ (98225274363/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (187562126311/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (187562126311/1000000000000:ℝ) ≤ taylorSin (1886796369/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (322407681151/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3282718887/10000000000:ℝ) + taylorErr ≤ (322407681151/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-98225274363/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-946600910791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-322407681151/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-187562126311/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7948321452429/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16036235156557/1000000000000:ℝ) := by nlinarith
  have hp1 : (13154460728281/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (414686668611/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8556682702791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4934557249341/1000000000000:ℝ) := by nlinarith
  have hN : (3952304505711/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (51332167599279/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3952304505711/1000000000000:ℝ) (51332167599279/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (592818281/10000000000000:ℝ) ≤ ((3952304505711/1000000000000:ℝ)/(51332167599279/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1382 (x : ℝ) (h₁ : (41453/8192:ℝ) ≤ x) (h₂ : x ≤ (10381/2048:ℝ)) : (306412007/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1890631321/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2162912911/10000000000:ℝ) := by nlinarith
  have hc1 : (195340016773/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195340016773/200000000000:ℝ) ≤ taylorCos (2162912911/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (982180742227/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1890631321/10000000000:ℝ) + taylorErr ≤ (982180742227/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (187938801721/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (187938801721/1000000000000:ℝ) ≤ taylorSin (1890631321/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-982180742227/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-195340016773/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13413050829/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-187938801721/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3179405280011/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15924254559041/1000000000000:ℝ) := by nlinarith
  have hp1 : (26309556140569/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3294327382323/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1413983380047/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4944586454869/1000000000000:ℝ) := by nlinarith
  have hN : (1981202856321/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506163766522277/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1981202856321/500000000000:ℝ) (506163766522277/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (306412007/5000000000000:ℝ) ≤ ((1981202856321/500000000000:ℝ)/(506163766522277/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1383 (x : ℝ) (h₁ : (41453/8192:ℝ) ≤ x) (h₂ : x ≤ (5193/1024:ℝ)) : (152910611/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1890631321/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2239611951/10000000000:ℝ) := by nlinarith
  have hc1 : (97502534279/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97502534279/100000000000:ℝ) ≤ taylorCos (2239611951/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (982180742227/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1890631321/10000000000:ℝ) + taylorErr ≤ (982180742227/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (187938801721/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (187938801721/1000000000000:ℝ) ≤ taylorSin (1890631321/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (111046811651/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2239611951/10000000000:ℝ) + taylorErr ≤ (111046811651/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-982180742227/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-97502534279/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-111046811651/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-187938801721/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3179405280011/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15931924462981/1000000000000:ℝ) := by nlinarith
  have hp1 : (26309556140569/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5273462547779/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5856012022919/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4944586454869/1000000000000:ℝ) := by nlinarith
  have hN : (1981202856321/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (101330486837653/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1981202856321/500000000000:ℝ) (101330486837653/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (152910611/2500000000000:ℝ) ≤ ((1981202856321/500000000000:ℝ)/(101330486837653/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1384 (x : ℝ) (h₁ : (41455/8192:ℝ) ≤ x) (h₂ : x ≤ (20773/4096:ℝ)) : (38610999/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (75932049/400000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (449456371/2000000000:ℝ) := by nlinarith
  have hc1 : (48742735617/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (48742735617/50000000000:ℝ) ≤ taylorCos (449456371/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (982036306087/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (75932049/400000000:ℝ) + taylorErr ≤ (982036306087/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (94346034783/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (94346034783/500000000000:ℝ) ≤ taylorSin (75932049/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-982036306087/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-48742735617/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-111420696491/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-94346034783/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15897793390449/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127461531627/8000000000:ℝ) := by nlinarith
  have hp1 : (26310825508583/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13184291053463/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1469002891917/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1241161029301/250000000000:ℝ) := by nlinarith
  have hN : (3982607811117/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (253350656948449/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3982607811117/1000000000000:ℝ) (253350656948449/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38610999/625000000000:ℝ) ≤ ((3982607811117/1000000000000:ℝ)/(253350656948449/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1385 (x : ℝ) (h₁ : (41457/8192:ℝ) ≤ x) (h₂ : x ≤ (1299/256:ℝ)) : (77842061/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (238246391/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (981891292259/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (238246391/1250000000:ℝ) + taylorErr ≤ (981891292259/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (18944522631/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (18944522631/100000000000:ℝ) ≤ taylorSin (238246391/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-981891292259/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-486469974967/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-231058110583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-18944522631/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15898560380843/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3985282086927/250000000000:ℝ) := by nlinarith
  have hp1 : (26312094876597/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13191272577633/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6095901035947/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4984700768587/1000000000000:ℝ) := by nlinarith
  have hN : (500351184541/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2536195729981/5000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (500351184541/125000000000:ℝ) (2536195729981/5000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (77842061/1250000000000:ℝ) ≤ ((500351184541/125000000000:ℝ)/(2536195729981/5000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1386 (x : ℝ) (h₁ : (10365/2048:ℝ) ≤ x) (h₂ : x ≤ (10385/2048:ℝ)) : (633910161/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (119842249/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2224272143/10000000000:ℝ) := by nlinarith
  have hc1 : (487682441421/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487682441421/500000000000:ℝ) ≤ taylorCos (2224272143/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (39266907539/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (119842249/625000000:ℝ) + taylorErr ≤ (39266907539/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95287376237/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95287376237/500000000000:ℝ) ≤ taylorSin (119842249/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-39266907539/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-487682441421/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-110298846213/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-95287376237/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7949855433217/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15930390482193/1000000000000:ℝ) := by nlinarith
  have hp1 : (13156999464309/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26364774002833/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2908004153179/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2507391916211/500000000000:ℝ) := by nlinarith
  have hN : (4033111143947/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506554681830291/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4033111143947/1000000000000:ℝ) (506554681830291/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (633910161/10000000000000:ℝ) ≤ ((4033111143947/1000000000000:ℝ)/(506554681830291/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1387 (x : ℝ) (h₁ : (10365/2048:ℝ) ≤ x) (h₂ : x ≤ (5195/1024:ℝ)) : (316344203/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (119842249/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1150485591/5000000000:ℝ) := by nlinarith
  have hc1 : (194728849477/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194728849477/200000000000:ℝ) ≤ taylorCos (1150485591/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (39266907539/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (119842249/625000000:ℝ) + taylorErr ≤ (39266907539/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95287376237/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95287376237/500000000000:ℝ) ≤ taylorSin (119842249/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-39266907539/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194728849477/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4561441709/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-95287376237/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7949855433217/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3984515096533/250000000000:ℝ) := by nlinarith
  have hp1 : (13156999464309/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26377467683141/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-751995507923/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2507391916211/500000000000:ℝ) := by nlinarith
  have hN : (4033111143947/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507043537743981/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4033111143947/1000000000000:ℝ) (507043537743981/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (316344203/5000000000000:ℝ) ≤ ((4033111143947/1000000000000:ℝ)/(507043537743981/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1388 (x : ℝ) (h₁ : (20731/4096:ℝ) ≤ x) (h₂ : x ≤ (41573/8192:ℝ)) : (638241617/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (60160809/312500000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1175412779/5000000000:ℝ) := by nlinarith
  have hc1 : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486247556609/500000000000:ℝ) ≤ taylorCos (1175412779/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (61345389421/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (60160809/312500000:ℝ) + taylorErr ≤ (61345389421/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (191327629871/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (191327629871/1000000000000:ℝ) ≤ taylorSin (60160809/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (2911540921/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1175412779/5000000000:ℝ) + taylorErr ≤ (2911540921/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-61345389421/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-486247556609/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2911540921/12500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-191327629871/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3975119464207/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15943045823693/1000000000000:ℝ) := by nlinarith
  have hp1 : (3289408537079/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26385718575343/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6145847948969/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2517418956307/500000000000:ℝ) := by nlinarith
  have hN : (2026655840939/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2029445681091/4000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2026655840939/500000000000:ℝ) (2029445681091/4000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (638241617/10000000000000:ℝ) ≤ ((2026655840939/500000000000:ℝ)/(2029445681091/4000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1389 (x : ℝ) (h₁ : (20731/4096:ℝ) ≤ x) (h₂ : x ≤ (10401/2048:ℝ)) : (318168869/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (60160809/312500000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2469709069/10000000000:ℝ) := by nlinarith
  have hc1 : (19393147657/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19393147657/20000000000:ℝ) ≤ taylorCos (2469709069/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (61345389421/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (60160809/312500000:ℝ) + taylorErr ≤ (61345389421/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (191327629871/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (191327629871/1000000000000:ℝ) ≤ taylorSin (60160809/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (244467905059/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2469709069/10000000000:ℝ) + taylorErr ≤ (244467905059/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-61345389421/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-19393147657/20000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-244467905059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-191327629871/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3975119464207/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15954934174799/1000000000000:ℝ) := by nlinarith
  have hp1 : (3289408537079/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26405393779823/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1613817824903/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2517418956307/500000000000:ℝ) := by nlinarith
  have hN : (2026655840939/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508119849044339/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2026655840939/500000000000:ℝ) (508119849044339/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (318168869/5000000000000:ℝ) ≤ ((2026655840939/500000000000:ℝ)/(508119849044339/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1390 (x : ℝ) (h₁ : (20731/4096:ℝ) ≤ x) (h₂ : x ≤ (10421/2048:ℝ)) : (63145721/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (60160809/312500000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2776505227/10000000000:ℝ) := by nlinarith
  have hc1 : (480851037121/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (480851037121/500000000000:ℝ) ≤ taylorCos (2776505227/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (61345389421/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (60160809/312500000:ℝ) + taylorErr ≤ (61345389421/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (191327629871/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (191327629871/1000000000000:ℝ) ≤ taylorSin (60160809/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (13704845611/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2776505227/10000000000:ℝ) + taylorErr ≤ (13704845611/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-61345389421/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-480851037121/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13704845611/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-191327629871/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3975119464207/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15985613790557/1000000000000:ℝ) := by nlinarith
  have hp1 : (3289408537079/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26456168501061/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7251554095313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2517418956307/500000000000:ℝ) := by nlinarith
  have hN : (2026655840939/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (510079696521693/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2026655840939/500000000000:ℝ) (510079696521693/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (63145721/1000000000000:ℝ) ≤ ((2026655840939/500000000000:ℝ)/(510079696521693/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1391 (x : ℝ) (h₁ : (5183/1024:ℝ) ≤ x) (h₂ : x ≤ (41535/8192:ℝ)) : (646985877/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (120800987/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2205097383/10000000000:ℝ) := by nlinarith
  have hc1 : (975786080291/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975786080291/1000000000000:ℝ) ≤ taylorCos (2205097383/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (98137919559/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (120800987/625000000:ℝ) + taylorErr ≤ (98137919559/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (48020098679/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (48020098679/250000000000:ℝ) ≤ taylorSin (120800987/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (218727049277/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2205097383/10000000000:ℝ) + taylorErr ≤ (218727049277/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-98137919559/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-975786080291/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-218727049277/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-48020098679/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7950622423611/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (124441195361/7812500000:ℝ) := by nlinarith
  have hp1 : (13158268832323/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5272320116551/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1153199021937/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5054890942183/1000000000000:ℝ) := by nlinarith
  have hN : (4073511746593/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (253216252309497/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4073511746593/1000000000000:ℝ) (253216252309497/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (646985877/10000000000000:ℝ) ≤ ((4073511746593/1000000000000:ℝ)/(253216252309497/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1392 (x : ℝ) (h₁ : (20733/4096:ℝ) ≤ x) (h₂ : x ≤ (41557/8192:ℝ)) : (652032997/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (30320089/156250000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1144733163/5000000000:ℝ) := by nlinarith
  have hc1 : (15217281197/15625000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15217281197/15625000000:ℝ) ≤ taylorCos (1144733163/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (245307895781/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (30320089/156250000:ℝ) + taylorErr ≤ (245307895781/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (48208261641/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (48208261641/250000000000:ℝ) ≤ taylorSin (30320089/156250000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (56737942767/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1144733163/5000000000:ℝ) + taylorErr ≤ (56737942767/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-245307895781/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-15217281197/15625000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-56737942767/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-48208261641/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (993875739851/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15936909900541/1000000000000:ℝ) := by nlinarith
  have hp1 : (1315890351633/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5275112726219/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2992990439497/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5074942908991/1000000000000:ℝ) := by nlinarith
  have hN : (4093711325867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126742548588981/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4093711325867/1000000000000:ℝ) (126742548588981/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (652032997/10000000000000:ℝ) ≤ ((4093711325867/1000000000000:ℝ)/(126742548588981/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1393 (x : ℝ) (h₁ : (20735/4096:ℝ) ≤ x) (h₂ : x ≤ (10413/2048:ℝ)) : (658907567/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61119547/312500000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (663446691/2500000000:ℝ) := by nlinarith
  have hc1 : (120624156321/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (120624156321/125000000000:ℝ) ≤ taylorCos (663446691/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (980934626579/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61119547/312500000:ℝ) + taylorErr ≤ (980934626579/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (194338009501/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (194338009501/1000000000000:ℝ) ≤ taylorSin (61119547/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (131137354689/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (663446691/2500000000:ℝ) + taylorErr ≤ (131137354689/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-980934626579/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-120624156321/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-131137354689/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-194338009501/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3975886454601/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7986670972127/500000000000:ℝ) := by nlinarith
  have hp1 : (1645021610543/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13217929306283/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6933457134769/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-319690225379/62500000000:ℝ) := by nlinarith
  have hN : (826821795897/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (509295305736129/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (826821795897/200000000000:ℝ) (509295305736129/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (658907567/10000000000000:ℝ) ≤ ((826821795897/200000000000:ℝ)/(509295305736129/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1394 (x : ℝ) (h₁ : (41473/8192:ℝ) ≤ x) (h₂ : x ≤ (10391/2048:ℝ)) : (674292103/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (49183259/250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (231631099/1000000000:ℝ) := by nlinarith
  have hc1 : (486646621893/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486646621893/500000000000:ℝ) ≤ taylorCos (231631099/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (980710394353/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (49183259/250000000:ℝ) + taylorErr ≤ (980710394353/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97733215899/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97733215899/500000000000:ℝ) ≤ taylorSin (49183259/250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-980710394353/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-486646621893/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-229565368111/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97733215899/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3180939260799/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (398489859173/25000000000:ℝ) := by nlinarith
  have hp1 : (26322249820709/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6595001604801/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1513983971099/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5145116249349/1000000000000:ℝ) := by nlinarith
  have hN : (1041101463749/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (63392667145487/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1041101463749/250000000000:ℝ) (63392667145487/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (674292103/10000000000000:ℝ) ≤ ((1041101463749/250000000000:ℝ)/(63392667145487/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1395 (x : ℝ) (h₁ : (41475/8192:ℝ) ≤ x) (h₂ : x ≤ (20773/4096:ℝ)) : (682031579/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (246875033/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (449456371/2000000000:ℝ) := by nlinarith
  have hc1 : (48742735617/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (48742735617/50000000000:ℝ) ≤ taylorCos (449456371/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (490280092513/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (246875033/1250000000:ℝ) + taylorErr ≤ (490280092513/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98109284843/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98109284843/500000000000:ℝ) ≤ taylorSin (246875033/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-490280092513/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-48742735617/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-111420696491/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-98109284843/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15905463294389/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127461531627/8000000000:ℝ) := by nlinarith
  have hp1 : (26323519188723/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13184291053463/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1469002891917/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5165163284313/1000000000000:ℝ) := by nlinarith
  have hN : (4184603099287/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (253350656948449/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4184603099287/1000000000000:ℝ) (253350656948449/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (682031579/10000000000000:ℝ) ≤ ((4184603099287/1000000000000:ℝ)/(253350656948449/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1396 (x : ℝ) (h₁ : (41475/8192:ℝ) ≤ x) (h₂ : x ≤ (20793/4096:ℝ)) : (5435249/80000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (246875033/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1200339967/5000000000:ℝ) := by nlinarith
  have hc1 : (194264361627/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194264361627/200000000000:ℝ) ≤ taylorCos (1200339967/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (490280092513/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (246875033/1250000000:ℝ) + taylorErr ≤ (490280092513/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98109284843/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98109284843/500000000000:ℝ) ≤ taylorSin (246875033/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-490280092513/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194264361627/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-237768672711/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-98109284843/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15905463294389/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7974015630627/500000000000:ℝ) := by nlinarith
  have hp1 : (26323519188723/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5278793893509/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6275659087873/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5165163284313/1000000000000:ℝ) := by nlinarith
  have hN : (4184603099287/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50767940221987/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4184603099287/1000000000000:ℝ) (50767940221987/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5435249/80000000000:ℝ) ≤ ((4184603099287/1000000000000:ℝ)/(50767940221987/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1397 (x : ℝ) (h₁ : (5185/1024:ℝ) ≤ x) (h₂ : x ≤ (5195/1024:ℝ)) : (697646719/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (124635939/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1150485591/5000000000:ℝ) := by nlinarith
  have hc1 : (194728849477/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194728849477/200000000000:ℝ) ≤ taylorCos (1150485591/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (196036427647/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (124635939/625000000:ℝ) + taylorErr ≤ (196036427647/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (198098408431/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (198098408431/1000000000000:ℝ) ≤ taylorSin (124635939/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-196036427647/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194728849477/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4561441709/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-198098408431/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7953690385187/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3984515096533/250000000000:ℝ) := by nlinarith
  have hp1 : (13163346304379/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26377467683141/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-751995507923/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5215275905047/1000000000000:ℝ) := by nlinarith
  have hN : (1058773441703/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507043537743981/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1058773441703/250000000000:ℝ) (507043537743981/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (697646719/10000000000000:ℝ) ≤ ((1058773441703/250000000000:ℝ)/(507043537743981/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1398 (x : ℝ) (h₁ : (5185/1024:ℝ) ≤ x) (h₂ : x ≤ (10395/2048:ℝ)) : (174075693/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (124635939/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1188835111/5000000000:ℝ) := by nlinarith
  have hc1 : (1214832919/1250000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (1214832919/1250000000:ℝ) ≤ taylorCos (1188835111/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (196036427647/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (124635939/625000000:ℝ) + taylorErr ≤ (196036427647/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (198098408431/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (198098408431/1000000000000:ℝ) ≤ taylorSin (124635939/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (235533061743/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1188835111/5000000000:ℝ) + taylorErr ≤ (235533061743/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-196036427647/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-1214832919/1250000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-235533061743/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-198098408431/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7953690385187/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1993216286259/125000000000:ℝ) := by nlinarith
  have hp1 : (13163346304379/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6597540340863/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3107877752913/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5215275905047/1000000000000:ℝ) := by nlinarith
  have hN : (1058773441703/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (6344157862093/12500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1058773441703/250000000000:ℝ) (6344157862093/12500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (174075693/2500000000000:ℝ) ≤ ((1058773441703/250000000000:ℝ)/(6344157862093/12500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1399 (x : ℝ) (h₁ : (5185/1024:ℝ) ≤ x) (h₂ : x ≤ (325/64:ℝ)) : (694962061/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (124635939/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (196036427647/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (124635939/625000000:ℝ) + taylorErr ≤ (196036427647/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (198098408431/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (198098408431/1000000000000:ℝ) ≤ taylorSin (124635939/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-196036427647/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970031250923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-242980182203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-198098408431/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7953690385187/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15953400194011/1000000000000:ℝ) := by nlinarith
  have hp1 : (13163346304379/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26402855043761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6415370529213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5215275905047/1000000000000:ℝ) := by nlinarith
  have hN : (1058773441703/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508021955500541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1058773441703/250000000000:ℝ) (508021955500541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (694962061/10000000000000:ℝ) ≤ ((1058773441703/250000000000:ℝ)/(508021955500541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1400 (x : ℝ) (h₁ : (5185/1024:ℝ) ≤ x) (h₂ : x ≤ (5205/1024:ℝ)) : (692290309/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (124635939/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (130388367/500000000:ℝ) := by nlinarith
  have hc1 : (60386875073/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (60386875073/62500000000:ℝ) ≤ taylorCos (130388367/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (196036427647/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (124635939/625000000:ℝ) + taylorErr ≤ (196036427647/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (198098408431/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (198098408431/1000000000000:ℝ) ≤ taylorSin (124635939/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-196036427647/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-60386875073/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-128915552241/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-198098408431/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7953690385187/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1596874000189/100000000000:ℝ) := by nlinarith
  have hp1 : (13163346304379/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1321412120219/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5323455413/781250000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5215275905047/1000000000000:ℝ) := by nlinarith
  have hN : (1058773441703/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127250328623981/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1058773441703/250000000000:ℝ) (127250328623981/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (692290309/10000000000000:ℝ) ≤ ((1058773441703/250000000000:ℝ)/(127250328623981/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1401 (x : ℝ) (h₁ : (5185/1024:ℝ) ≤ x) (h₂ : x ≤ (2605/512:ℝ)) : (68963139/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (124635939/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2761165419/10000000000:ℝ) := by nlinarith
  have hc1 : (192424280397/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192424280397/200000000000:ℝ) ≤ taylorCos (2761165419/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (196036427647/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (124635939/625000000:ℝ) + taylorErr ≤ (196036427647/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (198098408431/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (198098408431/1000000000000:ℝ) ≤ taylorSin (124635939/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-196036427647/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-192424280397/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27262135779/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-198098408431/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7953690385187/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15984079809769/1000000000000:ℝ) := by nlinarith
  have hp1 : (13163346304379/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26453629764999/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-450739029063/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5215275905047/1000000000000:ℝ) := by nlinarith
  have hN : (1058773441703/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50998161473013/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1058773441703/250000000000:ℝ) (50998161473013/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (68963139/1000000000000:ℝ) ≤ ((1058773441703/250000000000:ℝ)/(50998161473013/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1402 (x : ℝ) (h₁ : (5185/1024:ℝ) ≤ x) (h₂ : x ≤ (10441/2048:ℝ)) : (342044549/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (124635939/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (385412673/1250000000:ℝ) := by nlinarith
  have hc1 : (59552602833/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (59552602833/62500000000:ℝ) ≤ taylorCos (385412673/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (196036427647/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (124635939/625000000:ℝ) + taylorErr ≤ (196036427647/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (198098408431/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (198098408431/1000000000000:ℝ) ≤ taylorSin (124635939/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (303467948867/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (385412673/1250000000:ℝ) + taylorErr ≤ (303467948867/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-196036427647/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-59552602833/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-303467948867/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-198098408431/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7953690385187/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8008146703157/500000000000:ℝ) := by nlinarith
  have hp1 : (13163346304379/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13253471611149/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1608801538081/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5215275905047/1000000000000:ℝ) := by nlinarith
  have hN : (1058773441703/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20481732358171/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1058773441703/250000000000:ℝ) (20481732358171/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (342044549/5000000000000:ℝ) ≤ ((1058773441703/250000000000:ℝ)/(20481732358171/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1403 (x : ℝ) (h₁ : (5185/1024:ℝ) ≤ x) (h₂ : x ≤ (10461/2048:ℝ)) : (339431207/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (124635939/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1695048771/5000000000:ℝ) := by nlinarith
  have hc1 : (471542217589/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (471542217589/500000000000:ℝ) ≤ taylorCos (1695048771/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (196036427647/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (124635939/625000000:ℝ) + taylorErr ≤ (196036427647/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (198098408431/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (198098408431/1000000000000:ℝ) ≤ taylorSin (124635939/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (332553372201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1695048771/5000000000:ℝ) + taylorErr ≤ (332553372201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-196036427647/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-471542217589/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-332553372201/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-198098408431/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7953690385187/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2005871627759/125000000000:ℝ) := by nlinarith
  have hp1 : (13163346304379/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26557717943537/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8831858660087/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5215275905047/1000000000000:ℝ) := by nlinarith
  have hN : (1058773441703/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (257005343171107/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1058773441703/250000000000:ℝ) (257005343171107/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (339431207/5000000000000:ℝ) ≤ ((1058773441703/250000000000:ℝ)/(257005343171107/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1404 (x : ℝ) (h₁ : (10371/2048:ℝ) ≤ x) (h₂ : x ≤ (41555/8192:ℝ)) : (711359973/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (125594677/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1140898211/5000000000:ℝ) := by nlinarith
  have hc1 : (974079779957/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (974079779957/1000000000000:ℝ) ≤ taylorCos (1140898211/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244969276491/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (125594677/625000000:ℝ) + taylorErr ≤ (244969276491/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (99800877673/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (99800877673/500000000000:ℝ) ≤ taylorSin (125594677/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-244969276491/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-974079779957/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-45240945567/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-99800877673/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15908914751161/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15936142910147/1000000000000:ℝ) := by nlinarith
  have hp1 : (1645576959049/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3296786782883/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5965990055617/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5255360793329/1000000000000:ℝ) := by nlinarith
  have hN : (855096737473/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506921301705257/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (855096737473/200000000000:ℝ) (506921301705257/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (711359973/10000000000000:ℝ) ≤ ((855096737473/200000000000:ℝ)/(506921301705257/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1405 (x : ℝ) (h₁ : (10371/2048:ℝ) ≤ x) (h₂ : x ≤ (41575/8192:ℝ)) : (709989443/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (125594677/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1179247731/5000000000:ℝ) := by nlinarith
  have hc1 : (38892647091/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38892647091/40000000000:ℝ) ≤ taylorCos (1179247731/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244969276491/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (125594677/625000000:ℝ) + taylorErr ≤ (244969276491/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (99800877673/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (99800877673/500000000000:ℝ) ≤ taylorSin (125594677/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (116834549757/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1179247731/5000000000:ℝ) + taylorErr ≤ (116834549757/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244969276491/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-38892647091/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-116834549757/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-99800877673/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15908914751161/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15943812814087/1000000000000:ℝ) := by nlinarith
  have hp1 : (1645576959049/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13193493971687/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1233164742323/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5255360793329/1000000000000:ℝ) := by nlinarith
  have hN : (855096737473/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50741033410129/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (855096737473/200000000000:ℝ) (50741033410129/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (709989443/10000000000000:ℝ) ≤ ((855096737473/200000000000:ℝ)/(50741033410129/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1406 (x : ℝ) (h₁ : (10371/2048:ℝ) ≤ x) (h₂ : x ≤ (20813/4096:ℝ)) : (706509509/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (125594677/625000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (638519503/2500000000:ℝ) := by nlinarith
  have hc1 : (967560346987/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (967560346987/1000000000000:ℝ) ≤ taylorCos (638519503/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244969276491/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (125594677/625000000:ℝ) + taylorErr ≤ (244969276491/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (99800877673/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (99800877673/500000000000:ℝ) ≤ taylorSin (125594677/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (63160001041/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (638519503/2500000000:ℝ) + taylorErr ≤ (63160001041/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244969276491/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-967560346987/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-63160001041/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-99800877673/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15908914751161/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3990842767283/250000000000:ℝ) := by nlinarith
  have hp1 : (1645576959049/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26419356828163/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3337293209539/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5255360793329/1000000000000:ℝ) := by nlinarith
  have hN : (855096737473/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (254329215890801/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (855096737473/200000000000:ℝ) (254329215890801/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (706509509/10000000000000:ℝ) ≤ ((855096737473/200000000000:ℝ)/(254329215890801/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1407 (x : ℝ) (h₁ : (20743/4096:ℝ) ≤ x) (h₂ : x ≤ (41577/8192:ℝ)) : (71657399/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (63037023/312500000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1183082683/5000000000:ℝ) := by nlinarith
  have hc1 : (30379270917/31250000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (30379270917/31250000000:ℝ) ≤ taylorCos (1183082683/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (979723725129/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (63037023/312500000:ℝ) + taylorErr ≤ (979723725129/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (100176626447/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (100176626447/500000000000:ℝ) ≤ taylorSin (63037023/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (46882957577/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1183082683/5000000000:ℝ) + taylorErr ≤ (46882957577/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-979723725129/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-30379270917/31250000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-46882957577/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-100176626447/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3181936348311/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15944579804481/1000000000000:ℝ) := by nlinarith
  have hp1 : (26330500712799/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5277651462281/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1546449435077/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5275401468137/1000000000000:ℝ) := by nlinarith
  have hN : (134239929469/31250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507459250282927/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (134239929469/31250000000:ℝ) (507459250282927/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (71657399/1000000000000:ℝ) ≤ ((134239929469/31250000000:ℝ)/(507459250282927/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1408 (x : ℝ) (h₁ : (2593/512:ℝ) ≤ x) (h₂ : x ≤ (41599/8192:ℝ)) : (28871797/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/125000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2450534309/10000000000:ℝ) := by nlinarith
  have hc1 : (970124361323/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970124361323/1000000000000:ℝ) ≤ taylorCos (2450534309/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244892441987/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/125000000:ℝ) + taylorErr ≤ (244892441987/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (201104632579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (201104632579/1000000000000:ℝ) ≤ taylorSin (25310683/125000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (48521632403/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2450534309/10000000000:ℝ) + taylorErr ≤ (48521632403/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244892441987/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970124361323/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-48521632403/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-201104632579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15910448731949/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7976508349407/500000000000:ℝ) := by nlinarith
  have hp1 : (26331770080813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5280444071949/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6405394154593/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-661930118407/125000000000:ℝ) := by nlinarith
  have hN : (1078967794827/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507997483585277/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1078967794827/250000000000:ℝ) (507997483585277/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (28871797/400000000000:ℝ) ≤ ((1078967794827/250000000000:ℝ)/(507997483585277/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1409 (x : ℝ) (h₁ : (2593/512:ℝ) ≤ x) (h₂ : x ≤ (20815/4096:ℝ)) : (359821577/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/125000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (128470891/500000000:ℝ) := by nlinarith
  have hc1 : (193434332769/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (193434332769/200000000000:ℝ) ≤ taylorCos (128470891/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244892441987/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/125000000:ℝ) + taylorErr ≤ (244892441987/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (201104632579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (201104632579/1000000000000:ℝ) ≤ taylorSin (25310683/125000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (127061962669/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (128470891/500000000:ℝ) + taylorErr ≤ (127061962669/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244892441987/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-193434332769/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-127061962669/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-201104632579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15910448731949/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (49890328281/3125000000:ℝ) := by nlinarith
  have hp1 : (26331770080813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1056875822569/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1678608953913/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-661930118407/125000000000:ℝ) := by nlinarith
  have hN : (1078967794827/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508756386505923/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1078967794827/250000000000:ℝ) (508756386505923/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (359821577/5000000000000:ℝ) ≤ ((1078967794827/250000000000:ℝ)/(508756386505923/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1410 (x : ℝ) (h₁ : (2593/512:ℝ) ≤ x) (h₂ : x ≤ (20855/4096:ℝ)) : (357063571/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/125000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1438106989/5000000000:ℝ) := by nlinarith
  have hc1 : (958921328451/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (958921328451/1000000000000:ℝ) ≤ taylorCos (1438106989/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244892441987/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/125000000:ℝ) + taylorErr ≤ (244892441987/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (201104632579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (201104632579/1000000000000:ℝ) ≤ taylorSin (25310683/125000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (283672139603/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1438106989/5000000000:ℝ) + taylorErr ≤ (283672139603/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244892441987/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-958921328451/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-283672139603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-201104632579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15910448731949/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7997792332839/500000000000:ℝ) := by nlinarith
  have hp1 : (26331770080813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26472670285463/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7509559020883/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-661930118407/125000000000:ℝ) := by nlinarith
  have hN : (1078967794827/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (510717457593747/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1078967794827/250000000000:ℝ) (510717457593747/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (357063571/5000000000000:ℝ) ≤ ((1078967794827/250000000000:ℝ)/(510717457593747/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1411 (x : ℝ) (h₁ : (2593/512:ℝ) ≤ x) (h₂ : x ≤ (10483/2048:ℝ)) : (699094733/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/125000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (745514663/2000000000:ℝ) := by nlinarith
  have hc1 : (931326706803/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (931326706803/1000000000000:ℝ) ≤ taylorCos (745514663/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244892441987/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/125000000:ℝ) + taylorErr ≤ (244892441987/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (201104632579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (201104632579/1000000000000:ℝ) ≤ taylorSin (25310683/125000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (36418479187/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (745514663/2000000000:ℝ) + taylorErr ≤ (36418479187/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244892441987/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-931326706803/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-36418479187/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-201104632579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15910448731949/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8040360299703/500000000000:ℝ) := by nlinarith
  have hp1 : (26331770080813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26613570136899/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-387690300049/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-661930118407/125000000000:ℝ) := by nlinarith
  have hN : (1078967794827/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (516179149992321/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1078967794827/250000000000:ℝ) (516179149992321/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (699094733/10000000000000:ℝ) ≤ ((1078967794827/250000000000:ℝ)/(516179149992321/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1412 (x : ℝ) (h₁ : (2593/512:ℝ) ≤ x) (h₂ : x ≤ (5257/1024:ℝ)) : (345435191/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/125000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4203107359/10000000000:ℝ) := by nlinarith
  have hc1 : (456481094079/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (456481094079/500000000000:ℝ) ≤ taylorCos (4203107359/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244892441987/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/125000000:ℝ) + taylorErr ≤ (244892441987/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (201104632579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (201104632579/1000000000000:ℝ) ≤ taylorSin (25310683/125000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (81608833029/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4203107359/10000000000:ℝ) + taylorErr ≤ (81608833029/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244892441987/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-456481094079/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-81608833029/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-201104632579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15910448731949/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1612827400383/100000000000:ℝ) := by nlinarith
  have hp1 : (26331770080813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26692270954817/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-10891625417583/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-661930118407/125000000000:ℝ) := by nlinarith
  have hN : (1078967794827/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (259621222342619/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1078967794827/250000000000:ℝ) (259621222342619/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (345435191/5000000000000:ℝ) ≤ ((1078967794827/250000000000:ℝ)/(259621222342619/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1413 (x : ℝ) (h₁ : (2593/512:ℝ) ≤ x) (h₂ : x ≤ (333/64:ℝ)) : (327353763/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/125000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244892441987/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/125000000:ℝ) + taylorErr ≤ (244892441987/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (201104632579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (201104632579/1000000000000:ℝ) ≤ taylorSin (25310683/125000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244892441987/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-160641505837/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-297849653393/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-201104632579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15910448731949/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1634609927571/100000000000:ℝ) := by nlinarith
  have hp1 : (26331770080813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3381596434451/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-805765860733/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-661930118407/125000000000:ℝ) := by nlinarith
  have hN : (1078967794827/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (266694961531367/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1078967794827/250000000000:ℝ) (266694961531367/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (327353763/5000000000000:ℝ) ≤ ((1078967794827/250000000000:ℝ)/(266694961531367/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1414 (x : ℝ) (h₁ : (2593/512:ℝ) ≤ x) (h₂ : x ≤ (671/128:ℝ)) : (635374807/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/125000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1902136177/2500000000:ℝ) := by nlinarith
  have hc1 : (144849416121/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (144849416121/200000000000:ℝ) ≤ taylorCos (1902136177/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244892441987/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/125000000:ℝ) + taylorErr ≤ (244892441987/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (201104632579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (201104632579/1000000000000:ℝ) ≤ taylorSin (25310683/125000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (689540547001/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1902136177/2500000000:ℝ) + taylorErr ≤ (689540547001/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244892441987/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-144849416121/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-689540547001/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-201104632579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15910448731949/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16468817738741/1000000000000:ℝ) := by nlinarith
  have hp1 : (26331770080813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (340698379507/12500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-18794027757409/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-661930118407/125000000000:ℝ) := by nlinarith
  have hN : (1078967794827/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (541443915423741/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1078967794827/250000000000:ℝ) (541443915423741/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (635374807/10000000000000:ℝ) ≤ ((1078967794827/250000000000:ℝ)/(541443915423741/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1415 (x : ℝ) (h₁ : (41493/8192:ℝ) ≤ x) (h₂ : x ≤ (10401/2048:ℝ)) : (73842291/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2044029399/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2469709069/10000000000:ℝ) := by nlinarith
  have hc1 : (19393147657/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19393147657/20000000000:ℝ) ≤ taylorCos (2469709069/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (195836470819/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2044029399/10000000000:ℝ) + taylorErr ≤ (195836470819/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (25372820393/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (25372820393/125000000000:ℝ) ≤ taylorSin (2044029399/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (244467905059/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2469709069/10000000000:ℝ) + taylorErr ≤ (244467905059/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-195836470819/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-19393147657/20000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-244467905059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-25372820393/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7956183103967/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15954934174799/1000000000000:ℝ) := by nlinarith
  have hp1 : (1645933968803/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26405393779823/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1613817824903/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2672767166027/500000000000:ℝ) := by nlinarith
  have hN : (4366351977959/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508119849044339/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4366351977959/1000000000000:ℝ) (508119849044339/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (73842291/1000000000000:ℝ) ≤ ((4366351977959/1000000000000:ℝ)/(508119849044339/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1416 (x : ℝ) (h₁ : (41495/8192:ℝ) ≤ x) (h₂ : x ≤ (20783/4096:ℝ)) : (187000619/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2051699303/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1161990447/5000000000:ℝ) := by nlinarith
  have hc1 : (97311688309/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97311688309/100000000000:ℝ) ≤ taylorCos (1161990447/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (979026380417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2051699303/10000000000:ℝ) + taylorErr ≤ (979026380417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (20373352683/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (20373352683/100000000000:ℝ) ≤ taylorSin (2051699303/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (23031180709/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1161990447/5000000000:ℝ) + taylorErr ≤ (23031180709/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-979026380417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-97311688309/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-23031180709/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-20373352683/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1989141649791/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7970180678657/500000000000:ℝ) := by nlinarith
  have hp1 : (13168106434431/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5276255157447/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3037959649949/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2682784765559/500000000000:ℝ) := by nlinarith
  have hN : (4386543150701/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507190240403499/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4386543150701/1000000000000:ℝ) (507190240403499/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (187000619/2500000000000:ℝ) ≤ ((4386543150701/1000000000000:ℝ)/(507190240403499/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1417 (x : ℝ) (h₁ : (41497/8192:ℝ) ≤ x) (h₂ : x ≤ (10397/2048:ℝ)) : (753304927/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2059369207/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244717457701/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2059369207/10000000000:ℝ) + taylorErr ≤ (244717457701/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (25560546333/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (25560546333/125000000000:ℝ) ≤ taylorSin (2059369207/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (59628399277/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2408349837/10000000000:ℝ) + taylorErr ≤ (59628399277/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244717457701/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-971139156187/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59628399277/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-25560546333/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7956950094361/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (124599986341/7812500000:ℝ) := by nlinarith
  have hp1 : (6584370559219/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3299404854447/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6295623361199/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5385603480081/1000000000000:ℝ) := by nlinarith
  have hN : (4406733649277/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507728331343541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4406733649277/1000000000000:ℝ) (507728331343541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (753304927/10000000000000:ℝ) ≤ ((4406733649277/1000000000000:ℝ)/(507728331343541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1418 (x : ℝ) (h₁ : (10375/2048:ℝ) ≤ x) (h₂ : x ≤ (325/64:ℝ)) : (381405931/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2070874063/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (195726785341/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2070874063/10000000000:ℝ) + taylorErr ≤ (195726785341/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (25701301341/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (25701301341/125000000000:ℝ) ≤ taylorSin (2070874063/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-195726785341/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970031250923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-242980182203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-25701301341/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15915050674313/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15953400194011/1000000000000:ℝ) := by nlinarith
  have hp1 : (26339386288897/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26402855043761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6415370529213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5415652033183/1000000000000:ℝ) := by nlinarith
  have hN : (2218509053239/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508021955500541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2218509053239/500000000000:ℝ) (508021955500541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (381405931/5000000000000:ℝ) ≤ ((2218509053239/500000000000:ℝ)/(508021955500541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1419 (x : ℝ) (h₁ : (20751/4096:ℝ) ≤ x) (h₂ : x ≤ (10411/2048:ℝ)) : (766514859/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2078543967/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (655776787/2500000000:ℝ) := by nlinarith
  have hc1 : (965793356593/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (965793356593/1000000000000:ℝ) ≤ taylorCos (655776787/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (195695187531/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2078543967/10000000000:ℝ) + taylorErr ≤ (195695187531/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (103180476501/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (103180476501/500000000000:ℝ) ≤ taylorSin (2078543967/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (32414114683/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (655776787/2500000000:ℝ) + taylorErr ≤ (32414114683/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-195695187531/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-965793356593/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32414114683/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-103180476501/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15915817664707/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7985136991339/500000000000:ℝ) := by nlinarith
  have hp1 : (26340655656911/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13215390570221/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6853842968381/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5435682804057/1000000000000:ℝ) := by nlinarith
  have hN : (2228603433201/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127274825540901/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2228603433201/500000000000:ℝ) (127274825540901/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (766514859/10000000000000:ℝ) ≤ ((2228603433201/500000000000:ℝ)/(127274825540901/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1420 (x : ℝ) (h₁ : (20751/4096:ℝ) ≤ x) (h₂ : x ≤ (10421/2048:ℝ)) : (95446393/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2078543967/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2776505227/10000000000:ℝ) := by nlinarith
  have hc1 : (480851037121/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (480851037121/500000000000:ℝ) ≤ taylorCos (2776505227/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (195695187531/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2078543967/10000000000:ℝ) + taylorErr ≤ (195695187531/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (103180476501/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (103180476501/500000000000:ℝ) ≤ taylorSin (2078543967/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (13704845611/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2776505227/10000000000:ℝ) + taylorErr ≤ (13704845611/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-195695187531/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-480851037121/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13704845611/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-103180476501/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15915817664707/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15985613790557/1000000000000:ℝ) := by nlinarith
  have hp1 : (26340655656911/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26456168501061/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7251554095313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5435682804057/1000000000000:ℝ) := by nlinarith
  have hN : (2228603433201/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (510079696521693/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2228603433201/500000000000:ℝ) (510079696521693/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (95446393/1250000000000:ℝ) ≤ ((2228603433201/500000000000:ℝ)/(510079696521693/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1421 (x : ℝ) (h₁ : (1297/256:ℝ) ≤ x) (h₂ : x ≤ (41575/8192:ℝ)) : (778631889/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2086213871/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1179247731/5000000000:ℝ) := by nlinarith
  have hc1 : (38892647091/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38892647091/40000000000:ℝ) ≤ taylorCos (1179247731/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (978317372993/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2086213871/10000000000:ℝ) + taylorErr ≤ (978317372993/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (207111373879/1000000000000:ℝ) ≤ taylorSin (2086213871/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (116834549757/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1179247731/5000000000:ℝ) + taylorErr ≤ (116834549757/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-978317372993/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-38892647091/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-116834549757/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-207111373879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15916584655101/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15943812814087/1000000000000:ℝ) := by nlinarith
  have hp1 : (1053677000997/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13193493971687/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1233164742323/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5455712282529/1000000000000:ℝ) := by nlinarith
  have hN : (139918590923/31250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50741033410129/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (139918590923/31250000000:ℝ) (50741033410129/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (778631889/10000000000000:ℝ) ≤ ((139918590923/31250000000:ℝ)/(50741033410129/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1422 (x : ℝ) (h₁ : (1297/256:ℝ) ≤ x) (h₂ : x ≤ (41595/8192:ℝ)) : (388566237/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2086213871/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2435194501/10000000000:ℝ) := by nlinarith
  have hc1 : (485247688019/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (485247688019/500000000000:ℝ) ≤ taylorCos (2435194501/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (978317372993/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2086213871/10000000000:ℝ) + taylorErr ≤ (978317372993/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (207111373879/1000000000000:ℝ) ≤ taylorSin (2086213871/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (241119725011/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2435194501/10000000000:ℝ) + taylorErr ≤ (241119725011/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-978317372993/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-485247688019/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-241119725011/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-207111373879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15916584655101/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7975741359013/500000000000:ℝ) := by nlinarith
  have hp1 : (1053677000997/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26399681623683/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6365483973481/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5455712282529/1000000000000:ℝ) := by nlinarith
  have hN : (139918590923/31250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (101579920361393/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (139918590923/31250000000:ℝ) (101579920361393/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (388566237/5000000000000:ℝ) ≤ ((139918590923/31250000000:ℝ)/(101579920361393/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1423 (x : ℝ) (h₁ : (20753/4096:ℝ) ≤ x) (h₂ : x ≤ (41577/8192:ℝ)) : (785517521/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (83755351/400000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1183082683/5000000000:ℝ) := by nlinarith
  have hc1 : (30379270917/31250000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (30379270917/31250000000:ℝ) ≤ taylorCos (1183082683/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244539558203/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (83755351/400000000:ℝ) + taylorErr ≤ (244539558203/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (103930836459/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (103930836459/500000000000:ℝ) ≤ taylorSin (83755351/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (46882957577/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1183082683/5000000000:ℝ) + taylorErr ≤ (46882957577/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244539558203/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-30379270917/31250000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-46882957577/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-103930836459/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3183470329099/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15944579804481/1000000000000:ℝ) := by nlinarith
  have hp1 : (26343194392939/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5277651462281/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1546449435077/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-136893511413/25000000000:ℝ) := by nlinarith
  have hN : (1124395555927/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507459250282927/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1124395555927/250000000000:ℝ) (507459250282927/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (785517521/10000000000000:ℝ) ≤ ((1124395555927/250000000000:ℝ)/(507459250282927/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1424 (x : ℝ) (h₁ : (20753/4096:ℝ) ≤ x) (h₂ : x ≤ (41617/8192:ℝ)) : (782495959/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (83755351/400000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (503912689/2000000000:ℝ) := by nlinarith
  have hc1 : (968426558231/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968426558231/1000000000000:ℝ) ≤ taylorCos (503912689/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244539558203/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (83755351/400000000:ℝ) + taylorErr ≤ (244539558203/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (103930836459/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (103930836459/500000000000:ℝ) ≤ taylorSin (83755351/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (31162376669/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (503912689/2000000000:ℝ) + taylorErr ≤ (31162376669/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244539558203/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-968426558231/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31162376669/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-103930836459/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3183470329099/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (398997990309/25000000000:ℝ) := by nlinarith
  have hp1 : (26343194392939/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1056545786881/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6584895555767/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-136893511413/25000000000:ℝ) := by nlinarith
  have hN : (1124395555927/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508438068065987/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1124395555927/250000000000:ℝ) (508438068065987/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (782495959/10000000000000:ℝ) ≤ ((1124395555927/250000000000:ℝ)/(508438068065987/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1425 (x : ℝ) (h₁ : (20755/4096:ℝ) ≤ x) (h₂ : x ≤ (10423/2048:ℝ)) : (395439643/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2109223583/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1403592421/5000000000:ℝ) := by nlinarith
  have hc1 : (960856630841/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (960856630841/1000000000000:ℝ) ≤ taylorCos (1403592421/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (977838226267/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2109223583/10000000000:ℝ) + taylorErr ≤ (977838226267/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41872380743/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41872380743/200000000000:ℝ) ≤ taylorSin (2109223583/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-977838226267/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-960856630841/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-55409216517/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41872380743/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15918885626283/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15988681752133/1000000000000:ℝ) := by nlinarith
  have hp1 : (26345733128967/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5292249194637/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-733098453719/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5515792842647/1000000000000:ℝ) := by nlinarith
  have hN : (226897730819/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (255137944170991/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (226897730819/50000000000:ℝ) (255137944170991/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (395439643/5000000000000:ℝ) ≤ ((226897730819/50000000000:ℝ)/(255137944170991/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1426 (x : ℝ) (h₁ : (41515/8192:ℝ) ≤ x) (h₂ : x ≤ (20793/4096:ℝ)) : (816857769/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2128398343/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1200339967/5000000000:ℝ) := by nlinarith
  have hc1 : (194264361627/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194264361627/200000000000:ℝ) ≤ taylorCos (1200339967/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244358745617/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2128398343/10000000000:ℝ) + taylorErr ≤ (244358745617/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21123649901/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21123649901/100000000000:ℝ) ≤ taylorSin (2128398343/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-244358745617/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194264361627/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-237768672711/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21123649901/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3980200775567/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7974015630627/500000000000:ℝ) := by nlinarith
  have hp1 : (13174453274501/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5278793893509/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6275659087873/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-695731346519/125000000000:ℝ) := by nlinarith
  have hN : (1147103947421/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50767940221987/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1147103947421/250000000000:ℝ) (50767940221987/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (816857769/10000000000000:ℝ) ≤ ((1147103947421/250000000000:ℝ)/(50767940221987/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1427 (x : ℝ) (h₁ : (41515/8192:ℝ) ≤ x) (h₂ : x ≤ (20803/4096:ℝ)) : (815285161/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2128398343/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2477378973/10000000000:ℝ) := by nlinarith
  have hc1 : (969469593121/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969469593121/1000000000000:ℝ) ≤ taylorCos (2477378973/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244358745617/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2128398343/10000000000:ℝ) + taylorErr ≤ (244358745617/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21123649901/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21123649901/100000000000:ℝ) ≤ taylorSin (2128398343/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (49042310197/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2477378973/10000000000:ℝ) + taylorErr ≤ (49042310197/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-244358745617/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-969469593121/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-49042310197/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21123649901/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3980200775567/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15955701165193/1000000000000:ℝ) := by nlinarith
  have hp1 : (13174453274501/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13203331573927/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-809402353353/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-695731346519/125000000000:ℝ) := by nlinarith
  have hN : (1147103947421/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508168799345883/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1147103947421/250000000000:ℝ) (508168799345883/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (815285161/10000000000000:ℝ) ≤ ((1147103947421/250000000000:ℝ)/(508168799345883/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1428 (x : ℝ) (h₁ : (41517/8192:ℝ) ≤ x) (h₂ : x ≤ (5201/1024:ℝ)) : (51394681/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2136068247/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (195454535723/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2136068247/10000000000:ℝ) + taylorErr ≤ (195454535723/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (211986120051/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (211986120051/1000000000000:ℝ) ≤ taylorSin (2136068247/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (245955052659/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2485048877/10000000000:ℝ) + taylorErr ≤ (245955052659/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-195454535723/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-969281233079/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-245955052659/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-211986120051/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7960785046331/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15956468155587/1000000000000:ℝ) := by nlinarith
  have hp1 : (3293771989627/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5281586503177/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-81189555407/12500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5585871555309/1000000000000:ℝ) := by nlinarith
  have hN : (2304299438347/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127054438000131/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2304299438347/500000000000:ℝ) (127054438000131/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (51394681/625000000000:ℝ) ≤ ((2304299438347/500000000000:ℝ)/(127054438000131/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1429 (x : ℝ) (h₁ : (41519/8192:ℝ) ≤ x) (h₂ : x ≤ (20815/4096:ℝ)) : (103472171/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2143738151/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (128470891/500000000:ℝ) := by nlinarith
  have hc1 : (193434332769/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (193434332769/200000000000:ℝ) ≤ taylorCos (128470891/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (488554899929/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2143738151/10000000000:ℝ) + taylorErr ≤ (488554899929/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42547123277/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42547123277/200000000000:ℝ) ≤ taylorSin (2143738151/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (127061962669/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (128470891/500000000:ℝ) + taylorErr ≤ (127061962669/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-488554899929/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-193434332769/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-127061962669/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-42547123277/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3184467416611/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (49890328281/3125000000:ℝ) := by nlinarith
  have hp1 : (6587861321257/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1056875822569/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1678608953913/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2802945477673/500000000000:ℝ) := by nlinarith
  have hN : (144649411109/31250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508756386505923/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (144649411109/31250000000:ℝ) (508756386505923/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (103472171/1250000000000:ℝ) ≤ ((144649411109/31250000000:ℝ)/(508756386505923/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1430 (x : ℝ) (h₁ : (2595/512:ℝ) ≤ x) (h₂ : x ≤ (5205/1024:ℝ)) : (830590517/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2147573103/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (130388367/500000000:ℝ) := by nlinarith
  have hc1 : (60386875073/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (60386875073/62500000000:ℝ) ≤ taylorCos (130388367/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (977028144921/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2147573103/10000000000:ℝ) + taylorErr ≤ (977028144921/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4262206353/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4262206353/20000000000:ℝ) ≤ taylorSin (2147573103/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-977028144921/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-60386875073/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-128915552241/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4262206353/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3980680144563/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1596874000189/100000000000:ℝ) := by nlinarith
  have hp1 : (5270415993807/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1321412120219/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5323455413/781250000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5615900132939/1000000000000:ℝ) := by nlinarith
  have hN : (2319435994009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127250328623981/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2319435994009/500000000000:ℝ) (127250328623981/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (830590517/10000000000000:ℝ) ≤ ((2319435994009/500000000000:ℝ)/(127250328623981/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1431 (x : ℝ) (h₁ : (2595/512:ℝ) ≤ x) (h₂ : x ≤ (2605/512:ℝ)) : (827400419/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2147573103/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2761165419/10000000000:ℝ) := by nlinarith
  have hc1 : (192424280397/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192424280397/200000000000:ℝ) ≤ taylorCos (2761165419/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (977028144921/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2147573103/10000000000:ℝ) + taylorErr ≤ (977028144921/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4262206353/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4262206353/20000000000:ℝ) ≤ taylorSin (2147573103/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-977028144921/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-192424280397/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27262135779/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4262206353/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3980680144563/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15984079809769/1000000000000:ℝ) := by nlinarith
  have hp1 : (5270415993807/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26453629764999/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-450739029063/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5615900132939/1000000000000:ℝ) := by nlinarith
  have hN : (2319435994009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50998161473013/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2319435994009/500000000000:ℝ) (50998161473013/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (827400419/10000000000000:ℝ) ≤ ((2319435994009/500000000000:ℝ)/(50998161473013/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1432 (x : ℝ) (h₁ : (2595/512:ℝ) ≤ x) (h₂ : x ≤ (5215/1024:ℝ)) : (824225629/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2147573103/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2914563497/10000000000:ℝ) := by nlinarith
  have hc1 : (191565282153/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (191565282153/200000000000:ℝ) ≤ taylorCos (2914563497/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (977028144921/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2147573103/10000000000:ℝ) + taylorErr ≤ (977028144921/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4262206353/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4262206353/20000000000:ℝ) ≤ taylorSin (2147573103/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-977028144921/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-191565282153/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-287347461809/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4262206353/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3980680144563/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (999963726103/62500000000:ℝ) := by nlinarith
  have hp1 : (5270415993807/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13239508562809/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1902169590561/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5615900132939/1000000000000:ℝ) := by nlinarith
  have hN : (2319435994009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12774071405079/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2319435994009/500000000000:ℝ) (12774071405079/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (824225629/10000000000000:ℝ) ≤ ((2319435994009/500000000000:ℝ)/(12774071405079/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1433 (x : ℝ) (h₁ : (2595/512:ℝ) ≤ x) (h₂ : x ≤ (1305/256:ℝ)) : (821066057/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2147573103/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/1250000000:ℝ) := by nlinarith
  have hc1 : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190661207617/200000000000:ℝ) ≤ taylorCos (383495197/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (977028144921/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2147573103/10000000000:ℝ) + taylorErr ≤ (977028144921/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4262206353/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4262206353/20000000000:ℝ) ≤ taylorSin (2147573103/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-977028144921/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-190661207617/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-302005951603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4262206353/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3980680144563/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16014759425527/1000000000000:ℝ) := by nlinarith
  have hp1 : (5270415993807/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13252202243119/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4002243949269/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5615900132939/1000000000000:ℝ) := by nlinarith
  have hN : (2319435994009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127986259728753/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2319435994009/500000000000:ℝ) (127986259728753/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (821066057/10000000000000:ℝ) ≤ ((2319435994009/500000000000:ℝ)/(127986259728753/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1434 (x : ℝ) (h₁ : (2595/512:ℝ) ≤ x) (h₂ : x ≤ (2615/512:ℝ)) : (814792219/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2147573103/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1687378867/5000000000:ℝ) := by nlinarith
  have hc1 : (471796727939/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (471796727939/500000000000:ℝ) ≤ taylorCos (1687378867/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (977028144921/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2147573103/10000000000:ℝ) + taylorErr ≤ (977028144921/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4262206353/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4262206353/20000000000:ℝ) ≤ taylorSin (2147573103/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-977028144921/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-471796727939/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-82776577021/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4262206353/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3980680144563/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4011359760321/250000000000:ℝ) := by nlinarith
  have hp1 : (5270415993807/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13277589603737/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1099073418487/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5615900132939/1000000000000:ℝ) := by nlinarith
  have hN : (2319435994009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (256956114027561/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2319435994009/500000000000:ℝ) (256956114027561/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (814792219/10000000000000:ℝ) ≤ ((2319435994009/500000000000:ℝ)/(256956114027561/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1435 (x : ℝ) (h₁ : (2595/512:ℝ) ≤ x) (h₂ : x ≤ (655/128:ℝ)) : (404289107/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2147573103/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3681553891/10000000000:ℝ) := by nlinarith
  have hc1 : (93299279657/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (93299279657/100000000000:ℝ) ≤ taylorCos (3681553891/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (977028144921/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2147573103/10000000000:ℝ) + taylorErr ≤ (977028144921/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4262206353/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4262206353/20000000000:ℝ) ≤ taylorSin (2147573103/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-977028144921/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-93299279657/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89973759701/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4262206353/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3980680144563/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8038059328521/500000000000:ℝ) := by nlinarith
  have hp1 : (5270415993807/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26605953928713/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1196918852699/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5615900132939/1000000000000:ℝ) := by nlinarith
  have hN : (2319435994009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128970795537647/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2319435994009/500000000000:ℝ) (128970795537647/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (404289107/5000000000000:ℝ) ≤ ((2319435994009/500000000000:ℝ)/(128970795537647/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1436 (x : ℝ) (h₁ : (2595/512:ℝ) ≤ x) (h₂ : x ≤ (21/4:ℝ)) : (18241731/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2147573103/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (977028144921/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2147573103/10000000000:ℝ) + taylorErr ≤ (977028144921/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4262206353/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4262206353/20000000000:ℝ) ≤ taylorSin (2147573103/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-977028144921/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4262206353/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3980680144563/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16493361431347/1000000000000:ℝ) := by nlinarith
  have hp1 : (5270415993807/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (545929802751/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9650766670237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5615900132939/1000000000000:ℝ) := by nlinarith
  have hN : (2319435994009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (54306194261009/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2319435994009/500000000000:ℝ) (54306194261009/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (18241731/250000000000:ℝ) ≤ ((2319435994009/500000000000:ℝ)/(54306194261009/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1437 (x : ℝ) (h₁ : (10381/2048:ℝ) ≤ x) (h₂ : x ≤ (41635/8192:ℝ)) : (169102719/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (216291291/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (129429629/500000000:ℝ) := by nlinarith
  have hc1 : (483341304807/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483341304807/500000000000:ℝ) ≤ taylorCos (129429629/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (976700088411/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (216291291/1000000000:ℝ) + taylorErr ≤ (976700088411/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107304404321/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107304404321/500000000000:ℝ) ≤ taylorSin (216291291/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (255977985489/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (129429629/500000000:ℝ) + taylorErr ≤ (255977985489/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-976700088411/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-483341304807/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-255977985489/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107304404321/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (49763295497/3125000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3193364505181/200000000000:ℝ) := by nlinarith
  have hp1 : (26354618705063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13212534492151/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-676423592501/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5655933322507/1000000000000:ℝ) := by nlinarith
  have hN : (292452077131/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (101775768629499/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (292452077131/62500000000:ℝ) (101775768629499/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (169102719/2000000000000:ℝ) ≤ ((292452077131/62500000000:ℝ)/(101775768629499/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1438 (x : ℝ) (h₁ : (10381/2048:ℝ) ≤ x) (h₂ : x ≤ (20833/4096:ℝ)) : (168599037/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (216291291/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2707476091/10000000000:ℝ) := by nlinarith
  have hc1 : (481785606969/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (481785606969/500000000000:ℝ) ≤ taylorCos (2707476091/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (976700088411/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (216291291/1000000000:ℝ) + taylorErr ≤ (976700088411/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107304404321/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107304404321/500000000000:ℝ) ≤ taylorSin (216291291/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (66862972059/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2707476091/10000000000:ℝ) + taylorErr ≤ (66862972059/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-976700088411/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-481785606969/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-66862972059/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107304404321/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (49763295497/3125000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15978710877011/1000000000000:ℝ) := by nlinarith
  have hp1 : (26354618705063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13222372094391/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-884087095901/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5655933322507/1000000000000:ℝ) := by nlinarith
  have hN : (292452077131/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (25481920129111/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (292452077131/62500000000:ℝ) (25481920129111/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (168599037/2000000000000:ℝ) ≤ ((292452077131/62500000000:ℝ)/(25481920129111/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1439 (x : ℝ) (h₁ : (10381/2048:ℝ) ≤ x) (h₂ : x ≤ (20873/4096:ℝ)) : (418269633/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (216291291/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3014272249/10000000000:ℝ) := by nlinarith
  have hc1 : (954913740213/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (954913740213/1000000000000:ℝ) ≤ taylorCos (3014272249/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (976700088411/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (216291291/1000000000:ℝ) + taylorErr ≤ (976700088411/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107304404321/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107304404321/500000000000:ℝ) ≤ taylorSin (216291291/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (296883387503/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3014272249/10000000000:ℝ) + taylorErr ≤ (296883387503/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-976700088411/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-954913740213/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-296883387503/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107304404321/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (49763295497/3125000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16009390492769/1000000000000:ℝ) := by nlinarith
  have hp1 : (26354618705063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1324775945501/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7866079407657/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5655933322507/1000000000000:ℝ) := by nlinarith
  have hN : (292452077131/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20464046715997/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (292452077131/62500000000:ℝ) (20464046715997/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (418269633/5000000000000:ℝ) ≤ ((292452077131/62500000000:ℝ)/(20464046715997/40000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
