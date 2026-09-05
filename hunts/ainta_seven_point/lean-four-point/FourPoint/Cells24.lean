import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_1440 (x : ℝ) (h₁ : (20763/4096:ℝ) ≤ x) (h₂ : x ≤ (41597/8192:ℝ)) : (42797433/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1085291407/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (488572881/2000000000:ℝ) := by nlinarith
  have hc1 : (194062030817/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194062030817/200000000000:ℝ) ≤ taylorCos (488572881/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (195307039649/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1085291407/5000000000:ℝ) + taylorErr ≤ (195307039649/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107678932517/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107678932517/500000000000:ℝ) ≤ taylorSin (1085291407/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (120932007327/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (488572881/2000000000:ℝ) + taylorErr ≤ (120932007327/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-195307039649/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194062030817/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-120932007327/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107678932517/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7962510774717/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (797612485421/50000000000:ℝ) := by nlinarith
  have hp1 : (26355888073077/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13200475495857/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-319271999877/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1418986946623/250000000000:ℝ) := by nlinarith
  have hN : (4699412588247/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126987135379893/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4699412588247/1000000000000:ℝ) (126987135379893/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (42797433/500000000000:ℝ) ≤ ((4699412588247/1000000000000:ℝ)/(126987135379893/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1441 (x : ℝ) (h₁ : (20763/4096:ℝ) ≤ x) (h₂ : x ≤ (41617/8192:ℝ)) : (85430123/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1085291407/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (503912689/2000000000:ℝ) := by nlinarith
  have hc1 : (968426558231/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968426558231/1000000000000:ℝ) ≤ taylorCos (503912689/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (195307039649/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1085291407/5000000000:ℝ) + taylorErr ≤ (195307039649/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107678932517/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107678932517/500000000000:ℝ) ≤ taylorSin (1085291407/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-195307039649/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-968426558231/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31162376669/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107678932517/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7962510774717/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (398997990309/25000000000:ℝ) := by nlinarith
  have hp1 : (26355888073077/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1056545786881/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6584895555767/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1418986946623/250000000000:ℝ) := by nlinarith
  have hN : (4699412588247/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508438068065987/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4699412588247/1000000000000:ℝ) (508438068065987/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (85430123/1000000000000:ℝ) ≤ ((4699412588247/1000000000000:ℝ)/(508438068065987/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1442 (x : ℝ) (h₁ : (5191/1024:ℝ) ≤ x) (h₂ : x ≤ (41639/8192:ℝ)) : (859830283/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (650983097/2500000000:ℝ) := by nlinarith
  have hc1 : (241572201777/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (241572201777/250000000000:ℝ) ≤ taylorCos (650983097/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (257460556303/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (650983097/2500000000:ℝ) + taylorErr ≤ (257460556303/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-976369733609/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-241572201777/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-257460556303/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13506674671/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3981447134957/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15968356506693/1000000000000:ℝ) := by nlinarith
  have hp1 : (26357157441091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6606901930091/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6804066585443/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2847980406473/500000000000:ℝ) := by nlinarith
  have hN : (4719591079337/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50897681904969/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4719591079337/1000000000000:ℝ) (50897681904969/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (859830283/10000000000000:ℝ) ≤ ((4719591079337/1000000000000:ℝ)/(50897681904969/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1443 (x : ℝ) (h₁ : (10383/2048:ℝ) ≤ x) (h₂ : x ≤ (5227/1024:ℝ)) : (429927023/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1096796263/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3282718887/10000000000:ℝ) := by nlinarith
  have hc1 : (946600910791/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (946600910791/1000000000000:ℝ) ≤ taylorCos (3282718887/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244009270329/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1096796263/5000000000:ℝ) + taylorErr ≤ (244009270329/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21760427231/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21760427231/100000000000:ℝ) ≤ taylorSin (1096796263/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-244009270329/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-946600910791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-322407681151/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21760427231/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1990915315077/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16036235156557/1000000000000:ℝ) := by nlinarith
  have hp1 : (26359696177119/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (414686668611/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8556682702791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2867991252467/500000000000:ℝ) := by nlinarith
  have hN : (2379972711809/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (51332167599279/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2379972711809/500000000000:ℝ) (51332167599279/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (429927023/5000000000000:ℝ) ≤ ((2379972711809/500000000000:ℝ)/(51332167599279/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1444 (x : ℝ) (h₁ : (10383/2048:ℝ) ≤ x) (h₂ : x ≤ (5237/1024:ℝ)) : (853292617/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1096796263/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (897378761/2500000000:ℝ) := by nlinarith
  have hc1 : (7314575507/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7314575507/7812500000:ℝ) ≤ taylorCos (897378761/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (244009270329/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1096796263/5000000000:ℝ) + taylorErr ≤ (244009270329/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21760427231/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21760427231/100000000000:ℝ) ≤ taylorSin (1096796263/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-244009270329/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7314575507/7812500000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-17564637919/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21760427231/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1990915315077/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3213382954463/200000000000:ℝ) := by nlinarith
  have hp1 : (26359696177119/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13295360756171/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4670563953693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2867991252467/500000000000:ℝ) := by nlinarith
  have hN : (2379972711809/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128822875150417/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2379972711809/500000000000:ℝ) (128822875150417/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (853292617/10000000000000:ℝ) ≤ ((2379972711809/500000000000:ℝ)/(128822875150417/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1445 (x : ℝ) (h₁ : (41535/8192:ℝ) ≤ x) (h₂ : x ≤ (20813/4096:ℝ)) : (177372543/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1102548691/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (638519503/2500000000:ℝ) := by nlinarith
  have hc1 : (967560346987/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (967560346987/1000000000000:ℝ) ≤ taylorCos (638519503/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (975786084837/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1102548691/5000000000:ℝ) + taylorErr ≤ (975786084837/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43745408931/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43745408931/200000000000:ℝ) ≤ taylorSin (1102548691/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-975786084837/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-967560346987/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-63160001041/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-43745408931/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15928473006207/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3990842767283/250000000000:ℝ) := by nlinarith
  have hp1 : (1318080011457/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26419356828163/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3337293209539/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-180187340953/31250000000:ℝ) := by nlinarith
  have hN : (4790208825659/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (254329215890801/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4790208825659/1000000000000:ℝ) (254329215890801/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (177372543/2000000000000:ℝ) ≤ ((4790208825659/1000000000000:ℝ)/(254329215890801/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1446 (x : ℝ) (h₁ : (41537/8192:ℝ) ≤ x) (h₂ : x ≤ (10407/2048:ℝ)) : (894176473/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1106383643/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (640436979/2500000000:ℝ) := by nlinarith
  have hc1 : (483683144977/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483683144977/500000000000:ℝ) ≤ taylorCos (640436979/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (975618036293/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1106383643/5000000000:ℝ) + taylorErr ≤ (975618036293/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219475398803/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219475398803/1000000000000:ℝ) ≤ taylorSin (1106383643/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (3167275491/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (640436979/2500000000:ℝ) + taylorErr ≤ (3167275491/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-975618036293/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-483683144977/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-3167275491/12500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219475398803/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15929239996601/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7982069029763/500000000000:ℝ) := by nlinarith
  have hp1 : (13181434798577/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13210313098097/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6694512144647/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2893000659213/500000000000:ℝ) := by nlinarith
  have hN : (4810383282133/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (254353703983607/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4810383282133/1000000000000:ℝ) (254353703983607/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (894176473/10000000000000:ℝ) ≤ ((4810383282133/1000000000000:ℝ)/(254353703983607/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1447 (x : ℝ) (h₁ : (41537/8192:ℝ) ≤ x) (h₂ : x ≤ (2603/512:ℝ)) : (55778547/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1106383643/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (975618036293/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1106383643/5000000000:ℝ) + taylorErr ≤ (975618036293/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219475398803/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219475398803/1000000000000:ℝ) ≤ taylorSin (1106383643/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-975618036293/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-482697219707/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-130397060129/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219475398803/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15929239996601/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7985903981733/500000000000:ℝ) := by nlinarith
  have hp1 : (13181434798577/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3304164984563/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1723413600673/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2893000659213/500000000000:ℝ) := by nlinarith
  have hN : (4810383282133/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (63649662405459/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4810383282133/1000000000000:ℝ) (63649662405459/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (55778547/625000000000:ℝ) ≤ ((4810383282133/1000000000000:ℝ)/(63649662405459/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1448 (x : ℝ) (h₁ : (20773/4096:ℝ) ≤ x) (h₂ : x ≤ (41657/8192:ℝ)) : (925654441/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1123640927/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2672961523/10000000000:ℝ) := by nlinarith
  have hc1 : (241122142861/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (241122142861/250000000000:ℝ) ≤ taylorCos (2672961523/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (487427358443/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1123640927/5000000000:ℝ) + taylorErr ≤ (487427358443/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (222841388361/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (222841388361/1000000000000:ℝ) ≤ taylorSin (1123640927/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (66031144349/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2672961523/10000000000:ℝ) + taylorErr ≤ (66031144349/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-487427358443/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-241122142861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-66031144349/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-222841388361/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7966345726687/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15975259420239/1000000000000:ℝ) := by nlinarith
  have hp1 : (26368581753217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6609758008161/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3491599081191/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5876011366997/1000000000000:ℝ) := by nlinarith
  have hN : (4901156650111/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50941782708787/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4901156650111/1000000000000:ℝ) (50941782708787/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (925654441/10000000000000:ℝ) ≤ ((4901156650111/1000000000000:ℝ)/(50941782708787/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1449 (x : ℝ) (h₁ : (20773/4096:ℝ) ≤ x) (h₂ : x ≤ (5211/1024:ℝ)) : (461449393/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1123640927/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1395922517/5000000000:ℝ) := by nlinarith
  have hc1 : (240320120887/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (240320120887/250000000000:ℝ) ≤ taylorCos (1395922517/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (487427358443/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1123640927/5000000000:ℝ) + taylorErr ≤ (487427358443/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (222841388361/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (222841388361/1000000000000:ℝ) ≤ taylorSin (1123640927/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (137785910789/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1395922517/5000000000:ℝ) + taylorErr ≤ (137785910789/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-487427358443/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-240320120887/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-137785910789/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-222841388361/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7966345726687/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3197429554269/200000000000:ℝ) := by nlinarith
  have hp1 : (26368581753217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26458707237123/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7291274149933/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5876011366997/1000000000000:ℝ) := by nlinarith
  have hN : (4901156650111/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (510177787725643/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4901156650111/1000000000000:ℝ) (510177787725643/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (461449393/5000000000000:ℝ) ≤ ((4901156650111/1000000000000:ℝ)/(510177787725643/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1450 (x : ℝ) (h₁ : (20775/4096:ℝ) ≤ x) (h₂ : x ≤ (10423/2048:ℝ)) : (937791853/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1131310831/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1403592421/5000000000:ℝ) := by nlinarith
  have hc1 : (960856630841/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (960856630841/1000000000000:ℝ) ≤ taylorCos (1403592421/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (487255867821/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1131310831/5000000000:ℝ) + taylorErr ≤ (487255867821/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (112168267003/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (112168267003/500000000000:ℝ) ≤ taylorSin (1131310831/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-487255867821/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-960856630841/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-55409216517/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-112168267003/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7967112717081/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15988681752133/1000000000000:ℝ) := by nlinarith
  have hp1 : (5274224097849/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5292249194637/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-733098453719/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5916005768411/1000000000000:ℝ) := by nlinarith
  have hN : (4941494032769/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (255137944170991/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4941494032769/1000000000000:ℝ) (255137944170991/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (937791853/10000000000000:ℝ) ≤ ((4941494032769/1000000000000:ℝ)/(255137944170991/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1451 (x : ℝ) (h₁ : (20775/4096:ℝ) ≤ x) (h₂ : x ≤ (10443/2048:ℝ)) : (930614427/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1131310831/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3113981/10000000:ℝ) := by nlinarith
  have hc1 : (1859191669/1953125000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (1859191669/1953125000:ℝ) ≤ taylorCos (3113981/10000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (487255867821/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1131310831/5000000000:ℝ) + taylorErr ≤ (487255867821/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (112168267003/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (112168267003/500000000000:ℝ) ≤ taylorSin (1131310831/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (306389797689/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3113981/10000000:ℝ) + taylorErr ≤ (306389797689/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-487255867821/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-1859191669/1953125000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-306389797689/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-112168267003/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7967112717081/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1601936136789/100000000000:ℝ) := by nlinarith
  have hp1 : (5274224097849/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13256010347211/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8123012656891/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5916005768411/1000000000000:ℝ) := by nlinarith
  have hN : (4941494032769/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (256119938635047/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4941494032769/1000000000000:ℝ) (256119938635047/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (930614427/10000000000000:ℝ) ≤ ((4941494032769/1000000000000:ℝ)/(256119938635047/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1452 (x : ℝ) (h₁ : (41555/8192:ℝ) ≤ x) (h₂ : x ≤ (20833/4096:ℝ)) : (479710493/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2281796421/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2707476091/10000000000:ℝ) := by nlinarith
  have hc1 : (481785606969/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (481785606969/500000000000:ℝ) ≤ taylorCos (2707476091/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (121759973063/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2281796421/10000000000:ℝ) + taylorErr ≤ (121759973063/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (226204723213/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (226204723213/1000000000000:ℝ) ≤ taylorSin (2281796421/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-121759973063/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-481785606969/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-66862972059/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-226204723213/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7968071455073/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15978710877011/1000000000000:ℝ) := by nlinarith
  have hp1 : (26374293909279/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13222372094391/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-884087095901/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2982994926843/500000000000:ℝ) := by nlinarith
  have hN : (2495955034591/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (25481920129111/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2495955034591/500000000000:ℝ) (25481920129111/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (479710493/5000000000000:ℝ) ≤ ((2495955034591/500000000000:ℝ)/(25481920129111/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1453 (x : ℝ) (h₁ : (41557/8192:ℝ) ≤ x) (h₂ : x ≤ (2603/512:ℝ)) : (484432071/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (91578653/400000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (194781200231/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (91578653/400000000:ℝ) + taylorErr ≤ (194781200231/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (113475883223/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (113475883223/500000000000:ℝ) ≤ taylorSin (91578653/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-194781200231/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-482697219707/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-130397060129/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-113475883223/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (796845495027/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7985903981733/500000000000:ℝ) := by nlinarith
  have hp1 : (26375563277293/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3304164984563/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1723413600673/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5985980676789/1000000000000:ℝ) := by nlinarith
  have hN : (2506037337817/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (63649662405459/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2506037337817/500000000000:ℝ) (63649662405459/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (484432071/5000000000000:ℝ) ≤ ((2506037337817/500000000000:ℝ)/(63649662405459/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1454 (x : ℝ) (h₁ : (41559/8192:ℝ) ≤ x) (h₂ : x ≤ (20835/4096:ℝ)) : (974610313/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2297136229/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2722815899/10000000000:ℝ) := by nlinarith
  have hc1 : (963159814353/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (963159814353/1000000000000:ℝ) ≤ taylorCos (2722815899/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (973731644883/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2297136229/10000000000:ℝ) + taylorErr ≤ (973731644883/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22769867617/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22769867617/100000000000:ℝ) ≤ taylorSin (2297136229/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (268929672731/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2722815899/10000000000:ℝ) + taylorErr ≤ (268929672731/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-973731644883/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-963159814353/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-268929672731/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-22769867617/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7968838445467/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15980244857799/1000000000000:ℝ) := by nlinarith
  have hp1 : (26376832645307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6611820731211/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7112459141603/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3002984937447/500000000000:ℝ) := by nlinarith
  have hN : (5032238230011/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (509736451430423/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5032238230011/1000000000000:ℝ) (509736451430423/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (974610313/10000000000000:ℝ) ≤ ((5032238230011/1000000000000:ℝ)/(509736451430423/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1455 (x : ℝ) (h₁ : (5195/1024:ℝ) ≤ x) (h₂ : x ≤ (5215/1024:ℝ)) : (486913799/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2300971181/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2914563497/10000000000:ℝ) := by nlinarith
  have hc1 : (191565282153/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (191565282153/200000000000:ℝ) ≤ taylorCos (2914563497/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (243411062983/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2300971181/10000000000:ℝ) + taylorErr ≤ (243411062983/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57018020207/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57018020207/250000000000:ℝ) ≤ taylorSin (2300971181/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-243411062983/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-191565282153/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-287347461809/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-57018020207/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15938060386131/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (999963726103/62500000000:ℝ) := by nlinarith
  have hp1 : (13188733664657/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13239508562809/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1902169590561/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6015963860769/1000000000000:ℝ) := by nlinarith
  have hN : (5042319608837/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12774071405079/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5042319608837/1000000000000:ℝ) (12774071405079/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (486913799/5000000000000:ℝ) ≤ ((5042319608837/1000000000000:ℝ)/(12774071405079/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1456 (x : ℝ) (h₁ : (5195/1024:ℝ) ≤ x) (h₂ : x ≤ (1305/256:ℝ)) : (194018909/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2300971181/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/1250000000:ℝ) := by nlinarith
  have hc1 : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190661207617/200000000000:ℝ) ≤ taylorCos (383495197/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (243411062983/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2300971181/10000000000:ℝ) + taylorErr ≤ (243411062983/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57018020207/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57018020207/250000000000:ℝ) ≤ taylorSin (2300971181/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-243411062983/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-190661207617/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-302005951603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-57018020207/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15938060386131/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16014759425527/1000000000000:ℝ) := by nlinarith
  have hp1 : (13188733664657/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13252202243119/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4002243949269/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6015963860769/1000000000000:ℝ) := by nlinarith
  have hN : (5042319608837/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127986259728753/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5042319608837/1000000000000:ℝ) (127986259728753/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (194018909/2000000000000:ℝ) ≤ ((5042319608837/1000000000000:ℝ)/(127986259728753/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1457 (x : ℝ) (h₁ : (5195/1024:ℝ) ≤ x) (h₂ : x ≤ (2633/512:ℝ)) : (936576257/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2300971181/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4479223901/10000000000:ℝ) := by nlinarith
  have hc1 : (28167151399/31250000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (28167151399/31250000000:ℝ) ≤ taylorCos (4479223901/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (243411062983/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2300971181/10000000000:ℝ) + taylorErr ≤ (243411062983/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57018020207/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57018020207/250000000000:ℝ) ≤ taylorSin (2300971181/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-243411062983/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-28167151399/31250000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-433093821149/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-57018020207/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15938060386131/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4038971414503/250000000000:ℝ) := by nlinarith
  have hp1 : (13188733664657/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6684492050983/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5790024409601/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6015963860769/1000000000000:ℝ) := by nlinarith
  have hN : (5042319608837/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (130256320697379/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5042319608837/1000000000000:ℝ) (130256320697379/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (936576257/10000000000000:ℝ) ≤ ((5042319608837/1000000000000:ℝ)/(130256320697379/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1458 (x : ℝ) (h₁ : (10391/2048:ℝ) ≤ x) (h₂ : x ≤ (20853/4096:ℝ)) : (990796899/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2316310989/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (286087417/1000000000:ℝ) := by nlinarith
  have hc1 : (38374213907/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38374213907/40000000000:ℝ) ≤ taylorCos (286087417/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (973293248333/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2316310989/10000000000:ℝ) + taylorErr ≤ (973293248333/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22956536349/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22956536349/100000000000:ℝ) ≤ taylorSin (2316310989/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (70550209879/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (286087417/1000000000:ℝ) + taylorErr ≤ (70550209879/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-973293248333/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-38374213907/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-70550209879/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-22956536349/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15939594366919/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1599405068489/100000000000:ℝ) := by nlinarith
  have hp1 : (13190003032671/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26470131549401/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-373494667267/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3027967840629/500000000000:ℝ) := by nlinarith
  have hN : (203305697317/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (510619314621661/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (203305697317/40000000000:ℝ) (510619314621661/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (990796899/10000000000000:ℝ) ≤ ((203305697317/40000000000:ℝ)/(510619314621661/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1459 (x : ℝ) (h₁ : (10391/2048:ℝ) ≤ x) (h₂ : x ≤ (20873/4096:ℝ)) : (986997519/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2316310989/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3014272249/10000000000:ℝ) := by nlinarith
  have hc1 : (954913740213/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (954913740213/1000000000000:ℝ) ≤ taylorCos (3014272249/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (973293248333/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2316310989/10000000000:ℝ) + taylorErr ≤ (973293248333/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22956536349/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22956536349/100000000000:ℝ) ≤ taylorSin (2316310989/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-973293248333/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-954913740213/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-296883387503/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-22956536349/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15939594366919/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16009390492769/1000000000000:ℝ) := by nlinarith
  have hp1 : (13190003032671/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1324775945501/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7866079407657/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3027967840629/500000000000:ℝ) := by nlinarith
  have hN : (203305697317/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20464046715997/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (203305697317/40000000000:ℝ) (20464046715997/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (986997519/10000000000000:ℝ) ≤ ((203305697317/40000000000:ℝ)/(20464046715997/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1460 (x : ℝ) (h₁ : (1299/256:ℝ) ≤ x) (h₂ : x ≤ (41679/8192:ℝ)) : (504597163/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2757330467/10000000000:ℝ) := by nlinarith
  have hc1 : (192445176043/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192445176043/200000000000:ℝ) ≤ taylorCos (2757330467/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (272252368811/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2757330467/10000000000:ℝ) + taylorErr ≤ (272252368811/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-972939954481/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-192445176043/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-272252368811/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-231058105961/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15941128347707/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3995924078643/250000000000:ℝ) := by nlinarith
  have hp1 : (2638254480137/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3306624385123/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-450118160809/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1219180166447/200000000000:ℝ) := by nlinarith
  have hN : (2561480438877/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (254978547876463/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2561480438877/500000000000:ℝ) (254978547876463/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (504597163/5000000000000:ℝ) ≤ ((2561480438877/500000000000:ℝ)/(254978547876463/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1461 (x : ℝ) (h₁ : (1299/256:ℝ) ≤ x) (h₂ : x ≤ (20855/4096:ℝ)) : (251547891/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1438106989/5000000000:ℝ) := by nlinarith
  have hc1 : (958921328451/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (958921328451/1000000000000:ℝ) ≤ taylorCos (1438106989/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-972939954481/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-958921328451/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-283672139603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-231058105961/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15941128347707/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7997792332839/500000000000:ℝ) := by nlinarith
  have hp1 : (2638254480137/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26472670285463/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7509559020883/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1219180166447/200000000000:ℝ) := by nlinarith
  have hN : (2561480438877/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (510717457593747/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2561480438877/500000000000:ℝ) (510717457593747/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (251547891/2500000000000:ℝ) ≤ ((2561480438877/500000000000:ℝ)/(510717457593747/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1462 (x : ℝ) (h₁ : (1299/256:ℝ) ≤ x) (h₂ : x ≤ (20875/4096:ℝ)) : (1002333521/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3029612057/10000000000:ℝ) := by nlinarith
  have hc1 : (954457203477/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (954457203477/1000000000000:ℝ) ≤ taylorCos (3029612057/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (298347856977/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3029612057/10000000000:ℝ) + taylorErr ≤ (298347856977/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-972939954481/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-954457203477/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-298347856977/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-231058105961/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15941128347707/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16010924473557/1000000000000:ℝ) := by nlinarith
  have hp1 : (2638254480137/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13249028823041/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3952819356381/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1219180166447/200000000000:ℝ) := by nlinarith
  have hN : (2561480438877/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (511699404995893/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2561480438877/500000000000:ℝ) (511699404995893/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1002333521/10000000000000:ℝ) ≤ ((2561480438877/500000000000:ℝ)/(511699404995893/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1463 (x : ℝ) (h₁ : (5197/1024:ℝ) ≤ x) (h₂ : x ≤ (1317/256:ℝ)) : (199185017/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2362330413/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4540583133/10000000000:ℝ) := by nlinarith
  have hc1 : (449337231697/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (449337231697/500000000000:ℝ) ≤ taylorCos (4540583133/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (972226499349/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2362330413/10000000000:ℝ) + taylorErr ≤ (972226499349/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3656905567/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3656905567/15625000000:ℝ) ≤ taylorSin (2362330413/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (219308120439/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4540583133/10000000000:ℝ) + taylorErr ≤ (219308120439/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-972226499349/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-449337231697/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-219308120439/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3656905567/15625000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15944196309283/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4040505395291/250000000000:ℝ) := by nlinarith
  have hp1 : (13193811136713/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1337406157409/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11732161225797/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6175810738661/1000000000000:ℝ) := by nlinarith
  have hN : (325224014957/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (260710941590011/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (325224014957/62500000000:ℝ) (260710941590011/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (199185017/2000000000000:ℝ) ≤ ((325224014957/62500000000:ℝ)/(260710941590011/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1464 (x : ℝ) (h₁ : (5197/1024:ℝ) ≤ x) (h₂ : x ≤ (661/128:ℝ)) : (245228749/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2362330413/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (644271931/1250000000:ℝ) := by nlinarith
  have hc1 : (870086988811/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (870086988811/1000000000000:ℝ) ≤ taylorCos (644271931/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (972226499349/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2362330413/10000000000:ℝ) + taylorErr ≤ (972226499349/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3656905567/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3656905567/15625000000:ℝ) ≤ taylorSin (2362330413/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (492898194553/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/1250000000:ℝ) + taylorErr ≤ (492898194553/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-972226499349/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-870086988811/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-492898194553/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3656905567/15625000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15944196309283/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16223380812679/1000000000000:ℝ) := by nlinarith
  have hp1 : (13193811136713/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5369934518131/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6617077572137/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6175810738661/1000000000000:ℝ) := by nlinarith
  have hN : (325224014957/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (525396169986403/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (325224014957/62500000000:ℝ) (525396169986403/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (245228749/2500000000000:ℝ) ≤ ((325224014957/62500000000:ℝ)/(525396169986403/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1465 (x : ℝ) (h₁ : (41577/8192:ℝ) ≤ x) (h₂ : x ≤ (5211/1024:ℝ)) : (1044341323/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (473233073/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1395922517/5000000000:ℝ) := by nlinarith
  have hc1 : (240320120887/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (240320120887/250000000000:ℝ) ≤ taylorCos (1395922517/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (243034168473/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (473233073/2000000000:ℝ) + taylorErr ≤ (243034168473/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (7325461977/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (7325461977/31250000000:ℝ) ≤ taylorSin (473233073/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (137785910789/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1395922517/5000000000:ℝ) + taylorErr ≤ (137785910789/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-243034168473/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-240320120887/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-137785910789/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-7325461977/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (49826811889/3125000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3197429554269/200000000000:ℝ) := by nlinarith
  have hp1 : (26388256957433/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26458707237123/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7291274149933/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6185797535391/1000000000000:ℝ) := by nlinarith
  have hN : (5213660861499/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (510177787725643/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5213660861499/1000000000000:ℝ) (510177787725643/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1044341323/10000000000000:ℝ) ≤ ((5213660861499/1000000000000:ℝ)/(510177787725643/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1466 (x : ℝ) (h₁ : (20793/4096:ℝ) ≤ x) (h₂ : x ≤ (163/32:ℝ)) : (215367333/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2400679933/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2945243113/10000000000:ℝ) := by nlinarith
  have hc1 : (956940333463/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956940333463/1000000000000:ℝ) ≤ taylorCos (2945243113/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (971321812683/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2400679933/10000000000:ℝ) + taylorErr ≤ (971321812683/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (23776866809/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (23776866809/100000000000:ℝ) ≤ taylorSin (2400679933/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-971321812683/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-956940333463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-290284679541/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-23776866809/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15948031261253/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2000310947403/125000000000:ℝ) := by nlinarith
  have hp1 : (3299246139187/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26484094597743/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-192198172831/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1568914720431/250000000000:ℝ) := by nlinarith
  have hN : (5304337069041/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (511159217446437/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5304337069041/1000000000000:ℝ) (511159217446437/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (215367333/2000000000000:ℝ) ≤ ((5304337069041/1000000000000:ℝ)/(511159217446437/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1467 (x : ℝ) (h₁ : (20793/4096:ℝ) ≤ x) (h₂ : x ≤ (2613/512:ℝ)) : (534301079/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2400679933/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3252039271/10000000000:ℝ) := by nlinarith
  have hc1 : (473792794367/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (473792794367/500000000000:ℝ) ≤ taylorCos (3252039271/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (971321812683/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2400679933/10000000000:ℝ) + taylorErr ≤ (971321812683/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (23776866809/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (23776866809/100000000000:ℝ) ≤ taylorSin (2400679933/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-971321812683/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-473792794367/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-319502033143/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-23776866809/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15948031261253/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16033167194981/1000000000000:ℝ) := by nlinarith
  have hp1 : (3299246139187/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26534869318979/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4238972348299/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1568914720431/250000000000:ℝ) := by nlinarith
  have hN : (5304337069041/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (51312490060443/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5304337069041/1000000000000:ℝ) (51312490060443/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (534301079/5000000000000:ℝ) ≤ ((5304337069041/1000000000000:ℝ)/(51312490060443/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1468 (x : ℝ) (h₁ : (20795/4096:ℝ) ≤ x) (h₂ : x ≤ (10433/2048:ℝ)) : (546419271/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (120800987/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2960582921/10000000000:ℝ) := by nlinarith
  have hc1 : (956493916629/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956493916629/1000000000000:ℝ) ≤ taylorCos (2960582921/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (242738984367/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (120800987/500000000:ℝ) + taylorErr ≤ (242738984367/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (23925837667/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (23925837667/100000000000:ℝ) ≤ taylorSin (120800987/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (145876132767/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2960582921/10000000000:ℝ) + taylorErr ≤ (145876132767/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-242738984367/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-956493916629/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-145876132767/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-23925837667/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (398739131051/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16004021560011/1000000000000:ℝ) := by nlinarith
  have hp1 : (13198253924761/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26486633333803/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3863767640753/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6315585617833/1000000000000:ℝ) := by nlinarith
  have hN : (1068925936073/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (255628706093297/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1068925936073/200000000000:ℝ) (255628706093297/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (546419271/5000000000000:ℝ) ≤ ((1068925936073/200000000000:ℝ)/(255628706093297/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1469 (x : ℝ) (h₁ : (41599/8192:ℝ) ≤ x) (h₂ : x ≤ (20855/4096:ℝ)) : (1132610991/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (612633577/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1438106989/5000000000:ℝ) := by nlinarith
  have hc1 : (958921328451/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (958921328451/1000000000000:ℝ) ≤ taylorCos (1438106989/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (60632772867/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (612633577/2500000000:ℝ) + taylorErr ≤ (60632772867/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (121304078697/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (121304078697/500000000000:ℝ) ≤ taylorSin (612633577/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-60632772867/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-958921328451/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-283672139603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-121304078697/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15953016698813/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7997792332839/500000000000:ℝ) := by nlinarith
  have hp1 : (13201110002793/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26472670285463/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7509559020883/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3202696973333/500000000000:ℝ) := by nlinarith
  have hN : (2717634790397/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (510717457593747/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2717634790397/500000000000:ℝ) (510717457593747/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1132610991/10000000000000:ℝ) ≤ ((2717634790397/500000000000:ℝ)/(510717457593747/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1470 (x : ℝ) (h₁ : (325/64:ℝ) ≤ x) (h₂ : x ≤ (2615/512:ℝ)) : (140340159/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1687378867/5000000000:ℝ) := by nlinarith
  have hc1 : (471796727939/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (471796727939/500000000000:ℝ) ≤ taylorCos (1687378867/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-60626953467/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-471796727939/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-82776577021/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-242980177581/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4011359760321/250000000000:ℝ) := by nlinarith
  have hp1 : (26402854689593/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13277589603737/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1099073418487/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3207685160561/500000000000:ℝ) := by nlinarith
  have hN : (108906781313/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (256956114027561/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (108906781313/20000000000:ℝ) (256956114027561/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (140340159/1250000000000:ℝ) ≤ ((108906781313/20000000000:ℝ)/(256956114027561/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1471 (x : ℝ) (h₁ : (325/64:ℝ) ≤ x) (h₂ : x ≤ (655/128:ℝ)) : (1114158849/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3681553891/10000000000:ℝ) := by nlinarith
  have hc1 : (93299279657/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (93299279657/100000000000:ℝ) ≤ taylorCos (3681553891/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-60626953467/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-93299279657/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89973759701/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-242980177581/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8038059328521/500000000000:ℝ) := by nlinarith
  have hp1 : (26402854689593/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26605953928713/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1196918852699/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3207685160561/500000000000:ℝ) := by nlinarith
  have hN : (108906781313/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128970795537647/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (108906781313/20000000000:ℝ) (128970795537647/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1114158849/10000000000000:ℝ) ≤ ((108906781313/20000000000:ℝ)/(128970795537647/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1472 (x : ℝ) (h₁ : (325/64:ℝ) ≤ x) (h₂ : x ≤ (1315/256:ℝ)) : (1097277581/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4295146207/10000000000:ℝ) := by nlinarith
  have hc1 : (90916798079/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (90916798079/100000000000:ℝ) ≤ taylorCos (4295146207/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-60626953467/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-90916798079/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-416429562443/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-242980177581/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16137477888557/1000000000000:ℝ) := by nlinarith
  have hp1 : (26402854689593/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6676875842797/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11121793942809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3207685160561/500000000000:ℝ) := by nlinarith
  have hN : (108906781313/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (519836385207333/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (108906781313/20000000000:ℝ) (519836385207333/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1097277581/10000000000000:ℝ) ≤ ((108906781313/20000000000:ℝ)/(519836385207333/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1473 (x : ℝ) (h₁ : (325/64:ℝ) ≤ x) (h₂ : x ≤ (165/32:ℝ)) : (270178737/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/5000000000:ℝ) := by nlinarith
  have hc1 : (17638425241/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (17638425241/20000000000:ℝ) ≤ taylorCos (2454369261/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-60626953467/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-17638425241/20000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-117849184789/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-242980177581/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16198837120073/1000000000000:ℝ) := by nlinarith
  have hp1 : (26402854689593/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5361810562733/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-12637700076223/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3207685160561/500000000000:ℝ) := by nlinarith
  have hN : (108906781313/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (52380464808531/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (108906781313/20000000000:ℝ) (52380464808531/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (270178737/2500000000000:ℝ) ≤ ((108906781313/20000000000:ℝ)/(52380464808531/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1474 (x : ℝ) (h₁ : (325/64:ℝ) ≤ x) (h₂ : x ≤ (665/128:ℝ)) : (1048517003/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/625000000:ℝ) := by nlinarith
  have hc1 : (817584810857/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (817584810857/1000000000000:ℝ) ≤ taylorCos (383495197/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-60626953467/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-817584810857/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-575808193717/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-242980177581/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127512152993/7812500000:ℝ) := by nlinarith
  have hp1 : (26402854689593/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (27012151698617/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-15553818277991/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3207685160561/500000000000:ℝ) := by nlinarith
  have hN : (108906781313/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (531786353304707/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (108906781313/20000000000:ℝ) (531786353304707/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1048517003/10000000000000:ℝ) ≤ ((108906781313/20000000000:ℝ)/(531786353304707/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1475 (x : ℝ) (h₁ : (325/64:ℝ) ≤ x) (h₂ : x ≤ (335/64:ℝ)) : (1017509707/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3681553891/5000000000:ℝ) := by nlinarith
  have hc1 : (74095112303/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (74095112303/100000000000:ℝ) ≤ taylorCos (3681553891/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-60626953467/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-74095112303/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-671558957117/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-242980177581/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3288854809227/200000000000:ℝ) := by nlinarith
  have hp1 : (26402854689593/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2721525058357/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-18276645299581/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3207685160561/500000000000:ℝ) := by nlinarith
  have hN : (108906781313/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (539828297808779/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (108906781313/20000000000:ℝ) (539828297808779/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1017509707/10000000000000:ℝ) ≤ ((108906781313/20000000000:ℝ)/(539828297808779/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1476 (x : ℝ) (h₁ : (325/64:ℝ) ≤ x) (h₂ : x ≤ (21/4:ℝ)) : (502714163/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-60626953467/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-242980177581/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16493361431347/1000000000000:ℝ) := by nlinarith
  have hp1 : (26402854689593/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (545929802751/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9650766670237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3207685160561/500000000000:ℝ) := by nlinarith
  have hN : (108906781313/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (54306194261009/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (108906781313/20000000000:ℝ) (54306194261009/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (502714163/5000000000000:ℝ) ≤ ((108906781313/20000000000:ℝ)/(54306194261009/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1477 (x : ℝ) (h₁ : (10401/2048:ℝ) ≤ x) (h₂ : x ≤ (1309/256:ℝ)) : (1134166649/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (617427267/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (889708857/2500000000:ℝ) := by nlinarith
  have hc1 : (937339009647/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (937339009647/1000000000000:ℝ) ≤ taylorCos (889708857/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (969657387399/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (617427267/2500000000:ℝ) + taylorErr ≤ (969657387399/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (122233950219/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (122233950219/500000000000:ℝ) ≤ taylorSin (617427267/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (348418682521/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/2500000000:ℝ) + taylorErr ≤ (348418682521/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-969657387399/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-937339009647/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-348418682521/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-122233950219/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7977467087399/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16063846810739/1000000000000:ℝ) := by nlinarith
  have hp1 : (26405393425621/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13292822020109/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4631467535233/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6455271091/1000000000:ℝ) := by nlinarith
  have hN : (5485613703601/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (25754717435889/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5485613703601/1000000000000:ℝ) (25754717435889/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1134166649/10000000000000:ℝ) ≤ ((5485613703601/1000000000000:ℝ)/(25754717435889/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1478 (x : ℝ) (h₁ : (10401/2048:ℝ) ≤ x) (h₂ : x ≤ (2623/512:ℝ)) : (1125526841/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (617427267/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1932815793/5000000000:ℝ) := by nlinarith
  have hc1 : (57888139991/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (57888139991/62500000000:ℝ) ≤ taylorCos (1932815793/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (969657387399/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (617427267/2500000000:ℝ) + taylorErr ≤ (969657387399/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (122233950219/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (122233950219/500000000000:ℝ) ≤ taylorSin (617427267/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-969657387399/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-57888139991/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-377007412527/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-122233950219/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7977467087399/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16094526426497/1000000000000:ℝ) := by nlinarith
  have hp1 : (26405393425621/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1664776172591/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-10042127316243/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6455271091/1000000000:ℝ) := by nlinarith
  have hN : (5485613703601/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (517067561786421/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5485613703601/1000000000000:ℝ) (517067561786421/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1125526841/10000000000000:ℝ) ≤ ((5485613703601/1000000000000:ℝ)/(517067561786421/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1479 (x : ℝ) (h₁ : (5201/1024:ℝ) ≤ x) (h₂ : x ≤ (20875/4096:ℝ)) : (583100681/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (621262219/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3029612057/10000000000:ℝ) := by nlinarith
  have hc1 : (954457203477/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (954457203477/1000000000000:ℝ) ≤ taylorCos (3029612057/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (242320309407/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (621262219/2500000000:ℝ) + taylorErr ≤ (242320309407/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (245955048037/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (245955048037/1000000000000:ℝ) ≤ taylorSin (621262219/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (298347856977/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3029612057/10000000000:ℝ) + taylorErr ≤ (298347856977/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-242320309407/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-954457203477/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-298347856977/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-245955048037/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7978234077793/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16010924473557/1000000000000:ℝ) := by nlinarith
  have hp1 : (26407932161649/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13249028823041/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3952819356381/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-405947763961/62500000000:ℝ) := by nlinarith
  have hN : (1381470746437/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (511699404995893/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1381470746437/250000000000:ℝ) (511699404995893/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (583100681/5000000000000:ℝ) ≤ ((1381470746437/250000000000:ℝ)/(511699404995893/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1480 (x : ℝ) (h₁ : (5201/1024:ℝ) ≤ x) (h₂ : x ≤ (20895/4096:ℝ)) : (1161734083/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (621262219/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (636602027/2000000000:ℝ) := by nlinarith
  have hc1 : (949768489893/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (949768489893/1000000000000:ℝ) ≤ taylorCos (636602027/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (242320309407/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (621262219/2500000000:ℝ) + taylorErr ≤ (242320309407/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (245955048037/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (245955048037/1000000000000:ℝ) ≤ taylorSin (621262219/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (312953371487/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/2000000000:ℝ) + taylorErr ≤ (312953371487/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-242320309407/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-949768489893/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-312953371487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-245955048037/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7978234077793/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4006566070359/250000000000:ℝ) := by nlinarith
  have hp1 : (26407932161649/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13261722503351/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4150300769149/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-405947763961/62500000000:ℝ) := by nlinarith
  have hN : (1381470746437/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (512682293636863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1381470746437/250000000000:ℝ) (512682293636863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1161734083/10000000000000:ℝ) ≤ ((1381470746437/250000000000:ℝ)/(512682293636863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1481 (x : ℝ) (h₁ : (10403/2048:ℝ) ≤ x) (h₂ : x ≤ (5237/1024:ℝ)) : (583409317/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (625097171/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (897378761/2500000000:ℝ) := by nlinarith
  have hc1 : (7314575507/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7314575507/7812500000:ℝ) ≤ taylorCos (897378761/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (193780561409/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (625097171/2500000000:ℝ) + taylorErr ≤ (193780561409/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (247441616881/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (247441616881/1000000000000:ℝ) ≤ taylorSin (625097171/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-193780561409/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7314575507/7812500000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-17564637919/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-247441616881/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7979001068187/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3213382954463/200000000000:ℝ) := by nlinarith
  have hp1 : (26410470897677/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13295360756171/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4670563953693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6535049621509/1000000000000:ℝ) := by nlinarith
  have hN : (10871380497/1953125000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128822875150417/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (10871380497/1953125000:ℝ) (128822875150417/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (583409317/5000000000000:ℝ) ≤ ((10871380497/1953125000:ℝ)/(128822875150417/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1482 (x : ℝ) (h₁ : (10403/2048:ℝ) ≤ x) (h₂ : x ≤ (5257/1024:ℝ)) : (1149129417/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (625097171/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4203107359/10000000000:ℝ) := by nlinarith
  have hc1 : (456481094079/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (456481094079/500000000000:ℝ) ≤ taylorCos (4203107359/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (193780561409/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (625097171/2500000000:ℝ) + taylorErr ≤ (193780561409/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (247441616881/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (247441616881/1000000000000:ℝ) ≤ taylorSin (625097171/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-193780561409/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-456481094079/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-81608833029/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-247441616881/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7979001068187/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1612827400383/100000000000:ℝ) := by nlinarith
  have hp1 : (26410470897677/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26692270954817/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-10891625417583/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6535049621509/1000000000000:ℝ) := by nlinarith
  have hN : (10871380497/1953125000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (259621222342619/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (10871380497/1953125000:ℝ) (259621222342619/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1149129417/10000000000000:ℝ) ≤ ((10871380497/1953125000:ℝ)/(259621222342619/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1483 (x : ℝ) (h₁ : (20815/4096:ℝ) ≤ x) (h₂ : x ≤ (10443/2048:ℝ)) : (251770887/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2569417819/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3113981/10000000:ℝ) := by nlinarith
  have hc1 : (1859191669/1953125000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (1859191669/1953125000:ℝ) ≤ taylorCos (3113981/10000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (193434333679/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2569417819/10000000000:ℝ) + taylorErr ≤ (193434333679/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (254123920717/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (254123920717/1000000000000:ℝ) ≤ taylorSin (2569417819/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (306389797689/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3113981/10000000:ℝ) + taylorErr ≤ (306389797689/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-193434333679/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-1859191669/1953125000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-306389797689/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-254123920717/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15964905049919/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1601936136789/100000000000:ℝ) := by nlinarith
  have hp1 : (26421895209801/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13256010347211/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8123012656891/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-209826112609/31250000000:ℝ) := by nlinarith
  have hN : (5747263935093/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (256119938635047/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5747263935093/1000000000000:ℝ) (256119938635047/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (251770887/2000000000000:ℝ) ≤ ((5747263935093/1000000000000:ℝ)/(256119938635047/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1484 (x : ℝ) (h₁ : (20815/4096:ℝ) ≤ x) (h₂ : x ≤ (10463/2048:ℝ)) : (1249238179/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2569417819/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3420777157/10000000000:ℝ) := by nlinarith
  have hc1 : (235514934377/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (235514934377/250000000000:ℝ) ≤ taylorCos (3420777157/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (193434333679/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2569417819/10000000000:ℝ) + taylorErr ≤ (193434333679/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (254123920717/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (254123920717/1000000000000:ℝ) ≤ taylorSin (2569417819/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (83861287337/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3420777157/10000000000:ℝ) + taylorErr ≤ (83861287337/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-193434333679/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-235514934377/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-83861287337/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-254123920717/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15964905049919/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (501563780739/31250000000:ℝ) := by nlinarith
  have hp1 : (26421895209801/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26562795415661/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8910360875307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-209826112609/31250000000:ℝ) := by nlinarith
  have hN : (5747263935093/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (514207631153561/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5747263935093/1000000000000:ℝ) (514207631153561/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1249238179/10000000000000:ℝ) ≤ ((5747263935093/1000000000000:ℝ)/(514207631153561/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1485 (x : ℝ) (h₁ : (1301/256:ℝ) ≤ x) (h₂ : x ≤ (2673/512:ℝ)) : (1153447231/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2577087723/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3466796581/5000000000:ℝ) := by nlinarith
  have hc1 : (769103335309/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (769103335309/1000000000000:ℝ) ≤ taylorCos (3466796581/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (241744118331/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2577087723/10000000000:ℝ) + taylorErr ≤ (241744118331/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (796455179/3125000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (796455179/3125000000:ℝ) ≤ taylorSin (2577087723/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (639124447183/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3466796581/5000000000:ℝ) + taylorErr ≤ (639124447183/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-241744118331/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-769103335309/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-639124447183/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-796455179/3125000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15965672040313/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8200661292037/500000000000:ℝ) := by nlinarith
  have hp1 : (5284632915563/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6786041493459/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1084281254517/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3367178603771/500000000000:ℝ) := by nlinarith
  have hN : (2883690367109/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (33562922813357/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2883690367109/500000000000:ℝ) (33562922813357/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1153447231/10000000000000:ℝ) ≤ ((2883690367109/500000000000:ℝ)/(33562922813357/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1486 (x : ℝ) (h₁ : (1301/256:ℝ) ≤ x) (h₂ : x ≤ (21/4:ℝ)) : (563934301/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2577087723/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (241744118331/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2577087723/10000000000:ℝ) + taylorErr ≤ (241744118331/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (796455179/3125000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (796455179/3125000000:ℝ) ≤ taylorSin (2577087723/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-241744118331/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-796455179/3125000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15965672040313/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16493361431347/1000000000000:ℝ) := by nlinarith
  have hp1 : (5284632915563/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (545929802751/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9650766670237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3367178603771/500000000000:ℝ) := by nlinarith
  have hN : (2883690367109/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (54306194261009/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2883690367109/500000000000:ℝ) (54306194261009/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (563934301/5000000000000:ℝ) ≤ ((2883690367109/500000000000:ℝ)/(54306194261009/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1487 (x : ℝ) (h₁ : (2603/512:ℝ) ≤ x) (h₂ : x ≤ (10483/2048:ℝ)) : (1319026531/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (527689391/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (745514663/2000000000:ℝ) := by nlinarith
  have hc1 : (931326706803/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (931326706803/1000000000000:ℝ) ≤ taylorCos (745514663/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (241348610991/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (527689391/2000000000:ℝ) + taylorErr ≤ (241348610991/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (260794115637/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (260794115637/1000000000000:ℝ) ≤ taylorSin (527689391/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-241348610991/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-931326706803/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-36418479187/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-260794115637/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3194361592693/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8040360299703/500000000000:ℝ) := by nlinarith
  have hp1 : (26433319521927/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26613570136899/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-387690300049/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6893654188071/1000000000000:ℝ) := by nlinarith
  have hN : (5928259744107/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (516179149992321/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5928259744107/1000000000000:ℝ) (516179149992321/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1319026531/10000000000000:ℝ) ≤ ((5928259744107/1000000000000:ℝ)/(516179149992321/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1488 (x : ℝ) (h₁ : (2603/512:ℝ) ≤ x) (h₂ : x ≤ (5277/1024:ℝ)) : (641911203/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (527689391/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2408349837/5000000000:ℝ) := by nlinarith
  have hc1 : (177244505577/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (177244505577/200000000000:ℝ) ≤ taylorCos (2408349837/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (241348610991/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (527689391/2000000000:ℝ) + taylorErr ≤ (241348610991/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (260794115637/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (260794115637/1000000000000:ℝ) ≤ taylorSin (527689391/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (463259785817/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2408349837/5000000000:ℝ) + taylorErr ≤ (463259785817/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-241348610991/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-177244505577/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-463259785817/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-260794115637/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3194361592693/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8094816617673/500000000000:ℝ) := by nlinarith
  have hp1 : (26433319521927/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13396910198647/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1241249949847/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6893654188071/1000000000000:ℝ) := by nlinarith
  have hN : (5928259744107/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (13080211214751/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5928259744107/1000000000000:ℝ) (13080211214751/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (641911203/5000000000000:ℝ) ≤ ((5928259744107/1000000000000:ℝ)/(13080211214751/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1489 (x : ℝ) (h₁ : (2603/512:ℝ) ≤ x) (h₂ : x ≤ (5297/1024:ℝ)) : (252901217/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (527689391/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (543029199/1000000000:ℝ) := by nlinarith
  have hc1 : (428073663033/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (428073663033/500000000000:ℝ) ≤ taylorCos (543029199/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (241348610991/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (527689391/2000000000:ℝ) + taylorErr ≤ (241348610991/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (260794115637/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (260794115637/1000000000000:ℝ) ≤ taylorSin (527689391/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (103346360271/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (543029199/1000000000:ℝ) + taylorErr ≤ (103346360271/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-241348610991/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-428073663033/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-103346360271/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-260794115637/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3194361592693/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16250992466861/1000000000000:ℝ) := by nlinarith
  have hp1 : (26433319521927/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2689536983977/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6948846452707/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6893654188071/1000000000000:ℝ) := by nlinarith
  have hN : (5928259744107/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (263594756157973/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5928259744107/1000000000000:ℝ) (263594756157973/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (252901217/2000000000000:ℝ) ≤ ((5928259744107/1000000000000:ℝ)/(263594756157973/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1490 (x : ℝ) (h₁ : (651/128:ℝ) ≤ x) (h₂ : x ≤ (2675/512:ℝ)) : (128184591/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (56450493/80000000:ℝ) := by nlinarith
  have hc1 : (761202383143/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (761202383143/1000000000000:ℝ) ≤ taylorCos (56450493/80000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (240944017019/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/5000000000:ℝ) + taylorErr ≤ (240944017019/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (266712755147/1000000000000:ℝ) ≤ taylorSin (1349903093/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (324257201669/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/80000000:ℝ) + taylorErr ≤ (324257201669/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-240944017019/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-761202383143/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-324257201669/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-266712755147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1997242985827/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16413594430377/1000000000000:ℝ) := by nlinarith
  have hp1 : (13221737233019/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (27164475862331/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-352331077117/20000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-55100093207/7812500000:ℝ) := by nlinarith
  have hN : (304451793121/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (268906082124903/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (304451793121/50000000000:ℝ) (268906082124903/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (128184591/1000000000000:ℝ) ≤ ((304451793121/50000000000:ℝ)/(268906082124903/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1491 (x : ℝ) (h₁ : (651/128:ℝ) ≤ x) (h₂ : x ≤ (21/4:ℝ)) : (1257182497/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (240944017019/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/5000000000:ℝ) + taylorErr ≤ (240944017019/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (266712755147/1000000000000:ℝ) ≤ taylorSin (1349903093/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-240944017019/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-266712755147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1997242985827/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16493361431347/1000000000000:ℝ) := by nlinarith
  have hp1 : (13221737233019/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (545929802751/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9650766670237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-55100093207/7812500000:ℝ) := by nlinarith
  have hN : (304451793121/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (54306194261009/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (304451793121/50000000000:ℝ) (54306194261009/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1257182497/10000000000000:ℝ) ≤ ((304451793121/50000000000:ℝ)/(54306194261009/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1492 (x : ℝ) (h₁ : (10423/2048:ℝ) ≤ x) (h₂ : x ≤ (5247/1024:ℝ)) : (189574513/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2807184841/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1948155601/5000000000:ℝ) := by nlinarith
  have hc1 : (925049238491/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (925049238491/1000000000000:ℝ) ≤ taylorCos (1948155601/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (960856635393/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2807184841/10000000000:ℝ) + taylorErr ≤ (960856635393/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (69261519491/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (69261519491/250000000000:ℝ) ≤ taylorSin (2807184841/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (379847211257/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1948155601/5000000000:ℝ) + taylorErr ≤ (379847211257/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-960856635393/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-925049238491/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-379847211257/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-69261519491/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3997170438033/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2012199298509/125000000000:ℝ) := by nlinarith
  have hp1 : (13230622809117/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26641496233579/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-10119698048039/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7330984316573/1000000000000:ℝ) := by nlinarith
  have hN : (318506384059/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20690603606631/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (318506384059/50000000000:ℝ) (20690603606631/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (189574513/1250000000000:ℝ) ≤ ((318506384059/50000000000:ℝ)/(20690603606631/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1493 (x : ℝ) (h₁ : (10423/2048:ℝ) ≤ x) (h₂ : x ≤ (5257/1024:ℝ)) : (1505067239/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2807184841/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4203107359/10000000000:ℝ) := by nlinarith
  have hc1 : (456481094079/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (456481094079/500000000000:ℝ) ≤ taylorCos (4203107359/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (960856635393/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2807184841/10000000000:ℝ) + taylorErr ≤ (960856635393/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (69261519491/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (69261519491/250000000000:ℝ) ≤ taylorSin (2807184841/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-960856635393/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-456481094079/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-81608833029/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-69261519491/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3997170438033/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1612827400383/100000000000:ℝ) := by nlinarith
  have hp1 : (13230622809117/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26692270954817/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-10891625417583/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7330984316573/1000000000000:ℝ) := by nlinarith
  have hN : (318506384059/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (259621222342619/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (318506384059/50000000000:ℝ) (259621222342619/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1505067239/10000000000000:ℝ) ≤ ((318506384059/50000000000:ℝ)/(259621222342619/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1494 (x : ℝ) (h₁ : (5215/1024:ℝ) ≤ x) (h₂ : x ≤ (2643/512:ℝ)) : (1604867299/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (636602027/1250000000:ℝ) := by nlinarith
  have hc1 : (174618995229/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (174618995229/200000000000:ℝ) ≤ taylorCos (636602027/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (478913207659/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (364320437/1250000000:ℝ) + taylorErr ≤ (478913207659/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (71836864297/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (71836864297/250000000000:ℝ) ≤ taylorSin (364320437/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (48755016243/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/1250000000:ℝ) + taylorErr ≤ (48755016243/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-478913207659/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-174618995229/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-48755016243/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-71836864297/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15999419617647/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16217244889527/1000000000000:ℝ) := by nlinarith
  have hp1 : (26479016770429/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26839517646407/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-13085611188049/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7608678137821/1000000000000:ℝ) := by nlinarith
  have hN : (6650851722503/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (26249903180689/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6650851722503/1000000000000:ℝ) (26249903180689/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1604867299/10000000000000:ℝ) ≤ ((6650851722503/1000000000000:ℝ)/(26249903180689/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1495 (x : ℝ) (h₁ : (5215/1024:ℝ) ≤ x) (h₂ : x ≤ (2653/512:ℝ)) : (1580761433/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (5706408531/10000000000:ℝ) := by nlinarith
  have hc1 : (841554975169/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (841554975169/1000000000000:ℝ) ≤ taylorCos (5706408531/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (478913207659/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (364320437/1250000000:ℝ) + taylorErr ≤ (478913207659/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (71836864297/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (71836864297/250000000000:ℝ) ≤ taylorSin (364320437/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-478913207659/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-841554975169/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-540171474997/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-71836864297/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15999419617647/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16278604121043/1000000000000:ℝ) := by nlinarith
  have hp1 : (26479016770429/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6735266772221/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3638198986849/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7608678137821/1000000000000:ℝ) := by nlinarith
  have hN : (6650851722503/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (528985904259277/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6650851722503/1000000000000:ℝ) (528985904259277/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1580761433/10000000000000:ℝ) ≤ ((6650851722503/1000000000000:ℝ)/(528985904259277/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1496 (x : ℝ) (h₁ : (5217/1024:ℝ) ≤ x) (h₂ : x ≤ (661/128:ℝ)) : (1680579671/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371990341/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (644271931/1250000000:ℝ) := by nlinarith
  have hc1 : (870086988811/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (870086988811/1000000000000:ℝ) ≤ taylorCos (644271931/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (956045253627/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371990341/1250000000:ℝ) + taylorErr ≤ (956045253627/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4581549381/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4581549381/15625000000:ℝ) ≤ taylorSin (371990341/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (492898194553/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/1250000000:ℝ) + taylorErr ≤ (492898194553/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-956045253627/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-870086988811/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-492898194553/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4581549381/15625000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8002777770399/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16223380812679/1000000000000:ℝ) := by nlinarith
  have hp1 : (26489171714539/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5369934518131/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6617077572137/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1941783172351/250000000000:ℝ) := by nlinarith
  have hN : (6811087435777/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (525396169986403/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6811087435777/1000000000000:ℝ) (525396169986403/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1680579671/10000000000000:ℝ) ≤ ((6811087435777/1000000000000:ℝ)/(525396169986403/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1497 (x : ℝ) (h₁ : (5217/1024:ℝ) ≤ x) (h₂ : x ≤ (333/64:ℝ)) : (815292227/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371990341/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (956045253627/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371990341/1250000000:ℝ) + taylorErr ≤ (956045253627/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4581549381/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4581549381/15625000000:ℝ) ≤ taylorSin (371990341/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-956045253627/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-160641505837/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-297849653393/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4581549381/15625000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8002777770399/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1634609927571/100000000000:ℝ) := by nlinarith
  have hp1 : (26489171714539/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3381596434451/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-805765860733/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1941783172351/250000000000:ℝ) := by nlinarith
  have hN : (6811087435777/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (266694961531367/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6811087435777/1000000000000:ℝ) (266694961531367/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (815292227/5000000000000:ℝ) ≤ ((6811087435777/1000000000000:ℝ)/(266694961531367/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1498 (x : ℝ) (h₁ : (2613/512:ℝ) ≤ x) (h₂ : x ≤ (671/128:ℝ)) : (1934302493/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (325203927/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1902136177/2500000000:ℝ) := by nlinarith
  have hc1 : (144849416121/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (144849416121/200000000000:ℝ) ≤ taylorCos (1902136177/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (94758559329/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (325203927/1000000000:ℝ) + taylorErr ≤ (94758559329/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79875507131/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79875507131/250000000000:ℝ) ≤ taylorSin (325203927/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-94758559329/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-144849416121/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-689540547001/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-79875507131/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (801658359749/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16468817738741/1000000000000:ℝ) := by nlinarith
  have hp1 : (165842931019/6250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (340698379507/12500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-18794027757409/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-8477944460309/1000000000000:ℝ) := by nlinarith
  have hN : (7530358867019/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (541443915423741/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7530358867019/1000000000000:ℝ) (541443915423741/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1934302493/10000000000000:ℝ) ≤ ((7530358867019/1000000000000:ℝ)/(541443915423741/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1499 (x : ℝ) (h₁ : (2613/512:ℝ) ≤ x) (h₂ : x ≤ (21/4:ℝ)) : (96139667/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (325203927/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (94758559329/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (325203927/1000000000:ℝ) + taylorErr ≤ (94758559329/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79875507131/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79875507131/250000000000:ℝ) ≤ taylorSin (325203927/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-94758559329/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-79875507131/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (801658359749/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16493361431347/1000000000000:ℝ) := by nlinarith
  have hp1 : (165842931019/6250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (545929802751/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9650766670237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-8477944460309/1000000000000:ℝ) := by nlinarith
  have hN : (7530358867019/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (54306194261009/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7530358867019/1000000000000:ℝ) (54306194261009/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (96139667/500000000000:ℝ) ≤ ((7530358867019/1000000000000:ℝ)/(54306194261009/100000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
