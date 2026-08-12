import Zeta23Ext.BandCert.Check

/-!
# The real-side quantities `cap`, `slack`, and the implication
`certificate checks → cap ≤ slack`
-/

namespace BandDual

set_option maxRecDepth 4000

/-! ### The dual quantities -/

/-- `sup f` over the band `[a,b]`. -/
noncomputable def bandSupR (y a b : ℝ) : ℝ := ⨆ g : Set.Icc a b, fBig y g

/-- `min ω²` over `[0,w]`, the same-band repulsion charge. -/
noncomputable def omgMinR (w : ℝ) : ℝ := ⨅ r : Set.Icc (0:ℝ) w, (omg r) ^ 2

/-- `max_{m ∈ ℕ} [m F - (1-θ) m (m-1) K]`, the occupancy maximum of one band. -/
noncomputable def bandTermR (θ F K : ℝ) : ℝ :=
  ⨆ m : ℕ, ((m:ℝ) * F - (1 - θ) * (m:ℝ) * ((m:ℝ) - 1) * K)

/-- `tail(G) = 8 C² (1/G² + 1/(P G))`. -/
noncomputable def tailR (C P G : ℝ) : ℝ := 8 * C ^ 2 * (1 / G ^ 2 + 1 / (P * G))

/-- `cap(θ, y) = 2 Σ_i max_m [m F_i - (1-θ) m(m-1) K_i] + tail(G)`. -/
noncomputable def capR (θ y : ℝ) (bands : List (ℝ × ℝ)) (C P G : ℝ) : ℝ :=
  2 * ((bands.map fun b => bandTermR θ (bandSupR y b.1 b.2) (omgMinR (b.2 - b.1))).sum)
    + tailR C P G

/-! ### Bounding the three pieces -/

theorem bandSup_le {y a b v : ℝ} (hab : a ≤ b) (h : ∀ g : ℝ, a ≤ g → g ≤ b → fBig y g ≤ v) :
    bandSupR y a b ≤ v := by
  haveI : Nonempty (Set.Icc a b) := (Set.nonempty_Icc.mpr hab).to_subtype
  exact ciSup_le fun g => h g g.2.1 g.2.2

theorem le_omgMin {w v : ℝ} (hw : 0 ≤ w) (h : ∀ r : ℝ, 0 ≤ r → r ≤ w → v ≤ (omg r) ^ 2) :
    v ≤ omgMinR w := by
  haveI : Nonempty (Set.Icc (0:ℝ) w) := (Set.nonempty_Icc.mpr hw).to_subtype
  exact le_ciInf fun r => h r r.2.1 r.2.2

theorem nat_sq_ge (n : ℕ) : 0 ≤ ((n:ℝ) - 1) * ((n:ℝ) - 2) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num
  · have h3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
    nlinarith

theorem nat_mul_pred_nonneg (n : ℕ) : 0 ≤ (n:ℝ) * ((n:ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · norm_num
  · have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem divSO_mono {a b : ℝ} (h : a ≤ b) : a / (SO:ℝ) ≤ b / (SO:ℝ) := by
  have hS := SOR_pos
  rw [div_le_div_iff₀ hS hS]
  nlinarith

/-- The square-completion bound, in scaled integer form. -/
theorem bandTerm_le {F K B : ℤ} (hF : 0 ≤ F) (hK : 0 ≤ K) (hchk : bChk F K B = true)
    {x k : ℝ} (hx : x ≤ (F:ℝ) / (SO:ℝ)) (hk : (K:ℝ) / (SO:ℝ) ≤ k) :
    bandTermR (995/1000) x k ≤ (B:ℝ) / (SO:ℝ) := by
  have hS := SOR_pos
  have hSne : (SO:ℝ) ≠ 0 := ne_of_gt hS
  have hFr : (0:ℝ) ≤ (F:ℝ) / (SO:ℝ) := div_nonneg (by exact_mod_cast hF) (le_of_lt hS)
  have hKr : (0:ℝ) ≤ (K:ℝ) / (SO:ℝ) := div_nonneg (by exact_mod_cast hK) (le_of_lt hS)
  have hk0 : 0 ≤ k := le_trans hKr hk
  refine ciSup_le fun m => ?_
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hmm : 0 ≤ (m:ℝ) * ((m:ℝ) - 1) := nat_mul_pred_nonneg m
  have step : (m:ℝ) * x - (1 - 995/1000) * (m:ℝ) * ((m:ℝ) - 1) * k
      ≤ (m:ℝ) * ((F:ℝ)/(SO:ℝ)) - (1 - 995/1000) * (m:ℝ) * ((m:ℝ) - 1) * ((K:ℝ)/(SO:ℝ)) := by
    have h1 : (m:ℝ) * x ≤ (m:ℝ) * ((F:ℝ)/(SO:ℝ)) := by nlinarith
    have h2 : (1 - 995/1000) * ((m:ℝ) * ((m:ℝ) - 1)) * ((K:ℝ)/(SO:ℝ))
        ≤ (1 - 995/1000) * ((m:ℝ) * ((m:ℝ) - 1)) * k := by nlinarith
    nlinarith
  refine le_trans step ?_
  rcases Bool.or_eq_true_iff.mp hchk with h | h
  · -- branch 1 : `F ≤ 2cK`, and `B = F`
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' : (B:ℝ) = (F:ℝ) := by exact_mod_cast h2
    rw [h2']
    have h1' : 100 * (F:ℝ) ≤ (K:ℝ) := by exact_mod_cast h1
    have h1'' : 100 * ((F:ℝ)/(SO:ℝ)) ≤ (K:ℝ)/(SO:ℝ) := by
      have he : 100 * ((F:ℝ)/(SO:ℝ)) = (100 * (F:ℝ))/(SO:ℝ) := by ring
      rw [he]; exact divSO_mono h1'
    nlinarith [mul_nonneg hFr (nat_sq_ge m), mul_nonneg hmm (sub_nonneg.mpr h1'')]
  · -- branch 2 : the exact square completion
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    obtain ⟨hKpos, hsq⟩ := h
    have hKpos' : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
    have hKr' : (0:ℝ) < (K:ℝ)/(SO:ℝ) := div_pos hKpos' hS
    have hsq' : (200 * (F:ℝ) + (K:ℝ)) ^ 2 ≤ 800 * (K:ℝ) * (B:ℝ) := by exact_mod_cast hsq
    have expand : ((F:ℝ)/(SO:ℝ) + ((K:ℝ)/(SO:ℝ))/200)^2
        = (200*(F:ℝ)+(K:ℝ))^2 / (200*(SO:ℝ))^2 := by field_simp
    have expand2 : (4/200) * ((K:ℝ)/(SO:ℝ)) * ((B:ℝ)/(SO:ℝ))
        = (800*(K:ℝ)*(B:ℝ))/(200*(SO:ℝ))^2 := by field_simp; ring
    have key : ((F:ℝ)/(SO:ℝ) + ((K:ℝ)/(SO:ℝ))/200)^2
        ≤ (4/200) * ((K:ℝ)/(SO:ℝ)) * ((B:ℝ)/(SO:ℝ)) := by
      rw [expand, expand2]
      apply div_le_div_of_nonneg_right hsq' (by positivity)
    nlinarith [sq_nonneg (2*(1/200)*((K:ℝ)/(SO:ℝ))*(m:ℝ) - ((F:ℝ)/(SO:ℝ) + ((K:ℝ)/(SO:ℝ))/200)),
      key, hKr']

/-- The recorded tail dominates `8 C² (1/G² + 1/(P G))`. -/
theorem tail_le {C P T : ℤ} (hP : 0 < P) (h : 8 * C ^ 2 * (P + 98 * SO) ≤ T * (P * 98 ^ 2 * SO)) :
    tailR ((C:ℝ)/(SO:ℝ)) ((P:ℝ)/(SO:ℝ)) 98 ≤ (T:ℝ)/(SO:ℝ) := by
  have hS := SOR_pos
  have hP' : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP
  have hSne : (SO:ℝ) ≠ 0 := ne_of_gt hS
  have hPne : (P:ℝ) ≠ 0 := ne_of_gt hP'
  have h' : 8 * (C:ℝ) ^ 2 * ((P:ℝ) + 98 * (SO:ℝ)) ≤ (T:ℝ) * ((P:ℝ) * 98 ^ 2 * (SO:ℝ)) := by
    exact_mod_cast h
  rw [tailR, le_div_iff₀ hS]
  have hexp : 8 * ((C:ℝ)/(SO:ℝ)) ^ 2 * (1 / (98:ℝ) ^ 2 + 1 / (((P:ℝ)/(SO:ℝ)) * 98)) * (SO:ℝ)
      = (8 * (C:ℝ) ^ 2 * ((P:ℝ) + 98 * (SO:ℝ))) / ((P:ℝ) * 98 ^ 2 * (SO:ℝ)) := by
    field_simp
  rw [hexp, div_le_iff₀ (by positivity)]
  exact h'

/-! ### Assembling a depth -/

theorem sum_map_div (l : List Bnd) (s : ℝ) :
    (l.map fun b => (b.B : ℝ) / s).sum = ((l.map Bnd.B).sum : ℤ) / s := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      push_cast
      ring

/-- Enclosure of `σ₂`. -/
theorem sigIv_mem {d : Dep} (hc : Ctx d) : (sigIv d).mem (sigma2 (yOf d)) := by
  have hS := SOR_pos
  have hy := hc.ypos
  have hyd : 0 < d.yd := hc.ydpos
  have hY2 : (EIv.ofQ (2 * d.yn) d.yd).mem (2 * yOf d) := by
    have := EIv.ofQ_mem (n := 2 * d.yn) hyd
    have heq : ((2 * d.yn : ℤ):ℝ) / ((d.yd : ℤ):ℝ) = 2 * yOf d := by
      rw [yOf]; push_cast; ring
    rwa [heq] at this
  have hhalf : (EIv.divInt (EIv.ofQ (2 * d.yn) d.yd) 2).mem (yOf d) := by
    have := EIv.divInt_mem (d := 2) (by norm_num) hY2
    have heq : 2 * yOf d / ((2:ℤ):ℝ) = yOf d := by push_cast; ring
    rwa [heq] at this
  have habs : |yOf d| ≤ 1 := by
    rw [abs_le]; constructor <;> [linarith [hc.ypos]; linarith [hc.yle]]
  have hsc := sinhCoshSmall_mem hhalf habs
  have hy2 : (2 : ℝ) * yOf d ≠ 0 := by positivity
  have hzero : (EIv.pt 0).mem (0:ℝ) := by simpa using EIv.pt_mem 0
  have hsh : ((sinhCoshSmall (EIv.divInt (EIv.ofQ (2 * d.yn) d.yd) 2)).1).mem
      (Real.sinh (2 * yOf d / 2)) := by
    have : 2 * yOf d / 2 = yOf d := by ring
    rw [this]; exact hsc.1
  have hch : ((sinhCoshSmall (EIv.divInt (EIv.ofQ (2 * d.yn) d.yd) 2)).2).mem
      (Real.cosh (2 * yOf d / 2)) := by
    have : 2 * yOf d / 2 = yOf d := by ring
    rw [this]; exact hsc.2
  have hp := phiC_mem hzero hY2 hy2 hsh hch
  have hzeq : ((0:ℝ) : ℂ) + ((2 * yOf d : ℝ) : ℂ) * Complex.I = 2 * (yOf d : ℝ) * Complex.I := by
    push_cast; ring
  rw [hzeq] at hp
  have hnum := EIv.sub_mem hp.1 AIV_mem
  have hden := EIv.mulInt_mem (k := 2) AIV_mem
  have hdiv := EIv.div_mem hnum hden
  have heq : ((Phi2 (2 * (yOf d : ℝ) * Complex.I)).re - Acst) / (Acst * ((2:ℤ):ℝ))
      = sigma2 (yOf d) := by
    rw [sigma2]; push_cast; ring_nf
  rw [heq] at hdiv
  exact hdiv

theorem slack_lower {d : Dep} (hc : Ctx d) (hs2 : 0 ≤ d.s2)
    (hsig : loGe (sigIv d) d.s2 = true)
    (hsl : d.slack * SO ≤ 8 * d.s2 * SO + 8 * d.s2 * d.s2) :
    (d.slack : ℝ) / (SO:ℝ) ≤ slackF (yOf d) := by
  have hS := SOR_pos
  have h1 : ((d.s2 : ℤ):ℝ) / (SO:ℝ) ≤ sigma2 (yOf d) := loGe_sound hsig (sigIv_mem hc)
  have h2 : (0:ℝ) ≤ ((d.s2 : ℤ):ℝ) / (SO:ℝ) := div_nonneg (by exact_mod_cast hs2) (le_of_lt hS)
  have h3 : ((d.slack : ℤ):ℝ) * (SO:ℝ) ≤ 8 * (d.s2:ℝ) * (SO:ℝ) + 8 * (d.s2:ℝ) * (d.s2:ℝ) := by
    exact_mod_cast hsl
  have hSne : (SO:ℝ) ≠ 0 := ne_of_gt hS
  have h4 : (d.slack : ℝ)/(SO:ℝ) ≤ 8 * ((d.s2:ℝ)/(SO:ℝ)) + 8 * ((d.s2:ℝ)/(SO:ℝ))^2 := by
    have he : 8 * ((d.s2:ℝ)/(SO:ℝ)) + 8 * ((d.s2:ℝ)/(SO:ℝ))^2
        = (8 * (d.s2:ℝ) * (SO:ℝ) + 8 * (d.s2:ℝ) * (d.s2:ℝ))/((SO:ℝ)*(SO:ℝ)) := by
      field_simp
    have he2 : (d.slack:ℝ)/(SO:ℝ) = ((d.slack:ℝ)*(SO:ℝ))/((SO:ℝ)*(SO:ℝ)) := by
      field_simp
    rw [he, he2]
    exact div_le_div_of_nonneg_right h3 (le_of_lt (mul_pos hS hS))
  refine le_trans h4 ?_
  rw [slackF]
  nlinarith

/-! ### The main implication -/

/-- The recorded bands of a depth, as real intervals. -/
noncomputable def bandsOf (d : Dep) : List (ℝ × ℝ) :=
  d.bands.map fun b => ((b.lo : ℝ)/(SO:ℝ), (b.hi : ℝ)/(SO:ℝ))

/-- `cap(995/1000, y)` for a recorded depth. -/
noncomputable def capOf (d : Dep) : ℝ :=
  capR (995/1000) (yOf d) (bandsOf d) ((d.Cup:ℝ)/(SO:ℝ)) ((d.Plo:ℝ)/(SO:ℝ)) 98

theorem cap_le_slack_of_depOK {d : Dep} (h : depOK d = true) : capOf d ≤ slackF (yOf d) := by
  rw [depOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hbasic, hchain⟩, homg⟩, hbands⟩, harith⟩ := h
  have hc := ctx_of_basic hbasic
  have hS := SOR_pos
  simp only [arithOK, Bool.and_eq_true, decide_eq_true_eq] at harith
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hK0, hs20⟩, hP0⟩, hw0⟩, hsig⟩, hsl⟩, htail⟩, hcap⟩, hcapsl⟩, hocc⟩, hgaps⟩ := harith
  simp only [bandsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hbands
  -- each band term is at most `B / 2^64`
  have hterm : ∀ b ∈ d.bands,
      bandTermR (995/1000) (bandSupR (yOf d) ((b.lo:ℝ)/(SO:ℝ)) ((b.hi:ℝ)/(SO:ℝ)))
        (omgMinR ((b.hi:ℝ)/(SO:ℝ) - (b.lo:ℝ)/(SO:ℝ))) ≤ (b.B : ℝ)/(SO:ℝ) := by
    intro b hb
    obtain ⟨⟨⟨⟨hF0, hlohi⟩, hlopos⟩, hwid⟩, hbchk⟩ := hbands b hb
    have hlohi' : (b.lo:ℝ) ≤ (b.hi:ℝ) := by exact_mod_cast hlohi
    have hwid' : (b.hi:ℝ) - (b.lo:ℝ) ≤ (d.w:ℝ) := by
      have : ((b.hi - b.lo : ℤ):ℝ) ≤ ((d.w : ℤ):ℝ) := by exact_mod_cast hwid
      push_cast at this; linarith
    have hab : (b.lo:ℝ)/(SO:ℝ) ≤ (b.hi:ℝ)/(SO:ℝ) := divSO_mono hlohi'
    have hFsup : bandSupR (yOf d) ((b.lo:ℝ)/(SO:ℝ)) ((b.hi:ℝ)/(SO:ℝ)) ≤ (b.F:ℝ)/(SO:ℝ) := by
      refine bandSup_le hab fun g h1 h2 => ?_
      refine chainOK_band hc d.segs d.bands 0 hchain b hb g ⟨?_, ?_⟩
      · rw [div_le_iff₀ hS] at h1; linarith [h1]
      · rw [le_div_iff₀ hS] at h2; linarith [h2]
    have hKmin : (d.K:ℝ)/(SO:ℝ) ≤ omgMinR ((b.hi:ℝ)/(SO:ℝ) - (b.lo:ℝ)/(SO:ℝ)) := by
      refine le_omgMin (by linarith) fun r h1 h2 => ?_
      refine omgOK_sound d.ocells 0 d.w homg r ⟨?_, ?_⟩
      · push_cast; nlinarith
      · rw [div_sub_div_same, le_div_iff₀ hS] at h2
        have : (SO:ℝ) * r ≤ (b.hi:ℝ) - (b.lo:ℝ) := by linarith
        linarith
    exact bandTerm_le hF0 hK0 hbchk hFsup hKmin
  have hsum : ((bandsOf d).map fun p =>
        bandTermR (995/1000) (bandSupR (yOf d) p.1 p.2) (omgMinR (p.2 - p.1))).sum
      ≤ (((d.bands.map Bnd.B).sum : ℤ) : ℝ)/(SO:ℝ) := by
    rw [bandsOf, List.map_map]
    refine le_trans (List.sum_le_sum (g := fun b => (b.B : ℝ)/(SO:ℝ)) ?_) ?_
    · intro b hb; exact hterm b hb
    · rw [sum_map_div]
  have htailb := tail_le hP0 htail
  have hcapR : capOf d ≤ (d.cap : ℝ)/(SO:ℝ) := by
    have hstep : 2 * ((((d.bands.map Bnd.B).sum : ℤ) : ℝ)/(SO:ℝ)) + (d.tail:ℝ)/(SO:ℝ)
        ≤ (d.cap:ℝ)/(SO:ℝ) := by
      have h1 : ((2 * ((d.bands.map Bnd.B).sum) + d.tail : ℤ) : ℝ) ≤ ((d.cap : ℤ):ℝ) := by
        exact_mod_cast hcap
      have h2 : 2 * ((((d.bands.map Bnd.B).sum : ℤ) : ℝ)/(SO:ℝ)) + (d.tail:ℝ)/(SO:ℝ)
          = ((2 * ((d.bands.map Bnd.B).sum) + d.tail : ℤ) : ℝ)/(SO:ℝ) := by push_cast; ring
      rw [h2]; exact divSO_mono h1
    calc capOf d ≤ 2 * ((((d.bands.map Bnd.B).sum : ℤ) : ℝ)/(SO:ℝ)) + (d.tail:ℝ)/(SO:ℝ) := by
          rw [capOf, capR]; linarith
      _ ≤ (d.cap:ℝ)/(SO:ℝ) := hstep
  have hcapsl' : (d.cap:ℝ)/(SO:ℝ) ≤ (d.slack:ℝ)/(SO:ℝ) := by
    have h' : ((d.cap : ℤ):ℝ) ≤ ((d.slack : ℤ):ℝ) := by exact_mod_cast hcapsl
    exact divSO_mono h'
  exact le_trans hcapR (le_trans hcapsl' (slack_lower hc hs20 hsig hsl))

end BandDual
