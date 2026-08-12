import RequestProject.Verify

/-!
# The band-dual verdict

`cap(995/1000, y) ≤ slack(y)` at the four recorded depths, from the checked
rational certificate.
-/

namespace BandDual

/-- **The computational implication**: at every recorded depth the band-dual cap
is at most the slack. -/
theorem cap_le_slack : ∀ d ∈ cert, capOf d ≤ slackF (yOf d) :=
  fun d hd => cap_le_slack_of_depOK (band_dual_closes d hd)

theorem yOf_dep0 : yOf dep0 = 1/50 := by norm_num [yOf, dep0]
theorem yOf_dep1 : yOf dep1 = 1/10 := by norm_num [yOf, dep1]
theorem yOf_dep2 : yOf dep2 = 3/10 := by norm_num [yOf, dep2]
theorem yOf_dep3 : yOf dep3 = 49/100 := by norm_num [yOf, dep3]

/-- The recorded depths are exactly `1/50, 1/10, 3/10, 49/100`. -/
theorem cert_depths : cert.map yOf = [1/50, 1/10, 3/10, 49/100] := by
  simp [cert, yOf_dep0, yOf_dep1, yOf_dep2, yOf_dep3]

/-- The four-depth statement, spelled out. -/
theorem cap_le_slack_at_depths :
    capOf dep0 ≤ slackF (1/50) ∧ capOf dep1 ≤ slackF (1/10) ∧
      capOf dep2 ≤ slackF (3/10) ∧ capOf dep3 ≤ slackF (49/100) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← yOf_dep0]; exact cap_le_slack dep0 (by simp [cert])
  · rw [← yOf_dep1]; exact cap_le_slack dep1 (by simp [cert])
  · rw [← yOf_dep2]; exact cap_le_slack dep2 (by simp [cert])
  · rw [← yOf_dep3]; exact cap_le_slack dep3 (by simp [cert])

/-- **No band was missed**: on `(0, G]` the field `f` is nonpositive off the
recorded bands.  This is a property of the recorded cover, not an extra
assumption. -/
theorem f_nonpos_off_bands : ∀ d ∈ cert, ∀ g : ℝ, 0 ≤ g → g ≤ 98 →
    fBig (yOf d) g ≤ 0 ∨ ∃ b ∈ d.bands, (b.lo:ℝ)/(SO:ℝ) ≤ g ∧ g ≤ (b.hi:ℝ)/(SO:ℝ) := by
  intro d hd g hg0 hg98
  have hchk := band_dual_closes d hd
  rw [depOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hbasic, hchain⟩, _⟩, _⟩, _⟩ := hchk
  have hc := ctx_of_basic hbasic
  have hS := SOR_pos
  have hcell : inCell 0 GSO g := by
    constructor
    · push_cast; nlinarith
    · rw [GSO]; push_cast; nlinarith
  rcases chainOK_neg hc d.segs d.bands 0 hchain g hcell with h | ⟨b, hb, hlo, hhi⟩
  · exact Or.inl h
  · refine Or.inr ⟨b, hb, ?_, ?_⟩
    · rw [div_le_iff₀ hS]; linarith
    · rw [le_div_iff₀ hS]; linarith

/-- **The band-dual verdict.**  `H1` (the Im-majorant), `H2` (spacing and
repulsion of the bands beyond `G`) and `H3` (the dual layer) are the three
structural hypotheses of the transplant-lemma chain; only `H3` enters the
derivation of the verdict from the certificate, `H1` and `H2` are the named
assumptions under which the recorded `C_up` and `P_lo` are the right constants
for the tail term. -/
theorem band_dual_verdict {X : Type} (D R : X → ℝ) (farBands : ℕ → ℝ × ℝ)
    (_hH1 : ∀ d ∈ cert, ∀ g : ℝ, 0 < g →
      |(Phi2 ((g:ℂ) + (yOf d : ℝ) * Complex.I)).im| ≤ (d.Cup:ℝ)/(SO:ℝ) * Acst / g)
    (_hH2space : ∀ d ∈ cert, ∀ i j : ℕ, i ≠ j →
      (d.Plo:ℝ)/(SO:ℝ) ≤ |(farBands i).1 - (farBands j).1|)
    (_hH2rep : ∀ d ∈ cert, ∀ i : ℕ,
      (d.K:ℝ)/(SO:ℝ) ≤ omgMinR ((farBands i).2 - (farBands i).1))
    (hH3 : ∀ d ∈ cert, ∀ x : X, D x - (1 - 995/1000) * R x ≤ capOf d) :
    ∀ d ∈ cert, ∀ x : X, D x - (1 - 995/1000) * R x ≤ slackF (yOf d) :=
  fun d hd x => le_trans (hH3 d hd x) (cap_le_slack d hd)

end BandDual
