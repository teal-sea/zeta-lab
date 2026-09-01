import ZetaLean.WScratch.EForm3.FarField

/-!
# Counting over separated offsets

The total damage `∑_j (Qim y s_j ² - Qre y s_j ²)` of a `4`-separated configuration is
bounded by `0.1228 y²`, which is below the gain `Shq y / 2 ≥ 0.12986 y²`.  Offsets with
`|s_j| ≤ 28/5` contribute nothing (`no_damage`), and the remaining offsets on each side of `0`
dominate the arithmetic progression `28/5 + 4 m`.  Since `4 ≤ 2π`, the separation `2π` asked for
in `PROBLEM.md` is a special case (`separated_damage_of_le`).
-/

open scoped BigOperators Real
open MeasureTheory

set_option maxHeartbeats 1000000

namespace Retention

/-! ### An abstract rank-counting lemma -/

lemma rank_sum_le {S : Finset ℕ} {r : ℕ → ℕ} {F G : ℕ → ℝ} {B : ℝ}
    (hinj : ∀ i ∈ S, ∀ j ∈ S, r i = r j → i = j)
    (hlt : ∀ j ∈ S, r j < S.card)
    (hFG : ∀ j ∈ S, F j ≤ G (r j)) (hG : ∀ m, 0 ≤ G m)
    (hB : ∀ K, ∑ m ∈ Finset.range K, G m ≤ B) :
    ∑ j ∈ S, F j ≤ B := by
  have h1 : ∑ j ∈ S, F j ≤ ∑ j ∈ S, G (r j) := Finset.sum_le_sum hFG
  have h2 : ∑ m ∈ S.image r, G m = ∑ j ∈ S, G (r j) := Finset.sum_image hinj
  have h3 : S.image r ⊆ Finset.range S.card := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    exact Finset.mem_range.2 (hlt j hj)
  have h4 : ∑ m ∈ S.image r, G m ≤ ∑ m ∈ Finset.range S.card, G m :=
    Finset.sum_le_sum_of_subset_of_nonneg h3 (fun m _ _ => hG m)
  calc ∑ j ∈ S, F j ≤ ∑ j ∈ S, G (r j) := h1
    _ = ∑ m ∈ S.image r, G m := h2.symm
    _ ≤ ∑ m ∈ Finset.range S.card, G m := h4
    _ ≤ B := hB _

/-! ### Separated sequences -/

lemma sep_mono {x : ℕ → ℝ} {d : ℝ} {n : ℕ} (hsep : ∀ i, i+1 < n → x i + d ≤ x (i+1))
    {i j : ℕ} (hij : i ≤ j) (hj : j < n) : x i + ((j - i : ℕ) : ℝ) * d ≤ x j := by
  induction j with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge i (k+1) with h | h
    · have hik : i ≤ k := Nat.lt_succ_iff.1 h
      have hk : k < n := lt_trans (Nat.lt_succ_self k) hj
      have h1 := ih hik hk
      have h2 := hsep k hj
      have h3 : ((k + 1 - i : ℕ) : ℝ) = ((k - i : ℕ) : ℝ) + 1 := by
        have : k + 1 - i = (k - i) + 1 := by omega
        rw [this]; push_cast; ring
      rw [h3]
      nlinarith [h1, h2]
    · have : i = k + 1 := le_antisymm hij h
      subst this
      simp

/-! ### The majorant along the arithmetic progression -/

/-- `sm m = 28/5 + 4 m`, the `m`-th guaranteed offset on one side. -/
noncomputable def sm (m : ℕ) : ℝ := 28/5 + (m : ℝ) * 4

/-- The majorant term. -/
noncomputable def Gterm (m : ℕ) : ℝ := Wt ((sm m)^2 - 2)

lemma sm_ge (m : ℕ) : (28/5 : ℝ) ≤ sm m := by
  unfold sm
  have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  linarith

lemma sm_pos (m : ℕ) : (0:ℝ) < sm m := lt_of_lt_of_le (by norm_num) (sm_ge m)

lemma smw_pos (m : ℕ) : (0:ℝ) < (sm m)^2 - 2 := by
  have h := sm_ge m
  nlinarith

lemma Gterm_nonneg (m : ℕ) : 0 ≤ Gterm m := Wt_nonneg (smw_pos m)

lemma sm_succ (m : ℕ) : sm (m+1) = sm m + 4 := by
  unfold sm; push_cast; ring

lemma sm_ge_of_le {m : ℕ} {N : ℕ} (h : N ≤ m) : 28/5 + (N:ℝ) * 4 ≤ sm m := by
  unfold sm
  have : (N:ℝ) ≤ (m:ℝ) := by exact_mod_cast h
  linarith

/-- Bound for the tail terms. -/
lemma Wt_tail_le {w : ℝ} (hw : 1368 ≤ w) : Wt w ≤ (637/1000)/w := by
  have hw0 : (0:ℝ) < w := by linarith
  rw [Wt_eq hw0, div_le_div_iff₀ (by positivity) hw0]
  nlinarith [hw, sq_nonneg w, pow_pos hw0 3, pow_pos hw0 4]

lemma sm_nine : sm 9 = 41.6 := by unfold sm; norm_num

/-- The telescoping tail estimate, from `m = 9` on. -/
lemma tail_sum_le (K : ℕ) :
    ∑ m ∈ Finset.Ico 9 K, Gterm m ≤ (637/4000) * (1/(sm 9 - 2)) := by
  set C : ℝ := 637/4000 with hC
  have hC0 : 0 < C := by rw [hC]; norm_num
  have key : ∀ L : ℕ, ∑ m ∈ Finset.Ico 9 L, Gterm m + C * (1/(sm (max L 9) - 2))
      ≤ C * (1/(sm 9 - 2)) := by
    intro L
    induction L with
    | zero => simp
    | succ N ih =>
      rcases Nat.lt_or_ge N 9 with hN | hN
      · have h1 : Finset.Ico 9 (N+1) = ∅ := by
          apply Finset.Ico_eq_empty; omega
        have h2 : max (N+1) 9 = 9 := by omega
        rw [h1, h2]
        simp
      · have h2 : max (N+1) 9 = N+1 := by omega
        have h3 : max N 9 = N := by omega
        rw [h2] at *
        rw [h3] at ih
        rw [Finset.sum_Ico_succ_top (by omega : 9 ≤ N)]
        have hsN : (41.6 : ℝ) ≤ sm N := by
          have h := sm_ge_of_le hN
          norm_num at h ⊢
          linarith
        have hw : (1368:ℝ) ≤ (sm N)^2 - 2 := by nlinarith
        have hd1 : (0:ℝ) < sm N - 2 := by linarith
        have hd2 : (0:ℝ) < sm (N+1) - 2 := by rw [sm_succ]; linarith
        have hstep : Gterm N ≤ C * (1/(sm N - 2)) - C * (1/(sm (N+1) - 2)) := by
          have hdiff : C * (1/(sm N - 2)) - C * (1/(sm (N+1) - 2))
              = (637/1000) / ((sm N)^2 - 4) := by
            have he : sm (N+1) - 2 = sm N + 2 := by rw [sm_succ]; ring
            have ha1 : sm N - 2 ≠ 0 := ne_of_gt hd1
            have ha2 : sm N + 2 ≠ 0 := by positivity
            have hsq : (sm N)^2 - 4 = (sm N - 2) * (sm N + 2) := by ring
            rw [he, hC, hsq]
            field_simp
            ring
          rw [hdiff]
          have h1 : Gterm N ≤ (637/1000)/((sm N)^2 - 2) := Wt_tail_le hw
          have h2 : (637/1000)/((sm N)^2 - 2) ≤ (637/1000) / ((sm N)^2 - 4) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by nlinarith)
          linarith
        linarith [ih, hstep]
  have h := key K
  have hpos : 0 ≤ C * (1/(sm (max K 9) - 2)) := by
    have : (0:ℝ) < sm (max K 9) - 2 := by
      have := sm_ge (max K 9)
      linarith
    positivity
  linarith

/-- The full majorant sum, uniformly in `K`. -/
lemma Gsum_le (K : ℕ) : ∑ m ∈ Finset.range K, Gterm m ≤ 614/10000 := by
  have hsplit : ∑ m ∈ Finset.range K, Gterm m
      ≤ (∑ m ∈ Finset.range 9, Gterm m) + ∑ m ∈ Finset.Ico 9 K, Gterm m := by
    rcases Nat.lt_or_ge K 9 with h | h
    · have hsub : Finset.range K ⊆ Finset.range 9 := by
        intro m hm; rw [Finset.mem_range] at *; omega
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => Gterm_nonneg m)
      have h2 : (0:ℝ) ≤ ∑ m ∈ Finset.Ico 9 K, Gterm m :=
        Finset.sum_nonneg (fun m _ => Gterm_nonneg m)
      linarith
    · rw [← Finset.sum_range_add_sum_Ico _ h]
  -- the nine explicit terms
  have hexp : ∑ m ∈ Finset.range 9, Gterm m ≤ 573/10000 := by
    have bnd : ∀ (m : ℕ) (c v : ℝ), (sm m)^2 - 2 = c → Wt c ≤ v → Gterm m ≤ v := by
      intro m c v hc hv
      unfold Gterm
      rw [hc]
      exact hv
    have b0 : Gterm 0 ≤ 383/10000 := by
      refine bnd 0 29.36 _ (by unfold sm; norm_num) ?_
      rw [Wt]; norm_num
    have b1 : Gterm 1 ≤ 86/10000 := by
      refine bnd 1 90.16 _ (by unfold sm; norm_num) ?_
      rw [Wt]; norm_num
    have b2 : Gterm 2 ≤ 38/10000 := by
      refine bnd 2 182.96 _ (by unfold sm; norm_num) ?_
      rw [Wt]; norm_num
    have b3 : Gterm 3 ≤ 22/10000 := by
      refine bnd 3 307.76 _ (by unfold sm; norm_num) ?_
      rw [Wt]; norm_num
    have b4 : Gterm 4 ≤ 15/10000 := by
      refine bnd 4 464.56 _ (by unfold sm; norm_num) ?_
      rw [Wt]; norm_num
    have b5 : Gterm 5 ≤ 10/10000 := by
      refine bnd 5 653.36 _ (by unfold sm; norm_num) ?_
      rw [Wt]; norm_num
    have b6 : Gterm 6 ≤ 8/10000 := by
      refine bnd 6 874.16 _ (by unfold sm; norm_num) ?_
      rw [Wt]; norm_num
    have b7 : Gterm 7 ≤ 6/10000 := by
      refine bnd 7 1126.96 _ (by unfold sm; norm_num) ?_
      rw [Wt]; norm_num
    have b8 : Gterm 8 ≤ 5/10000 := by
      refine bnd 8 1411.76 _ (by unfold sm; norm_num) ?_
      rw [Wt]; norm_num
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    linarith
  have htail : ∑ m ∈ Finset.Ico 9 K, Gterm m ≤ 41/10000 := by
    refine le_trans (tail_sum_le K) ?_
    rw [sm_nine]
    norm_num
  linarith

/-! ### Rank helpers -/

lemma filter_card_lt {S : Finset ℕ} {j : ℕ} (hj : j ∈ S) {P : ℕ → Prop} [DecidablePred P]
    (hPj : ¬ P j) : (S.filter P).card < S.card := by
  have hsub : S.filter P ⊆ S.erase j := by
    intro i hi
    rw [Finset.mem_filter] at hi
    refine Finset.mem_erase.2 ⟨?_, hi.1⟩
    rintro rfl
    exact hPj hi.2
  have h1 := Finset.card_le_card hsub
  have h2 : (S.erase j).card < S.card := Finset.card_erase_lt_of_mem hj
  omega

lemma rank_lt_inc {S : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hij : i < j) :
    (S.filter (fun k => k < i)).card < (S.filter (fun k => k < j)).card := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_trans hk.2 hij⟩
  · intro hsub
    have hmem : i ∈ S.filter (fun k => k < i) := hsub (Finset.mem_filter.2 ⟨hi, hij⟩)
    rw [Finset.mem_filter] at hmem
    exact absurd hmem.2 (lt_irrefl i)

lemma rank_lt_dec {S : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hij : j < i) :
    (S.filter (fun k => i < k)).card < (S.filter (fun k => j < k)).card := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_trans hij hk.2⟩
  · intro hsub
    have hmem : i ∈ S.filter (fun k => i < k) := hsub (Finset.mem_filter.2 ⟨hi, hij⟩)
    rw [Finset.mem_filter] at hmem
    exact absurd hmem.2 (lt_irrefl i)

/-! ### The separated counting theorem -/

/-- With offsets separated by at least `4`, the total damage is at most `0.1228 y²`. -/
theorem separated_damage {n : ℕ} {x : ℕ → ℝ} {y t : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2)
    (hsep : ∀ i, i + 1 < n → x i + 4 ≤ x (i+1)) :
    ∑ j ∈ Finset.range n, (Qim y (x j - t) ^ 2 - Qre y (x j - t) ^ 2) ≤ (1228/10000) * y^2 := by
  classical
  set D : ℕ → ℝ := fun j => Qim y (x j - t) ^ 2 - Qre y (x j - t) ^ 2 with hDdef
  set Jp := (Finset.range n).filter (fun j => 28/5 < x j - t) with hJpdef
  set Jm := (Finset.range n).filter (fun j => x j - t < -(28/5)) with hJmdef
  have hy2 : (0:ℝ) ≤ y^2 := sq_nonneg y
  have hpi0 : (0:ℝ) < (4:ℝ) := by norm_num
  have hside : ∀ (S : Finset ℕ) (r : ℕ → ℕ),
      (∀ i ∈ S, ∀ j ∈ S, r i = r j → i = j) → (∀ j ∈ S, r j < S.card) →
      (∀ j ∈ S, D j ≤ y^2 * Gterm (r j)) → ∑ j ∈ S, D j ≤ y^2 * (614/10000) := by
    intro S r h1 h2 h3
    refine rank_sum_le h1 h2 h3 (fun m => mul_nonneg hy2 (Gterm_nonneg m)) ?_
    intro K
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Gsum_le K) hy2
  have hJpsub : Jp ⊆ Finset.range n := Finset.filter_subset _ _
  have hJmsub : Jm ⊆ Finset.range n := Finset.filter_subset _ _
  -- the positive side
  have hJp_bound : ∑ j ∈ Jp, D j ≤ y^2 * (614/10000) := by
    rcases Finset.eq_empty_or_nonempty Jp with he | hne
    · rw [he, Finset.sum_empty]
      positivity
    · refine hside Jp (fun j => (Jp.filter (fun k => k < j)).card) ?_ ?_ ?_
      · intro i hi j hj hr
        by_contra hne'
        rcases Nat.lt_or_ge i j with h | h
        · exact absurd hr (Nat.ne_of_lt (rank_lt_inc hi h))
        · have hji : j < i := by omega
          exact absurd hr.symm (Nat.ne_of_lt (rank_lt_inc hj hji))
      · intro j hj
        exact filter_card_lt hj (by simp)
      · intro j hj
        have hjn : j < n := Finset.mem_range.1 (hJpsub hj)
        have hjs : (28/5:ℝ) < x j - t := (Finset.mem_filter.1 hj).2
        have hi0 : Jp.min' hne ∈ Jp := Jp.min'_mem hne
        have hi0s : (28/5:ℝ) < x (Jp.min' hne) - t := (Finset.mem_filter.1 hi0).2
        have hle : Jp.min' hne ≤ j := Finset.min'_le _ _ hj
        have hstep := sep_mono hsep hle hjn
        have hrk : (Jp.filter (fun k => k < j)).card ≤ j - Jp.min' hne := by
          have hsub : Jp.filter (fun k => k < j) ⊆ Finset.Ico (Jp.min' hne) j := by
            intro k hk
            rw [Finset.mem_filter] at hk
            exact Finset.mem_Ico.2 ⟨Finset.min'_le _ _ hk.1, hk.2⟩
          have := Finset.card_le_card hsub
          simpa [Nat.card_Ico] using this
        have hcast : (((Jp.filter (fun k => k < j)).card : ℕ) : ℝ)
            ≤ ((j - Jp.min' hne : ℕ) : ℝ) := by exact_mod_cast hrk
        have hmul := mul_le_mul_of_nonneg_right hcast hpi0.le
        have hsm : sm ((Jp.filter (fun k => k < j)).card) ≤ x j - t := by
          unfold sm
          linarith only [hstep, hi0s, hmul]
        have hs1 : (28/5:ℝ) ≤ x j - t := le_of_lt hjs
        have h1 : Qim y (x j - t)^2 ≤ y^2 * Wt ((x j - t)^2 - 2) := Qim_far_sq hy0 hy hs1
        have hpos := sm_ge ((Jp.filter (fun k => k < j)).card)
        have h2 : Wt ((x j - t)^2 - 2) ≤ Gterm ((Jp.filter (fun k => k < j)).card) := by
          refine Wt_anti (smw_pos _) ?_
          nlinarith only [hsm, hpos]
        have h3 : D j ≤ Qim y (x j - t)^2 := by
          simp only [hDdef]
          nlinarith only [sq_nonneg (Qre y (x j - t))]
        calc D j ≤ Qim y (x j - t)^2 := h3
          _ ≤ y^2 * Wt ((x j - t)^2 - 2) := h1
          _ ≤ y^2 * Gterm ((Jp.filter (fun k => k < j)).card) :=
              mul_le_mul_of_nonneg_left h2 hy2
  -- the negative side
  have hJm_bound : ∑ j ∈ Jm, D j ≤ y^2 * (614/10000) := by
    rcases Finset.eq_empty_or_nonempty Jm with he | hne
    · rw [he, Finset.sum_empty]
      positivity
    · refine hside Jm (fun j => (Jm.filter (fun k => j < k)).card) ?_ ?_ ?_
      · intro i hi j hj hr
        by_contra hne'
        rcases Nat.lt_or_ge i j with h | h
        · exact absurd hr.symm (Nat.ne_of_lt (rank_lt_dec hj h))
        · have hji : j < i := by omega
          exact absurd hr (Nat.ne_of_lt (rank_lt_dec hi hji))
      · intro j hj
        exact filter_card_lt hj (by simp)
      · intro j hj
        have hjs : x j - t < -(28/5:ℝ) := (Finset.mem_filter.1 hj).2
        have hi1 : Jm.max' hne ∈ Jm := Jm.max'_mem hne
        have hi1n : Jm.max' hne < n := Finset.mem_range.1 (hJmsub hi1)
        have hi1s : x (Jm.max' hne) - t < -(28/5:ℝ) := (Finset.mem_filter.1 hi1).2
        have hle : j ≤ Jm.max' hne := Finset.le_max' _ _ hj
        have hstep := sep_mono hsep hle hi1n
        have hrk : (Jm.filter (fun k => j < k)).card ≤ Jm.max' hne - j := by
          have hsub : Jm.filter (fun k => j < k) ⊆ Finset.Ioc j (Jm.max' hne) := by
            intro k hk
            rw [Finset.mem_filter] at hk
            exact Finset.mem_Ioc.2 ⟨hk.2, Finset.le_max' _ _ hk.1⟩
          have := Finset.card_le_card hsub
          simpa [Nat.card_Ioc] using this
        have hcast : (((Jm.filter (fun k => j < k)).card : ℕ) : ℝ)
            ≤ ((Jm.max' hne - j : ℕ) : ℝ) := by exact_mod_cast hrk
        have hmul := mul_le_mul_of_nonneg_right hcast hpi0.le
        have hsm : sm ((Jm.filter (fun k => j < k)).card) ≤ -(x j - t) := by
          unfold sm
          linarith only [hstep, hi1s, hmul]
        have hpos := sm_ge ((Jm.filter (fun k => j < k)).card)
        have habs : (28/5:ℝ) ≤ |x j - t| := by
          rw [abs_of_neg (by linarith : x j - t < 0)]
          linarith only [hsm, hpos]
        have h1 : Qim y (x j - t)^2 ≤ y^2 * Wt ((x j - t)^2 - 2) := Qim_far_sq_abs hy0 hy habs
        have h2 : Wt ((x j - t)^2 - 2) ≤ Gterm ((Jm.filter (fun k => j < k)).card) := by
          refine Wt_anti (smw_pos _) ?_
          nlinarith only [hsm, hpos]
        have h3 : D j ≤ Qim y (x j - t)^2 := by
          simp only [hDdef]
          nlinarith only [sq_nonneg (Qre y (x j - t))]
        calc D j ≤ Qim y (x j - t)^2 := h3
          _ ≤ y^2 * Wt ((x j - t)^2 - 2) := h1
          _ ≤ y^2 * Gterm ((Jm.filter (fun k => j < k)).card) :=
              mul_le_mul_of_nonneg_left h2 hy2
  -- assembling
  have hdisj : Disjoint Jp Jm := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (Finset.mem_filter.1 ha).2
    have h2 := (Finset.mem_filter.1 hb).2
    linarith
  have hsub : Jp ∪ Jm ⊆ Finset.range n := Finset.union_subset hJpsub hJmsub
  have hrest : ∀ j ∈ Finset.range n \ (Jp ∪ Jm), D j ≤ 0 := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    have hjn := hj.1
    have hnot := hj.2
    have h1 : ¬ ((28/5:ℝ) < x j - t) := fun h =>
      hnot (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hjn, h⟩))
    have h2 : ¬ (x j - t < -(28/5:ℝ)) := fun h =>
      hnot (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hjn, h⟩))
    have habs : |x j - t| ≤ 28/5 := abs_le.2 ⟨by linarith [not_lt.1 h2], not_lt.1 h1⟩
    have hnd := no_damage hy0 hy habs
    simp only [hDdef]
    linarith
  have hun : ∑ j ∈ Jp ∪ Jm, D j = ∑ j ∈ Jp, D j + ∑ j ∈ Jm, D j := Finset.sum_union hdisj
  have hsplit : ∑ j ∈ Finset.range n, D j
      = ∑ j ∈ Finset.range n \ (Jp ∪ Jm), D j + ∑ j ∈ Jp ∪ Jm, D j := (Finset.sum_sdiff hsub).symm
  have hnp : ∑ j ∈ Finset.range n \ (Jp ∪ Jm), D j ≤ 0 := Finset.sum_nonpos hrest
  have : ∑ j ∈ Finset.range n, D j ≤ 1228/10000 * y^2 := by
    rw [hsplit, hun]
    linarith only [hnp, hJp_bound, hJm_bound]
  exact this

/-- The same bound for any separation `d ≥ 4`; in particular for `d = 2π`. -/
theorem separated_damage_of_le {n : ℕ} {x : ℕ → ℝ} {y t d : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2)
    (hd : 4 ≤ d) (hsep : ∀ i, i + 1 < n → x i + d ≤ x (i+1)) :
    ∑ j ∈ Finset.range n, (Qim y (x j - t) ^ 2 - Qre y (x j - t) ^ 2) ≤ (1228/10000) * y^2 :=
  separated_damage hy0 hy (fun i hi => by linarith [hsep i hi])

end Retention
