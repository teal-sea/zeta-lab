/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.ClusterPrefix

/-!
# Exact labelled matching counts

This file isolates the finite counting identity used by the squarefree RAMS2
cluster majorant.  A matching with `a` edges on `r` labelled vertices is
obtained by choosing its `2a` covered vertices and pairing them.  The pairing
count is defined recursively, so the construction is division-free in `ℕ`.

The resulting `matchingCount r a` is shown to satisfy both the factorial
formula

`r! / (2^a * a! * (r - 2a)!)`

on its natural range and the vertex-removal recurrence.  No analytic estimate,
connected-component classification, or RAMS2 asymptotic is asserted here.
-/

namespace ZetaLean.HigherXi

open Finset

/-- The number of pairings of `2a` labelled vertices. -/
def pairingCount : ℕ → ℕ
  | 0 => 1
  | a + 1 => (2 * a + 1) * pairingCount a

@[simp]
theorem pairingCount_zero : pairingCount 0 = 1 := rfl

@[simp]
theorem pairingCount_succ (a : ℕ) :
    pairingCount (a + 1) = (2 * a + 1) * pairingCount a := rfl

/-- The number of matchings with exactly `a` edges on `r` labelled vertices. -/
def matchingCount (r a : ℕ) : ℕ :=
  r.choose (2 * a) * pairingCount a

@[simp]
theorem matchingCount_zero_edges (r : ℕ) : matchingCount r 0 = 1 := by
  simp [matchingCount]

/-- There are no `a`-edge matchings when fewer than `2a` vertices are
available. -/
theorem matchingCount_eq_zero_of_lt {r a : ℕ} (h : r < 2 * a) :
    matchingCount r a = 0 := by
  simp [matchingCount, Nat.choose_eq_zero_of_lt h]

/-- The recursive pairing count clears the denominator in the standard
factorial expression `(2a)! / (2^a a!)`. -/
theorem pairingCount_mul_pow_two_mul_factorial (a : ℕ) :
    pairingCount a * (2 ^ a * a.factorial) = (2 * a).factorial := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pairingCount_succ, pow_succ, Nat.factorial_succ]
      calc
        (2 * a + 1) * pairingCount a *
              (2 ^ a * 2 * ((a + 1) * a.factorial)) =
            (2 * a + 2) * (2 * a + 1) *
              (pairingCount a * (2 ^ a * a.factorial)) := by ring
        _ = (2 * a + 2) * (2 * a + 1) * (2 * a).factorial := by rw [ih]
        _ = (2 * (a + 1)).factorial := by
          rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
            Nat.factorial_succ,
            show 2 * a + 1 = 2 * a + 1 by rfl, Nat.factorial_succ]
          ring

/-- Denominator-cleared form of the exact labelled matching count. -/
theorem matchingCount_mul_denominator_eq_factorial {r a : ℕ} (h : 2 * a ≤ r) :
    matchingCount r a *
        (2 ^ a * a.factorial * (r - 2 * a).factorial) = r.factorial := by
  rw [matchingCount]
  calc
    (r.choose (2 * a) * pairingCount a) *
          (2 ^ a * a.factorial * (r - 2 * a).factorial) =
        r.choose (2 * a) *
          (pairingCount a * (2 ^ a * a.factorial)) *
            (r - 2 * a).factorial := by ring
    _ = r.choose (2 * a) * (2 * a).factorial *
          (r - 2 * a).factorial := by
      rw [pairingCount_mul_pow_two_mul_factorial]
    _ = r.factorial := Nat.choose_mul_factorial_mul_factorial h

/-- The factorial formula used as `N(r,a)` in the RAMS2 squarefree cluster
majorant. -/
theorem matchingCount_eq_factorial_div {r a : ℕ} (h : 2 * a ≤ r) :
    matchingCount r a =
      r.factorial /
        (2 ^ a * a.factorial * (r - 2 * a).factorial) := by
  apply Nat.eq_div_of_mul_eq_right
  · positivity
  · rw [mul_comm]
    exact matchingCount_mul_denominator_eq_factorial h

/-- Removing one distinguished vertex either leaves it unmatched or pairs it
with one of the other vertices.  This recurrence characterizes the same exact
labelled count without division. -/
theorem matchingCount_add_two_succ (r a : ℕ) :
    matchingCount (r + 2) (a + 1) =
      matchingCount (r + 1) (a + 1) +
        (r + 1) * matchingCount r a := by
  unfold matchingCount
  rw [show r + 2 = (r + 1) + 1 by omega,
    show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
    Nat.choose_succ_succ', pairingCount_succ]
  have hchoose :
      (r + 1) * r.choose (2 * a) =
        (r + 1).choose (2 * a + 1) * (2 * a + 1) :=
    Nat.add_one_mul_choose_eq r (2 * a)
  rw [show (r + 1) * (r.choose (2 * a) * pairingCount a) =
      ((r + 1) * r.choose (2 * a)) * pairingCount a by ring, hchoose]
  ring

/-- Vertex-removal recurrence in a form valid also for empty old support. -/
theorem matchingCount_succ_succ (r a : ℕ) :
    matchingCount (r + 1) (a + 1) =
      matchingCount r (a + 1) + r * matchingCount (r - 1) a := by
  cases r with
  | zero =>
      rw [matchingCount_eq_zero_of_lt (by omega),
        matchingCount_eq_zero_of_lt (by omega)]
      simp
  | succ r =>
      simpa [Nat.succ_eq_add_one] using matchingCount_add_two_succ r a

section MatchingFamilyBridge

variable {α : Type*} [DecidableEq α]

/-- The `a`-edge slice of the concrete matching family from `ClusterPrefix`. -/
noncomputable def matchingSlice (S : Finset α) (a : ℕ) :
    Finset (Finset (Finset α)) := by
  classical
  exact (matchingFamily S).filter fun M ↦ M.card = a

omit [DecidableEq α] in
theorem mem_matchingSlice_iff {S : Finset α} {a : ℕ}
    {M : Finset (Finset α)} :
    M ∈ matchingSlice S a ↔ M ∈ matchingFamily S ∧ M.card = a := by
  classical
  simp [matchingSlice]

/-- Disjoint two-element edges cover exactly twice as many vertices as there
are edges.  This is the structural cardinality invariant behind the matching
count. -/
theorem card_coveredVertices_eq_two_mul_card
    {M : Finset (Finset α)}
    (hmatching : IsFiniteMatching M)
    (hedge : ∀ e ∈ M, e.card = 2) :
    (coveredVertices M).card = 2 * M.card := by
  have hpair : (M : Set (Finset α)).PairwiseDisjoint id := by
    intro e he f hf hef
    exact hmatching e he f hf hef
  rw [coveredVertices, Finset.card_biUnion hpair]
  calc
    ∑ e ∈ M, e.card = ∑ _e ∈ M, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact hedge e he
    _ = 2 * M.card := by simp [mul_comm]

/-- Every member of `matchingFamily S` satisfies the exact covered-vertex
cardinality invariant. -/
theorem card_coveredVertices_of_mem_matchingFamily
    {S : Finset α} {M : Finset (Finset α)}
    (hM : M ∈ matchingFamily S) :
    (coveredVertices M).card = 2 * M.card := by
  have hm := mem_matchingFamily_iff.mp hM
  apply card_coveredVertices_eq_two_mul_card hm.2
  intro e he
  exact (Finset.mem_powersetCard.mp (hm.1 he)).2

/-- A concrete matching covers only vertices of its ambient support. -/
theorem coveredVertices_subset_of_mem_matchingFamily
    {S : Finset α} {M : Finset (Finset α)}
    (hM : M ∈ matchingFamily S) :
    coveredVertices M ⊆ S := by
  intro p hp
  obtain ⟨e, heM, hpe⟩ := Finset.mem_biUnion.mp hp
  exact (Finset.mem_powersetCard.mp ((mem_matchingFamily_iff.mp hM).1 heM)).1 hpe

/-- Every member of the `a`-edge slice covers exactly `2a` support vertices. -/
theorem card_coveredVertices_of_mem_matchingSlice
    {S : Finset α} {a : ℕ} {M : Finset (Finset α)}
    (hM : M ∈ matchingSlice S a) :
    (coveredVertices M).card = 2 * a := by
  have hs := mem_matchingSlice_iff.mp hM
  rw [card_coveredVertices_of_mem_matchingFamily hs.1, hs.2]

omit [DecidableEq α] in
/-- A nonempty `a`-edge slice forces at least `2a` ambient vertices. -/
theorem two_mul_le_card_of_mem_matchingSlice
    {S : Finset α} {a : ℕ} {M : Finset (Finset α)}
    (hM : M ∈ matchingSlice S a) :
    2 * a ≤ S.card := by
  classical
  rw [← card_coveredVertices_of_mem_matchingSlice hM]
  exact Finset.card_le_card
    (coveredVertices_subset_of_mem_matchingFamily (mem_matchingSlice_iff.mp hM).1)

omit [DecidableEq α] in
/-- Above the natural range, the concrete matching slice is empty. -/
theorem matchingSlice_eq_empty_of_card_lt {S : Finset α} {a : ℕ}
    (h : S.card < 2 * a) :
    matchingSlice S a = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro M hM
  exact (Nat.not_le_of_lt h) (two_mul_le_card_of_mem_matchingSlice hM)

omit [DecidableEq α] in
/-- The concrete and arithmetic matching counts agree throughout the empty
range `S.card < 2a`. -/
theorem card_matchingSlice_eq_matchingCount_of_card_lt
    {S : Finset α} {a : ℕ} (h : S.card < 2 * a) :
    (matchingSlice S a).card = matchingCount S.card a := by
  classical
  rw [matchingSlice_eq_empty_of_card_lt h,
    matchingCount_eq_zero_of_lt h]
  simp

omit [DecidableEq α] in
/-- The zero-edge slice consists only of the empty matching. -/
theorem matchingSlice_zero (S : Finset α) :
    matchingSlice S 0 = {∅} := by
  classical
  ext M
  constructor
  · intro hM
    have hs := mem_matchingSlice_iff.mp hM
    have hzero : M = ∅ := Finset.card_eq_zero.mp hs.2
    simp [hzero]
  · intro hM
    have hzero : M = ∅ := by simpa using hM
    subst M
    apply mem_matchingSlice_iff.mpr
    exact ⟨mem_matchingFamily_iff.mpr ⟨by simp, by simp [IsFiniteMatching]⟩, by simp⟩

omit [DecidableEq α] in
/-- The concrete zero-edge matching slice has the exact cardinality predicted
by `matchingCount`. -/
theorem card_matchingSlice_zero (S : Finset α) :
    (matchingSlice S 0).card = matchingCount S.card 0 := by
  classical
  rw [matchingSlice_zero]
  simp

/-- The one-edge slice is exactly the singleton image of the two-element
subsets of the support. -/
theorem matchingSlice_one (S : Finset α) :
    matchingSlice S 1 = (S.powersetCard 2).image singleton := by
  classical
  ext M
  constructor
  · intro hM
    have hs := mem_matchingSlice_iff.mp hM
    obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hs.2
    have he : e ∈ S.powersetCard 2 := hs.1 |> mem_matchingFamily_iff.mp |>.1 (by simp)
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  · intro hM
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hM
    apply mem_matchingSlice_iff.mpr
    constructor
    · apply mem_matchingFamily_iff.mpr
      constructor
      · intro f hf
        have hfe : f = e := Finset.mem_singleton.mp hf
        simpa [hfe] using he
      · simp [IsFiniteMatching]
    · simp

omit [DecidableEq α] in
/-- The concrete one-edge matching slice has the exact cardinality predicted
by `matchingCount`. -/
theorem card_matchingSlice_one (S : Finset α) :
    (matchingSlice S 1).card = matchingCount S.card 1 := by
  classical
  rw [matchingSlice_one, Finset.card_image_of_injective _ Finset.singleton_injective,
    Finset.card_powersetCard]
  simp [matchingCount]

/-- Adding a new vertex paired with `w` transports an `a`-edge matching on
`S.erase w` to an `(a+1)`-edge matching on `insert v S`. -/
theorem insert_pair_mem_matchingSlice {S : Finset α} {v w : α}
    {a : ℕ} {M : Finset (Finset α)} (hv : v ∉ S) (hw : w ∈ S)
    (hM : M ∈ matchingSlice (S.erase w) a) :
    insert {v, w} M ∈ matchingSlice (insert v S) (a + 1) := by
  classical
  have hvw : v ≠ w := by
    intro hvw
    apply hv
    simpa [hvw] using hw
  have hm := mem_matchingSlice_iff.mp hM
  have hnew : {v, w} ∉ M := by
    intro hedge
    have hsub := (Finset.mem_powersetCard.mp
      ((mem_matchingFamily_iff.mp hm.1).1 hedge)).1
    exact (by simp : w ∉ S.erase w) (hsub (by simp))
  apply mem_matchingSlice_iff.mpr
  constructor
  · apply mem_matchingFamily_iff.mpr
    constructor
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | heM
      · exact Finset.mem_powersetCard.mpr ⟨by simp [hw], by simp [hvw]⟩
      · have hold := Finset.mem_powersetCard.mp
          ((mem_matchingFamily_iff.mp hm.1).1 heM)
        exact Finset.mem_powersetCard.mpr
          ⟨hold.1.trans fun x hx ↦ by simp [Finset.mem_of_mem_erase hx], hold.2⟩
    · have hdis : ∀ f ∈ M, Disjoint {v, w} f := by
        intro f hf
        rw [Finset.disjoint_left]
        intro x hx hxf
        have hfsub := (Finset.mem_powersetCard.mp
          ((mem_matchingFamily_iff.mp hm.1).1 hf)).1
        rcases Finset.mem_insert.mp hx with rfl | hxw
        · exact hv (Finset.mem_of_mem_erase (hfsub hxf))
        · have hxw' : x = w := Finset.mem_singleton.mp hxw
          subst x
          exact (by simp : w ∉ S.erase w) (hfsub hxf)
      intro e he f hf hef
      rcases Finset.mem_insert.mp he with rfl | heM
      · rcases Finset.mem_insert.mp hf with rfl | hfM
        · exact (hef rfl).elim
        · exact hdis f hfM
      · rcases Finset.mem_insert.mp hf with rfl | hfM
        · exact (hdis e heM).symm
        · exact (mem_matchingFamily_iff.mp hm.1).2 e heM f hfM hef
  · rw [Finset.card_insert_of_notMem hnew, hm.2]

/-- Removing a named edge incident to the new vertex recovers an `a`-edge
matching on the support with its other endpoint removed. -/
theorem erase_pair_mem_matchingSlice {S : Finset α} {v w : α}
    {a : ℕ} {M : Finset (Finset α)}
    (hM : M ∈ matchingSlice (insert v S) (a + 1))
    (hedge : {v, w} ∈ M) :
    M.erase {v, w} ∈ matchingSlice (S.erase w) a := by
  classical
  have hm := mem_matchingSlice_iff.mp hM
  apply mem_matchingSlice_iff.mpr
  constructor
  · apply mem_matchingFamily_iff.mpr
    constructor
    · intro f hfErase
      have hf : f ∈ M := Finset.mem_of_mem_erase hfErase
      have hne : f ≠ {v, w} := Finset.ne_of_mem_erase hfErase
      have hdis := (mem_matchingFamily_iff.mp hm.1).2 f hf {v, w} hedge hne
      have hfsub := (Finset.mem_powersetCard.mp
        ((mem_matchingFamily_iff.mp hm.1).1 hf)).1
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro x hxf
        have hxinsert := hfsub hxf
        have hxv : x ≠ v := by
          intro hxv
          subst x
          exact (Finset.disjoint_left.mp hdis) hxf (by simp)
        have hxw : x ≠ w := by
          intro hxw
          subst x
          exact (Finset.disjoint_left.mp hdis) hxf (by simp)
        exact Finset.mem_erase.mpr
          ⟨hxw, (Finset.mem_insert.mp hxinsert).resolve_left hxv⟩
      · exact (Finset.mem_powersetCard.mp
          ((mem_matchingFamily_iff.mp hm.1).1 hf)).2
    · intro e he f hf hef
      exact (mem_matchingFamily_iff.mp hm.1).2 e
        (Finset.mem_of_mem_erase he) f (Finset.mem_of_mem_erase hf) hef
  · rw [Finset.card_erase_of_mem hedge, hm.2]
    simp

/-- The fiber of `(a+1)`-edge matchings containing the named edge `{v,w}`. -/
noncomputable def matchingSliceAt (S : Finset α) (v : α) (a : ℕ) (w : α) :
    Finset (Finset (Finset α)) := by
  classical
  exact (matchingSlice (insert v S) (a + 1)).filter fun M ↦ {v, w} ∈ M

/-- A named-edge fiber is exactly the image of the smaller matching slice
obtained by deleting that edge and its old endpoint. -/
theorem matchingSliceAt_eq_image_insert_pair {S : Finset α} {v w : α}
    {a : ℕ} (hv : v ∉ S) (hw : w ∈ S) :
    matchingSliceAt S v a w =
      (matchingSlice (S.erase w) a).image (insert {v, w}) := by
  classical
  ext M
  constructor
  · intro hM
    have hf := Finset.mem_filter.mp hM
    exact Finset.mem_image.mpr
      ⟨M.erase {v, w}, erase_pair_mem_matchingSlice hf.1 hf.2,
        Finset.insert_erase hf.2⟩
  · intro hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hM
    apply Finset.mem_filter.mpr
    exact ⟨insert_pair_mem_matchingSlice hv hw hN, Finset.mem_insert_self _ _⟩

/-- Adding `{v,w}` is injective on matchings supported in `S.erase w`, so the
named-edge fiber and the smaller slice have equal cardinality. -/
theorem card_matchingSliceAt {S : Finset α} {v w : α} {a : ℕ}
    (hv : v ∉ S) (hw : w ∈ S) :
    (matchingSliceAt S v a w).card = (matchingSlice (S.erase w) a).card := by
  classical
  rw [matchingSliceAt_eq_image_insert_pair hv hw]
  apply Finset.card_image_iff.mpr
  intro M hM N hN hMN
  have hnot : ∀ K ∈ matchingSlice (S.erase w) a, {v, w} ∉ K := by
    intro K hK hedge
    have hkfamily := (mem_matchingSlice_iff.mp hK).1
    have hsub := (Finset.mem_powersetCard.mp
      ((mem_matchingFamily_iff.mp hkfamily).1 hedge)).1
    exact (by simp : w ∉ S.erase w) (hsub (by simp))
  have herase := congrArg (fun K : Finset (Finset α) ↦ K.erase {v, w}) hMN
  simpa [hnot M hM, hnot N hN] using herase

/-- Matchings in the enlarged support that leave the new vertex unmatched. -/
noncomputable def unmatchedMatchingSlice (S : Finset α) (v : α) (a : ℕ) :
    Finset (Finset (Finset α)) := by
  classical
  exact (matchingSlice (insert v S) a).filter fun M ↦ v ∉ coveredVertices M

/-- Matchings in the enlarged support that use the new vertex. -/
noncomputable def matchedMatchingSlice (S : Finset α) (v : α) (a : ℕ) :
    Finset (Finset (Finset α)) := by
  classical
  exact (matchingSlice (insert v S) a).filter fun M ↦ v ∈ coveredVertices M

/-- Enlarging a support by a vertex does not change the slice of matchings that
leave that vertex uncovered. -/
theorem unmatchedMatchingSlice_eq {S : Finset α} {v : α} {a : ℕ}
    (hv : v ∉ S) :
    unmatchedMatchingSlice S v a = matchingSlice S a := by
  classical
  ext M
  constructor
  · intro hM
    have hf := Finset.mem_filter.mp hM
    have hm := mem_matchingSlice_iff.mp hf.1
    apply mem_matchingSlice_iff.mpr
    refine ⟨mem_matchingFamily_iff.mpr ⟨?_, (mem_matchingFamily_iff.mp hm.1).2⟩, hm.2⟩
    intro e he
    have hedge := Finset.mem_powersetCard.mp
      ((mem_matchingFamily_iff.mp hm.1).1 he)
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hedge.2⟩
    intro x hxe
    rcases Finset.mem_insert.mp (hedge.1 hxe) with rfl | hxS
    · exact (hf.2 (Finset.mem_biUnion.mpr ⟨e, he, hxe⟩)).elim
    · exact hxS
  · intro hM
    have hm := mem_matchingSlice_iff.mp hM
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_matchingSlice_iff.mpr
      refine ⟨mem_matchingFamily_iff.mpr ⟨?_, (mem_matchingFamily_iff.mp hm.1).2⟩, hm.2⟩
      intro e he
      have hedge := Finset.mem_powersetCard.mp
        ((mem_matchingFamily_iff.mp hm.1).1 he)
      exact Finset.mem_powersetCard.mpr
        ⟨hedge.1.trans fun x hx ↦ Finset.mem_insert_of_mem hx, hedge.2⟩
    · intro hvcover
      obtain ⟨e, heM, hve⟩ := Finset.mem_biUnion.mp hvcover
      exact hv ((Finset.mem_powersetCard.mp
        ((mem_matchingFamily_iff.mp hm.1).1 heM)).1 hve)

/-- A covered new vertex has a unique partner in the old support. -/
theorem existsUnique_partner_of_mem_matchedMatchingSlice
    {S : Finset α} {v : α} {a : ℕ} {M : Finset (Finset α)}
    (hv : v ∉ S) (hM : M ∈ matchedMatchingSlice S v (a + 1)) :
    ∃! w, w ∈ S ∧ {v, w} ∈ M := by
  classical
  have hf := Finset.mem_filter.mp hM
  have hm := mem_matchingSlice_iff.mp hf.1
  obtain ⟨e, heM, hve⟩ := Finset.mem_biUnion.mp hf.2
  have hedge := Finset.mem_powersetCard.mp
    ((mem_matchingFamily_iff.mp hm.1).1 heM)
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hedge.2
  rcases Finset.mem_insert.mp hve with hvx | hvy
  · subst x
    refine ⟨y, ⟨?_, heM⟩, ?_⟩
    · exact (Finset.mem_insert.mp (hedge.1 (by simp))).resolve_left hxy.symm
    · intro z hz
      by_contra hzy
      have hzv : z ≠ v := by
        intro hzv
        exact hv (hzv ▸ hz.1)
      have hne : ({v, z} : Finset α) ≠ ({v, y} : Finset α) := by
        intro heq
        have hzmem : z ∈ ({v, y} : Finset α) := heq ▸ (by simp)
        rcases Finset.mem_insert.mp hzmem with hzv' | hzy'
        · exact hzv hzv'
        · exact hzy (Finset.mem_singleton.mp hzy')
      have hdis := (mem_matchingFamily_iff.mp hm.1).2
        {v, z} hz.2 {v, y} heM hne
      have hvleft : v ∈ ({v, z} : Finset α) := by simp
      have hvright : v ∈ ({v, y} : Finset α) := by simp
      exact (Finset.disjoint_left.mp hdis) hvleft hvright
  · have hvy' : v = y := Finset.mem_singleton.mp hvy
    subst y
    refine ⟨x, ⟨?_, by simpa [Finset.pair_comm] using heM⟩, ?_⟩
    · exact (Finset.mem_insert.mp (hedge.1 (by simp))).resolve_left hxy
    · intro z hz
      by_contra hzx
      have hzv : z ≠ v := by
        intro hzv
        exact hv (hzv ▸ hz.1)
      have hne : ({v, z} : Finset α) ≠ ({v, x} : Finset α) := by
        intro heq
        have hzmem : z ∈ ({v, x} : Finset α) := heq ▸ (by simp)
        rcases Finset.mem_insert.mp hzmem with hzv' | hzx'
        · exact hzv hzv'
        · exact hzx (Finset.mem_singleton.mp hzx')
      have hxedge : {v, x} ∈ M := by simpa [Finset.pair_comm] using heM
      have hdis := (mem_matchingFamily_iff.mp hm.1).2
        {v, z} hz.2 {v, x} hxedge hne
      have hvleft : v ∈ ({v, z} : Finset α) := by simp
      have hvright : v ∈ ({v, x} : Finset α) := by simp
      exact (Finset.disjoint_left.mp hdis) hvleft hvright

/-- The matchings that cover the new vertex are the disjoint union of their
unique-partner fibers. -/
theorem matchedMatchingSlice_eq_biUnion {S : Finset α} {v : α} {a : ℕ}
    (hv : v ∉ S) :
    matchedMatchingSlice S v (a + 1) =
      S.biUnion fun w ↦ matchingSliceAt S v a w := by
  classical
  ext M
  constructor
  · intro hM
    obtain ⟨w, hw, hedge⟩ :=
      (existsUnique_partner_of_mem_matchedMatchingSlice hv hM).exists
    exact Finset.mem_biUnion.mpr
      ⟨w, hw, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hM).1, hedge⟩⟩
  · intro hM
    obtain ⟨w, hw, hMw⟩ := Finset.mem_biUnion.mp hM
    have hf := Finset.mem_filter.mp hMw
    apply Finset.mem_filter.mpr
    exact ⟨hf.1, Finset.mem_biUnion.mpr ⟨{v, w}, hf.2, by simp⟩⟩

/-- The unique-partner fibers are pairwise disjoint. -/
theorem pairwiseDisjoint_matchingSliceAt {S : Finset α} {v : α} {a : ℕ}
    (hv : v ∉ S) :
    (S : Set α).PairwiseDisjoint fun w ↦ matchingSliceAt S v a w := by
  classical
  intro w hw z hz hwz
  change Disjoint (matchingSliceAt S v a w) (matchingSliceAt S v a z)
  rw [Finset.disjoint_left]
  intro M hMw hMz
  have hmatched : M ∈ matchedMatchingSlice S v (a + 1) := by
    have hf := Finset.mem_filter.mp hMw
    exact Finset.mem_filter.mpr
      ⟨hf.1, Finset.mem_biUnion.mpr ⟨{v, w}, hf.2, by simp⟩⟩
  have hu := existsUnique_partner_of_mem_matchedMatchingSlice hv hmatched
  have hw' : w ∈ S ∧ {v, w} ∈ M := ⟨hw, (Finset.mem_filter.mp hMw).2⟩
  have hz' : z ∈ S ∧ {v, z} ∈ M := ⟨hz, (Finset.mem_filter.mp hMz).2⟩
  exact hwz (hu.unique hw' hz')

/-- Exact cardinality of the part of the slice that covers a new vertex. -/
theorem card_matchedMatchingSlice {S : Finset α} {v : α} {a : ℕ}
    (hv : v ∉ S) :
    (matchedMatchingSlice S v (a + 1)).card =
      ∑ w ∈ S, (matchingSlice (S.erase w) a).card := by
  classical
  rw [matchedMatchingSlice_eq_biUnion hv,
    Finset.card_biUnion (pairwiseDisjoint_matchingSliceAt hv)]
  apply Finset.sum_congr rfl
  intro w hw
  exact card_matchingSliceAt hv hw

/-- Exact vertex-removal recurrence for the concrete matching slices. -/
theorem card_matchingSlice_insert_succ {S : Finset α} {v : α} {a : ℕ}
    (hv : v ∉ S) :
    (matchingSlice (insert v S) (a + 1)).card =
      (matchingSlice S (a + 1)).card +
        ∑ w ∈ S, (matchingSlice (S.erase w) a).card := by
  classical
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := matchingSlice (insert v S) (a + 1))
    (fun M ↦ v ∈ coveredVertices M)
  change (matchedMatchingSlice S v (a + 1)).card +
      (unmatchedMatchingSlice S v (a + 1)).card =
        (matchingSlice (insert v S) (a + 1)).card at hpartition
  rw [card_matchedMatchingSlice hv, unmatchedMatchingSlice_eq hv] at hpartition
  omega

omit [DecidableEq α] in
/-- The concrete `a`-edge slice of `matchingFamily S` has exactly the labelled
matching count `S.card! / (2^a a! (S.card-2a)!)`.  The proof uses the honest
vertex-removal decomposition into an unmatched slice and disjoint
unique-partner fibers. -/
theorem card_matchingSlice (S : Finset α) (a : ℕ) :
    (matchingSlice S a).card = matchingCount S.card a := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S a with
  | h n ih =>
      rcases S.eq_empty_or_nonempty with hS | hS
      · subst S
        cases a with
        | zero =>
            rw [← hn]
            exact card_matchingSlice_zero ∅
        | succ a =>
            rw [← hn]
            exact card_matchingSlice_eq_matchingCount_of_card_lt (by simp)
      · obtain ⟨v, hvS⟩ := hS
        let T := S.erase v
        have hvT : v ∉ T := by simp [T]
        have hST : insert v T = S := by simpa [T] using Finset.insert_erase hvS
        rw [← hST] at hn ⊢
        cases a with
        | zero =>
            rw [← hn]
            exact card_matchingSlice_zero (insert v T)
        | succ a =>
            have hTlt : T.card < n := by
              rw [Finset.card_insert_of_notMem hvT] at hn
              omega
            have hT := ih T.card hTlt T (a + 1) rfl
            have hErase : ∀ w ∈ T,
                (matchingSlice (T.erase w) a).card =
                  matchingCount (T.card - 1) a := by
              intro w hw
              have hEraseLt : (T.erase w).card < n := by
                rw [Finset.card_erase_of_mem hw]
                omega
              rw [ih (T.erase w).card hEraseLt (T.erase w) a rfl,
                Finset.card_erase_of_mem hw]
            calc
              (matchingSlice (insert v T) (a + 1)).card =
                  (matchingSlice T (a + 1)).card +
                    ∑ w ∈ T, (matchingSlice (T.erase w) a).card :=
                card_matchingSlice_insert_succ hvT
              _ = matchingCount T.card (a + 1) +
                    T.card * matchingCount (T.card - 1) a := by
                have hsum :
                    (∑ w ∈ T, (matchingSlice (T.erase w) a).card) =
                      ∑ _w ∈ T, matchingCount (T.card - 1) a :=
                  Finset.sum_congr rfl hErase
                rw [hT, hsum]
                simp
              _ = matchingCount (T.card + 1) (a + 1) :=
                (matchingCount_succ_succ T.card a).symm
              _ = matchingCount n (a + 1) := by
                rw [← hn, Finset.card_insert_of_notMem hvT]

end MatchingFamilyBridge

end ZetaLean.HigherXi
