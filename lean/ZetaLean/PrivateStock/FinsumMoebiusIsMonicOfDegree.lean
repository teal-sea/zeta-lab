import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import ZetaLean.PrivateStock.CardIsMonicOfDegree

/-!
# The Moebius function summed over monic polynomials of a fixed degree

Over a finite field `F` with `q = |F|` elements, the Dirichlet series of the Moebius function
of `F[X]` is `1 - q * t`, so that

`∑ (f monic of degree n), μ f = 0`  for every `n ≥ 2`.

We prove this by the elementary route: the Moebius function of a unique factorization monoid
sums to zero over the (monic) divisors of a non-unit, and the resulting convolution identity
`∑ k ≤ n, q ^ (n - k) * S k = 0` (`n ≥ 1`, `S k` the sum in degree `k`) forces `S n = 0` as
soon as `n ≥ 2`.
-/

set_option autoImplicit false

open Finset UniqueFactorizationMonoid

open scoped Polynomial

namespace Polynomial

/-! ### The finset of monic polynomials of a given degree -/

theorem finite_setOf_isMonicOfDegree (F : Type*) [Field F] [Finite F] (n : ℕ) :
    {f : F[X] | IsMonicOfDegree f n}.Finite :=
  Set.finite_coe_iff.mp (Finite.of_equiv _ (isMonicOfDegreeEquivFun F n).symm)

/-- The finset of monic polynomials of degree `n` over a finite field. -/
noncomputable def monicsOfDegree (F : Type*) [Field F] [Finite F] (n : ℕ) : Finset F[X] :=
  (finite_setOf_isMonicOfDegree F n).toFinset

variable {F : Type*} [Field F] [Finite F]

@[simp]
theorem mem_monicsOfDegree {n : ℕ} {f : F[X]} :
    f ∈ monicsOfDegree F n ↔ IsMonicOfDegree f n :=
  Set.Finite.mem_toFinset _

theorem card_monicsOfDegree (n : ℕ) :
    (monicsOfDegree F n).card = Nat.card F ^ n := by
  rw [← card_isMonicOfDegree F n, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_monicsOfDegree)

/-! ### The Moebius function summed over the monic divisors of a non-unit -/

theorem finite_setOf_monic_dvd {f : F[X]} (hf : f ≠ 0) :
    {d : F[X] | d.Monic ∧ d ∣ f}.Finite := by
  refine Set.Finite.subset ((Set.finite_Icc 0 f.natDegree).biUnion
    (fun k _ ↦ finite_setOf_isMonicOfDegree F k)) ?_
  rintro d ⟨hm, hdvd⟩
  exact Set.mem_biUnion (Set.mem_Icc.mpr ⟨Nat.zero_le _, natDegree_le_of_dvd hdvd hf⟩) ⟨rfl, hm⟩

open scoped Classical in
/-- The finset of monic divisors of `f`; empty by convention when `f = 0`. -/
noncomputable def monicDivisors (f : F[X]) : Finset F[X] :=
  if hf : f = 0 then ∅ else (finite_setOf_monic_dvd hf).toFinset

theorem mem_monicDivisors {f d : F[X]} (hf : f ≠ 0) :
    d ∈ monicDivisors f ↔ d.Monic ∧ d ∣ f := by
  rw [monicDivisors, dif_neg hf]
  exact Set.Finite.mem_toFinset _

/-- The Moebius function of `F[X]` sums to zero over the monic divisors of a monic non-unit:
the squarefree monic divisors are exactly the products of subsets of the set of monic
irreducible divisors, and an alternating sum over a nonempty powerset vanishes. -/
theorem sum_moebius_monicDivisors {f : F[X]} (hf : f.Monic) (hfu : ¬ IsUnit f) :
    ∑ d ∈ monicDivisors f, moebius d = 0 := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  -- Only the squarefree divisors contribute.
  rw [← Finset.sum_filter_of_ne (p := Squarefree)
    fun d _ hd ↦ by by_contra h; exact hd (moebius_of_not_squarefree h)]
  set S : Finset F[X] := (normalizedFactors f).toFinset with hSdef
  have hSne : S.Nonempty := by
    rw [hSdef, Multiset.toFinset_nonempty]
    exact fun h ↦ hfu ((normalizedFactors_eq_zero_iff hf0).mp h)
  have hSmem : ∀ p ∈ S, Irreducible p ∧ p.Monic ∧ p ∣ f := by
    intro p hp
    rw [hSdef, Multiset.mem_toFinset] at hp
    exact (Polynomial.mem_normalizedFactors_iff hf0).mp hp
  -- `T ↦ ∏ T` and `d ↦ {monic irreducible factors of d}` are mutually inverse.
  have hval : ∀ T : Finset F[X], T.prod id = T.val.prod := by
    intro T
    rw [Finset.prod_eq_multiset_prod, Multiset.map_id]
  have hprodTle : ∀ T ∈ S.powerset, T.val ≤ normalizedFactors f := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    refine (Multiset.le_iff_subset T.nodup).mpr fun x hx ↦ ?_
    have hxS : x ∈ S := hT hx
    rwa [hSdef, Multiset.mem_toFinset] at hxS
  have hprodMonic : ∀ T ∈ S.powerset, (T.prod id).Monic := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    exact monic_multiset_prod_of_monic T.val id fun p hp ↦ (hSmem p (hT hp)).2.1
  have hprodFactors : ∀ T ∈ S.powerset, normalizedFactors (T.prod id) = T.val := by
    intro T hT
    have hT' := hT
    rw [Finset.mem_powerset] at hT'
    rw [hval, normalizedFactors_prod_eq T.val fun p hp ↦ (hSmem p (hT' hp)).1]
    rw [Multiset.map_congr rfl fun p hp ↦ (hSmem p (hT' hp)).2.1.normalize_eq_self,
      Multiset.map_id']
  have hprodNe : ∀ T ∈ S.powerset, T.prod id ≠ 0 := fun T hT ↦ (hprodMonic T hT).ne_zero
  refine (Finset.sum_nbij' (t := S.powerset) (g := fun T : Finset F[X] ↦ (-1 : ℤ) ^ T.card)
    (fun d ↦ (normalizedFactors d).toFinset) (fun T ↦ T.prod id) ?_ ?_ ?_ ?_ ?_).trans
    (Finset.sum_powerset_neg_one_pow_card_of_nonempty hSne)
  · -- the map lands in the powerset
    intro d hd
    rw [Finset.mem_filter, mem_monicDivisors hf0] at hd
    obtain ⟨⟨hdm, hdvd⟩, -⟩ := hd
    rw [Finset.mem_powerset, hSdef]
    exact Multiset.toFinset_subset.mpr (Multiset.subset_of_le
      ((dvd_iff_normalizedFactors_le_normalizedFactors hdm.ne_zero hf0).mp hdvd))
  · -- the inverse map lands in the filtered divisors
    intro T hT
    rw [Finset.mem_filter, mem_monicDivisors hf0]
    refine ⟨⟨hprodMonic T hT, ?_⟩, ?_⟩
    · rw [(dvd_iff_normalizedFactors_le_normalizedFactors (hprodNe T hT) hf0), hprodFactors T hT]
      exact hprodTle T hT
    · rw [squarefree_iff_nodup_normalizedFactors (hprodNe T hT), hprodFactors T hT]
      exact T.nodup
  · -- left inverse
    intro d hd
    rw [Finset.mem_filter, mem_monicDivisors hf0] at hd
    obtain ⟨⟨hdm, -⟩, hdsq⟩ := hd
    have hnd : (normalizedFactors d).Nodup :=
      (squarefree_iff_nodup_normalizedFactors hdm.ne_zero).mp hdsq
    rw [hval, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    refine eq_of_monic_of_associated ?_ hdm (prod_normalizedFactors hdm.ne_zero)
    have := monic_multiset_prod_of_monic (normalizedFactors d) id fun p hp ↦
      ((Polynomial.mem_normalizedFactors_iff hdm.ne_zero).mp hp).2.1
    rwa [Multiset.map_id] at this
  · -- right inverse
    intro T hT
    rw [hprodFactors T hT, Finset.val_toFinset]
  · -- the summands agree
    intro d hd
    rw [Finset.mem_filter, mem_monicDivisors hf0] at hd
    obtain ⟨⟨hdm, -⟩, hdsq⟩ := hd
    have hnd : (normalizedFactors d).Nodup :=
      (squarefree_iff_nodup_normalizedFactors hdm.ne_zero).mp hdsq
    rw [hdsq.moebius_eq, Multiset.toFinset_card_of_nodup hnd, normalizedFactors,
      Multiset.card_map]

/-! ### The convolution identity and the induction -/

variable (F) in
/-- The sum of the Moebius function over all monic polynomials of degree `n`. -/
noncomputable def moebiusSumOfDegree (n : ℕ) : ℤ := ∑ f ∈ monicsOfDegree F n, moebius f

open scoped Classical in
/-- The pairs `(d, e)` of monic polynomials of total degree `n`. -/
noncomputable def monicPairs (F : Type*) [Field F] [Finite F] (n : ℕ) : Finset (F[X] × F[X]) :=
  (Finset.range (n + 1)).biUnion fun k ↦ monicsOfDegree F k ×ˢ monicsOfDegree F (n - k)

theorem mem_monicPairs {n : ℕ} {p : F[X] × F[X]} :
    p ∈ monicPairs F n ↔
      ∃ k ≤ n, IsMonicOfDegree p.1 k ∧ IsMonicOfDegree p.2 (n - k) := by
  classical
  simp only [monicPairs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
    mem_monicsOfDegree, Nat.lt_succ_iff]

/-- Summing `μ d` over all pairs `(d, e)` of monic polynomials of total degree `n`, sorted by
the degree of `d`. -/
theorem sum_moebius_monicPairs_eq (n : ℕ) :
    ∑ p ∈ monicPairs F n, moebius p.1
      = ∑ k ∈ Finset.range (n + 1), (Nat.card F : ℤ) ^ (n - k) * moebiusSumOfDegree F k := by
  classical
  rw [monicPairs, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_product, moebiusSumOfDegree, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [Finset.sum_const, card_monicsOfDegree, nsmul_eq_mul, Nat.cast_pow]
  · intro k _ l _ hkl
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, mem_monicsOfDegree]
    rintro p ⟨hp1, -⟩ ⟨hq1, -⟩
    exact hkl (hp1.natDegree_eq ▸ hq1.natDegree_eq)

/-- Summing `μ d` over all pairs `(d, e)` of monic polynomials of total degree `n ≥ 1` gives
zero, because for each monic `f` of degree `n` the Moebius function sums to zero over the
monic divisors of `f`. -/
theorem sum_moebius_monicPairs_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ monicPairs F n, moebius p.1 = 0 := by
  classical
  have hmaps : ∀ p ∈ monicPairs F n, p.1 * p.2 ∈ monicsOfDegree F n := by
    intro p hp
    obtain ⟨k, hk, hp1, hp2⟩ := mem_monicPairs.mp hp
    rw [mem_monicsOfDegree]
    have := hp1.mul hp2
    rwa [Nat.add_sub_cancel' hk] at this
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_eq_zero fun f hf ↦ ?_
  rw [mem_monicsOfDegree] at hf
  have hf0 : f ≠ 0 := hf.monic.ne_zero
  have hfu : ¬ IsUnit f := by
    intro h
    have := natDegree_eq_zero_of_isUnit h
    rw [hf.natDegree_eq] at this
    omega
  refine Eq.trans ?_ (sum_moebius_monicDivisors hf.monic hfu)
  refine Finset.sum_nbij' (fun p ↦ p.1) (fun d ↦ (d, f / d)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp, hprod⟩ := hp
    obtain ⟨k, hk, hp1, hp2⟩ := mem_monicPairs.mp hp
    exact (mem_monicDivisors hf0).mpr ⟨hp1.monic, hprod ▸ Dvd.intro _ rfl⟩
  · intro d hd
    obtain ⟨hdm, hdvd⟩ := (mem_monicDivisors hf0).mp hd
    have hd0 : d ≠ 0 := hdm.ne_zero
    have hkey : d * (f / d) = f := EuclideanDomain.mul_div_cancel' hd0 hdvd
    have hle : d.natDegree ≤ n := hf.natDegree_eq ▸ natDegree_le_of_dvd hdvd hf0
    have hd' : IsMonicOfDegree d d.natDegree := ⟨rfl, hdm⟩
    have hquot : IsMonicOfDegree (f / d) (n - d.natDegree) := by
      refine hd'.of_mul_left ?_
      rw [hkey, Nat.add_sub_cancel' hle]
      exact hf
    rw [Finset.mem_filter]
    exact ⟨mem_monicPairs.mpr ⟨d.natDegree, hle, hd', hquot⟩, hkey⟩
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp, hprod⟩ := hp
    obtain ⟨k, hk, hp1, hp2⟩ := mem_monicPairs.mp hp
    have hp10 : p.1 ≠ 0 := hp1.monic.ne_zero
    have hdvd : p.1 ∣ f := ⟨p.2, hprod.symm⟩
    have : f / p.1 = p.2 :=
      mul_left_cancel₀ hp10 (by rw [EuclideanDomain.mul_div_cancel' hp10 hdvd, hprod])
    rw [this]
  · intro d _
    rfl
  · intro p _
    rfl

/-- The main induction: the convolution identity forces the degree-`n` Moebius sum to vanish
for every `n ≥ 2`. -/
theorem moebiusSumOfDegree_eq_zero {n : ℕ} (hn : 2 ≤ n) : moebiusSumOfDegree F n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have key : ∀ j : ℕ, 1 ≤ j →
      ∑ k ∈ Finset.range (j + 1), (Nat.card F : ℤ) ^ (j - k) * moebiusSumOfDegree F k = 0 :=
    fun j hj ↦ (sum_moebius_monicPairs_eq j).symm.trans (sum_moebius_monicPairs_eq_zero hj)
  have h1 := key (m + 2) (by omega)
  have h2 := key (m + 1) (by omega)
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul] at h1
  have h3 : ∑ k ∈ Finset.range (m + 2), (Nat.card F : ℤ) ^ (m + 2 - k) * moebiusSumOfDegree F k
      = (Nat.card F : ℤ) *
        ∑ k ∈ Finset.range (m + 2), (Nat.card F : ℤ) ^ (m + 1 - k) * moebiusSumOfDegree F k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    rw [← mul_assoc, ← pow_succ']
    congr 2
    omega
  rw [h3, h2, mul_zero, zero_add] at h1
  exact h1

end Polynomial

/-- Over a finite field `F`, the Moebius function of `F[X]` sums to zero over the monic
polynomials of any fixed degree `n ≥ 2`. -/
theorem Polynomial.finsum_moebius_isMonicOfDegree_eq_zero (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) :
    ∑ᶠ f : {f : F[X] // Polynomial.IsMonicOfDegree f n},
      UniqueFactorizationMonoid.moebius (f : F[X]) = 0 := by
  classical
  have : Finite {f : F[X] // Polynomial.IsMonicOfDegree f n} :=
    Finite.of_equiv _ (Polynomial.isMonicOfDegreeEquivFun F n).symm
  have : Fintype {f : F[X] // Polynomial.IsMonicOfDegree f n} := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_subtype (Polynomial.monicsOfDegree F n)
    (fun _ ↦ Polynomial.mem_monicsOfDegree) (fun d ↦ UniqueFactorizationMonoid.moebius d)]
  exact Polynomial.moebiusSumOfDegree_eq_zero hn
