import Mathlib.FieldTheory.Finite.Extension
import ZetaLean.PrivateStock.NumMonicIrreducibleOfDegree

/-!
# The mass formula for monic irreducible polynomials over a finite field

Over a finite field `F` with `q = |F|` elements, the polynomial `X ^ (q ^ d) - X` is the product
of all the monic irreducible polynomials of `F[X]` whose degree divides `d`. Comparing degrees
gives the classical identity

`∑ e ∈ d.divisors, e * numMonicIrreducibleOfDegree F e = q ^ d`.

We prove it by counting the elements of a degree-`d` extension `L/F` according to their minimal
polynomial: the fibre over a monic irreducible `P` is the root set of `P` in `L`, which has
exactly `deg P` elements.
-/

set_option autoImplicit false

open Polynomial Finset

namespace Submission.Helpers

/-- Over a finite field there are only finitely many polynomials of degree at most `n`. -/
theorem finite_setOf_natDegree_le (F : Type*) [Field F] [Finite F] (n : ℕ) :
    {P : F[X] | P.natDegree ≤ n}.Finite := by
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective
    (fun P : {P : F[X] | P.natDegree ≤ n} ↦ fun i : Fin (n + 1) ↦ P.1.coeff i) ?_
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  have hP : P.natDegree ≤ n := hP
  have hQ : Q.natDegree ≤ n := hQ
  refine Subtype.ext (Polynomial.ext fun i ↦ ?_)
  by_cases hi : i ≤ n
  · exact congrFun h ⟨i, by omega⟩
  · rw [P.coeff_eq_zero_of_natDegree_lt (by omega), Q.coeff_eq_zero_of_natDegree_lt (by omega)]

end Submission.Helpers

open Submission.Helpers in
/-- The degrees of the monic irreducible polynomials over a finite field `F` satisfy the mass
formula `∑ e ∈ d.divisors, e * numMonicIrreducibleOfDegree F e = |F| ^ d` for every `d ≠ 0`.

Equivalently, `X ^ (|F| ^ d) - X` is the product of all monic irreducible polynomials whose
degree divides `d`. -/
theorem Polynomial.sum_degree_mul_numMonicIrreducibleOfDegree_eq_pow
    (F : Type*) [Field F] [Finite F] {d : ℕ} (hd : d ≠ 0) :
    ∑ e ∈ d.divisors, e * Polynomial.numMonicIrreducibleOfDegree F e = Nat.card F ^ d := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists F
  have : CharP F p := hp
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have : NeZero d := ⟨hd⟩
  -- A degree-`d` extension `L` of `F`.
  set L := FiniteField.Extension F p d with hLdef
  have : Fintype L := Fintype.ofFinite L
  have hq : Nat.card F ^ d = Fintype.card L := by
    rw [← FiniteField.natCard_extension F p d, Nat.card_eq_fintype_card]
  -- The polynomial `X ^ |L| - X` over `L`.
  have hone : 1 < Fintype.card L := Fintype.one_lt_card
  set g : L[X] := X ^ Fintype.card L - X with hgdef
  have hg0 : g ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L hone
  have hgdeg : g.natDegree = Fintype.card L := FiniteField.X_pow_card_sub_X_natDegree_eq L hone
  have hgroots : g.roots = (Finset.univ : Finset L).val := FiniteField.roots_X_pow_card_sub_X L
  have hgsplits : g.Splits := by
    rw [splits_iff_card_roots, hgroots, hgdeg]
    exact Finset.card_univ
  -- The (finite) set of monic irreducible polynomials whose degree divides `d`.
  set A : Set F[X] := {P : F[X] | P.Monic ∧ Irreducible P ∧ P.natDegree ∣ d} with hAdef
  have hA : A.Finite := by
    refine (finite_setOf_natDegree_le F d).subset ?_
    rintro P ⟨-, -, hPd⟩
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hPd
  set S : Finset F[X] := hA.toFinset with hSdef
  have hmemS : ∀ P : F[X], P ∈ S ↔ (P.Monic ∧ Irreducible P ∧ P.natDegree ∣ d) := by
    intro P; rw [hSdef, Set.Finite.mem_toFinset]; rfl
  -- Every element of `L` has minimal polynomial in `S`.
  have hmaps : ∀ x : L, minpoly F x ∈ S := by
    intro x
    have hint : IsIntegral F x := IsIntegral.of_finite F x
    refine (hmemS _).mpr ⟨minpoly.monic hint, minpoly.irreducible hint, ?_⟩
    refine Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (minpoly.irreducible hint) ?_
    refine minpoly.dvd F x ?_
    simp only [map_sub, map_pow, aeval_X]
    rw [hq, FiniteField.pow_card, sub_self]
  -- The fibre over a monic irreducible `P` is the root set of `P` in `L`, of size `deg P`.
  have key : ∀ P ∈ S,
      (Finset.univ.filter (fun x : L ↦ minpoly F x = P)).card = P.natDegree := by
    intro P hP
    obtain ⟨hmonic, hirr, hPd⟩ := (hmemS P).mp hP
    have hPdvd : P ∣ (X ^ Nat.card F ^ d - X : F[X]) :=
      hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hPd
    have hPmap0 : P.map (algebraMap F L) ≠ 0 := (hmonic.map _).ne_zero
    have hmap : P.map (algebraMap F L) ∣ g := by
      have h := Polynomial.map_dvd (algebraMap F L) hPdvd
      rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, hq, ← hgdef] at h
    have hsplits : (P.map (algebraMap F L)).Splits := hgsplits.of_dvd hg0 hmap
    have hcard : Multiset.card (P.map (algebraMap F L)).roots = P.natDegree := by
      rw [splits_iff_card_roots.mp hsplits, Polynomial.natDegree_map]
    have hnodup : (P.map (algebraMap F L)).roots.Nodup := by
      refine Multiset.nodup_of_le (Polynomial.roots.le_of_dvd hg0 hmap) ?_
      rw [hgroots]
      exact Finset.univ.nodup
    have hfib : (Finset.univ.filter (fun x : L ↦ minpoly F x = P))
        = (P.map (algebraMap F L)).roots.toFinset := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
        Polynomial.mem_roots hPmap0, Polynomial.IsRoot.def, Polynomial.eval_map,
        ← Polynomial.aeval_def]
      constructor
      · rintro rfl; exact minpoly.aeval F x
      · intro h; exact (minpoly.eq_of_irreducible_of_monic hirr h hmonic).symm
    rw [hfib, Multiset.toFinset_card_of_nodup hnodup, hcard]
  -- Count `L` fibrewise over `S`.
  have h1 : Fintype.card L = ∑ P ∈ S, P.natDegree := by
    rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := fun x : L ↦ minpoly F x) (t := S)
        (fun x _ ↦ hmaps x)]
    exact Finset.sum_congr rfl fun P hP ↦ key P hP
  -- Regroup the sum over `S` by degree.
  have h2 : ∑ P ∈ S, P.natDegree = ∑ e ∈ d.divisors, e * numMonicIrreducibleOfDegree F e := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun P : F[X] ↦ P.natDegree) (t := d.divisors)
      (fun P hP ↦ Nat.mem_divisors.mpr ⟨((hmemS P).mp hP).2.2, hd⟩)]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    rw [Finset.sum_congr rfl fun P hP ↦ (Finset.mem_filter.mp hP).2, Finset.sum_const,
      smul_eq_mul, mul_comm]
    congr 1
    rw [Polynomial.numMonicIrreducibleOfDegree, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun P ↦ ?_)
    rw [Finset.mem_filter, hmemS]
    constructor
    · rintro ⟨⟨hm, hi, -⟩, hdeg⟩
      exact ⟨hm, hi, hdeg⟩
    · rintro ⟨hm, hi, hdeg⟩
      exact ⟨⟨hm, hi, by rw [hdeg]; exact (Nat.mem_divisors.mp he).1⟩, hdeg⟩
  rw [← h2, ← h1, ← hq]
