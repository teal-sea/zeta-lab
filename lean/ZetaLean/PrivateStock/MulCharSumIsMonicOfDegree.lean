import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ZetaLean.PrivateStock.FiniteIsMonicOfDegree

/-!
# Character sums over monic polynomials of a given degree

Let `F` be a finite field, let `Q ∈ F[X]` have degree `d ≥ 1` and let `χ` be a nontrivial
multiplicative character of `F[X] ⧸ (Q)`. If `n ≥ d`, then the monic polynomials of degree `n`
are equidistributed among the residue classes mod `Q`, so `∑ χ(f mod Q) = 0`.

The equidistribution is packaged as `Polynomial.bijective_quotientMk_degreeLT`: the polynomials
of degree `< d` are a complete and irredundant set of representatives for `F[X] ⧸ (Q)`. Adding
such a representative to a monic polynomial of degree `n ≥ d` keeps it monic of degree `n`, so
the (finite) sum is invariant under those translations while their average over all translations
is a full character sum over `F[X] ⧸ (Q)`, which vanishes.
-/

set_option autoImplicit false

open scoped Polynomial

namespace Polynomial

/-- The polynomials of degree `< Q.natDegree` form a complete and irredundant set of
representatives for `F[X] ⧸ (Q)`. -/
theorem bijective_quotientMk_degreeLT {F : Type*} [Field F] {Q : F[X]} (hQ : Q ≠ 0) :
    Function.Bijective fun p : degreeLT F Q.natDegree ↦
      Ideal.Quotient.mk (Ideal.span {Q}) (p : F[X]) := by
  constructor
  · intro p p' h
    simp only at h
    have h0 : Ideal.Quotient.mk (Ideal.span {Q}) ((p : F[X]) - (p' : F[X])) = 0 := by
      rw [map_sub, h, sub_self]
    have hdvd : Q ∣ ((p : F[X]) - (p' : F[X])) :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    have hmem : ((p : F[X]) - (p' : F[X])) ∈ degreeLT F Q.natDegree :=
      (degreeLT F Q.natDegree).sub_mem p.2 p'.2
    rw [mem_degreeLT] at hmem
    have hz : (p : F[X]) - (p' : F[X]) = 0 := by
      by_contra hne
      exact hne (eq_zero_of_dvd_of_natDegree_lt hdvd
        ((natDegree_lt_iff_degree_lt hne).mpr hmem))
    exact Subtype.ext (sub_eq_zero.mp hz)
  · intro a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hmonic : (Q * C (Q.leadingCoeff)⁻¹).Monic := monic_mul_leadingCoeff_inv hQ
    refine ⟨⟨g %ₘ (Q * C (Q.leadingCoeff)⁻¹), ?_⟩, ?_⟩
    · rw [mem_degreeLT]
      refine lt_of_lt_of_le (degree_modByMonic_lt g hmonic) ?_
      rw [degree_mul_leadingCoeff_self_inv, degree_eq_natDegree hQ]
    · simp only
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact dvd_trans (dvd_mul_right Q _)
        (dvd_modByMonic_sub g (Q * C (Q.leadingCoeff)⁻¹))

end Polynomial

namespace MulChar

open Polynomial

/-- The sum of a nontrivial multiplicative character over a full set of residues vanishes,
even after an additive shift. -/
private theorem sum_add_left_eq_zero {R : Type*} [CommRing R] [Fintype R]
    {χ : MulChar R ℂ} (hχ : χ ≠ 1) (c : R) : ∑ a : R, χ (c + a) = 0 :=
  (Fintype.sum_equiv (Equiv.addLeft c) _ _ fun _ ↦ rfl).trans (sum_eq_zero_of_ne_one hχ)

/-- For `n` at least the degree of `Q`, the monic polynomials of degree `n` hit every residue
class mod `Q` equally often, so a nontrivial character of `F[X] ⧸ (Q)` sums to zero over them. -/
theorem sum_isMonicOfDegree_eq_zero {F : Type*} [Field F] [Fintype F] {Q : F[X]}
    (hQ : 1 ≤ Q.natDegree) {χ : MulChar (F[X] ⧸ Ideal.span {Q}) ℂ} (hχ : χ ≠ 1) {n : ℕ}
    (hn : Q.natDegree ≤ n) :
    ∑' f : {f : F[X] // Polynomial.IsMonicOfDegree f n},
      χ (Ideal.Quotient.mk (Ideal.span {Q}) (f : F[X])) = 0 := by
  have hQ0 : Q ≠ 0 := fun h ↦ by simp [h] at hQ
  have hn0 : 0 < n := lt_of_lt_of_le hQ hn
  have : Finite {f : F[X] // IsMonicOfDegree f n} := finite_isMonicOfDegree n
  have : Fintype {f : F[X] // IsMonicOfDegree f n} := Fintype.ofFinite _
  have : Finite (degreeLT F Q.natDegree) :=
    Finite.of_equiv _ (degreeLTEquiv F Q.natDegree).toEquiv.symm
  have : Fintype (degreeLT F Q.natDegree) := Fintype.ofFinite _
  have : Nonempty (degreeLT F Q.natDegree) := ⟨0⟩
  have hbij := bijective_quotientMk_degreeLT hQ0
  have : Finite (F[X] ⧸ Ideal.span {Q}) := Finite.of_surjective _ hbij.2
  have : Fintype (F[X] ⧸ Ideal.span {Q}) := Fintype.ofFinite _
  rw [tsum_fintype]
  -- Summing over all translations by a polynomial of degree `< Q.natDegree`, with the monic
  -- polynomial fixed, gives a full character sum, hence zero.
  have key : ∀ f : {f : F[X] // IsMonicOfDegree f n},
      ∑ p : degreeLT F Q.natDegree,
        χ (Ideal.Quotient.mk (Ideal.span {Q}) ((f : F[X]) + (p : F[X]))) = 0 := by
    intro f
    calc ∑ p : degreeLT F Q.natDegree,
          χ (Ideal.Quotient.mk (Ideal.span {Q}) ((f : F[X]) + (p : F[X])))
        = ∑ p : degreeLT F Q.natDegree, χ (Ideal.Quotient.mk (Ideal.span {Q}) (f : F[X]) +
            Ideal.Quotient.mk (Ideal.span {Q}) (p : F[X])) := by
          simp only [map_add]
      _ = ∑ a : F[X] ⧸ Ideal.span {Q},
            χ (Ideal.Quotient.mk (Ideal.span {Q}) (f : F[X]) + a) :=
          Fintype.sum_bijective _ hbij _ _ fun _ ↦ rfl
      _ = 0 := sum_add_left_eq_zero hχ _
  -- Each such translation is a bijection of the monic polynomials of degree `n`.
  have key2 : ∀ p : degreeLT F Q.natDegree,
      ∑ f : {f : F[X] // IsMonicOfDegree f n},
          χ (Ideal.Quotient.mk (Ideal.span {Q}) ((f : F[X]) + (p : F[X])))
        = ∑ f : {f : F[X] // IsMonicOfDegree f n},
            χ (Ideal.Quotient.mk (Ideal.span {Q}) (f : F[X])) := by
    intro p
    have hpd : (p : F[X]).natDegree < n := by
      rcases eq_or_ne (p : F[X]) 0 with h | h
      · rw [h, natDegree_zero]; exact hn0
      · exact lt_of_lt_of_le ((natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp p.2)) hn
    exact Fintype.sum_equiv
      { toFun := fun f ↦ ⟨(f : F[X]) + (p : F[X]), f.2.add_right hpd⟩
        invFun := fun f ↦ ⟨(f : F[X]) - (p : F[X]), f.2.sub hpd⟩
        left_inv := fun f ↦ by ext; simp
        right_inv := fun f ↦ by ext; simp } _ _ fun _ ↦ rfl
  have hsum : ∑ p : degreeLT F Q.natDegree, ∑ f : {f : F[X] // IsMonicOfDegree f n},
      χ (Ideal.Quotient.mk (Ideal.span {Q}) ((f : F[X]) + (p : F[X]))) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun f _ ↦ key f
  rw [Finset.sum_congr rfl fun p _ ↦ key2 p, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_eq_zero] at hsum
  rcases hsum with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) Fintype.card_ne_zero
  · exact h

end MulChar
