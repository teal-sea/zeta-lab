/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Dominated convergence for nontrivial arithmetic cores

The repeated-prime step in `hunts/higher_xi/RAMS2-CLUSTER.md` splits an integer
into a nontrivial powerful core and a squarefree remainder.  Its final passage
to the limit has a generic functional-analytic shape: every fixed nontrivial
core contribution vanishes, while all contributions are bounded by one
summable harmonic majorant.

This file formalizes exactly that reusable shape.  The predicate selecting the
cores is an argument, so no unproved characterization of powerful integers is
built in.  Establishing the concrete Cauchy bound, the summability of its
arithmetic majorant, and any asymptotic remain separate obligations.
-/

namespace ZetaLean.HigherXi

open Filter Topology

/-- Indices selected by an arithmetic core predicate, excluding the trivial
core `1`.  For the RAMS2 application the predicate will be “powerful”. -/
def NontrivialCoreIndex (isCore : ℕ → Prop) :=
  {q : ℕ // isCore q ∧ q ≠ 1}

/-- The total contribution of all nontrivial selected cores. -/
noncomputable def nontrivialCoreMass
    {A E : Type*} [NormedAddCommGroup E]
    (isCore : ℕ → Prop) (term : A → ℕ → E) (a : A) : E :=
  ∑' q : NontrivialCoreIndex isCore, term a q.1

/-- A summable majorant controls every restricted collection of nontrivial
cores.  This is the quantitative tail estimate used after finitely many cores
or primes have been peeled. -/
theorem norm_tsum_nontrivialCore_restrict_le
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {isCore : ℕ → Prop} {term : ℕ → E} {majorant : ℕ → ℝ}
    (hmajorant : Summable
      (fun q : NontrivialCoreIndex isCore ↦ majorant q.1))
    (hterm : ∀ q : NontrivialCoreIndex isCore, ‖term q.1‖ ≤ majorant q.1)
    (s : Set (NontrivialCoreIndex isCore)) :
    ‖∑' q : s, term q.1.1‖ ≤ ∑' q : s, majorant q.1.1 := by
  have hnorm : Summable
      (fun q : NontrivialCoreIndex isCore ↦ ‖term q.1‖) :=
    hmajorant.of_norm_bounded fun q ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hterm q
  apply (norm_tsum_le_tsum_norm (hnorm.subtype s)).trans
  exact (hnorm.subtype s).tsum_le_tsum
    (fun q ↦ hterm q.1) (hmajorant.subtype s)

/-- Every parameter value satisfying the domination hypothesis has an
absolutely summable nontrivial-core family. -/
theorem summable_nontrivialCore_of_dominated
    {A E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {isCore : ℕ → Prop} {term : A → ℕ → E}
    {majorant : ℕ → ℝ} {a : A}
    (hmajorant : Summable
      (fun q : NontrivialCoreIndex isCore ↦ majorant q.1))
    (hterm : ∀ q : NontrivialCoreIndex isCore,
      ‖term a q.1‖ ≤ majorant q.1) :
    Summable (fun q : NontrivialCoreIndex isCore ↦ term a q.1) :=
  hmajorant.of_norm_bounded hterm

/-- Dominated pointwise vanishing removes every nontrivial arithmetic-core
stratum in the limit.  The arithmetic work is isolated in two explicit
hypotheses: summability of `majorant` on the chosen cores and the eventual
uniform bound by that majorant. -/
theorem tendsto_nontrivialCoreMass_zero_of_dominated
    {A E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : Filter A} {isCore : ℕ → Prop} {term : A → ℕ → E}
    {majorant : ℕ → ℝ}
    (hmajorant : Summable
      (fun q : NontrivialCoreIndex isCore ↦ majorant q.1))
    (hzero : ∀ q : NontrivialCoreIndex isCore,
      Tendsto (fun a ↦ term a q.1) F (nhds 0))
    (hbound : ∀ᶠ a in F, ∀ q : NontrivialCoreIndex isCore,
      ‖term a q.1‖ ≤ majorant q.1) :
    Tendsto (nontrivialCoreMass isCore term) F (nhds 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (G := E) hmajorant hzero hbound
  change Tendsto (fun a ↦
    ∑' q : NontrivialCoreIndex isCore, term a q.1) F (nhds 0)
  simpa only [tsum_zero] using h

/-- A convenient real nonnegative specialization.  It makes the exact
harmonic-majorant boundary visible for the intended squared-mass terms. -/
theorem tendsto_nontrivialCoreMass_zero_of_nonneg_dominated
    {A : Type*} {F : Filter A} {isCore : ℕ → Prop}
    {term : A → ℕ → ℝ} {majorant : ℕ → ℝ}
    (hmajorant : Summable
      (fun q : NontrivialCoreIndex isCore ↦ majorant q.1))
    (hterm_nonneg : ∀ a q, 0 ≤ term a q)
    (hzero : ∀ q : NontrivialCoreIndex isCore,
      Tendsto (fun a ↦ term a q.1) F (nhds 0))
    (hbound : ∀ᶠ a in F, ∀ q : NontrivialCoreIndex isCore,
      term a q.1 ≤ majorant q.1) :
    Tendsto (nontrivialCoreMass isCore term) F (nhds 0) := by
  apply tendsto_nontrivialCoreMass_zero_of_dominated hmajorant hzero
  filter_upwards [hbound] with a ha
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (hterm_nonneg a q.1)]
  exact ha q

end ZetaLean.HigherXi
