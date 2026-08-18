/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.HardyRamanujantheorem
import ZetaLean.MertensSecond

/-!
# Declaration probe for hunt r_8c3b94 (pricing Erdős–Kac)

This file exists to make the hunt's Mathlib claims checkable rather than
grep-based.  Every `#check` below either resolves at the pin recorded in
`lean/lake-manifest.json` (mathlib `51e6992e`, toolchain `v4.33.0-rc2`) or the
file fails to compile.  It proves nothing mathematical and is imported by
nothing; it is the evidence behind the `found: true` rows of `results.json`.

The misses are recorded in `results.json` and cannot be probed this way: a
name that does not exist produces an error, not a fact.  What this file does
establish is that the *hits* are real and have the shape the pricing assumes.

Run with:

    cd lean && PATH="$HOME/.elan/bin:$PATH" \
      lake env lean ../hunts/r_8c3b94/Probe.lean
-/

open MeasureTheory ProbabilityTheory Filter Finset

section Probability

-- The CLT Mathlib actually has: i.i.d. only.  Note `hindep : iIndepFun X P`
-- and `hident : ∀ i, IdentDistrib (X i) (X 0) P P`.  Both hypotheses fail for
-- the prime indicators `n ↦ if p ∣ n then 1 else 0`.
#check @ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
#check @ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum
#check @ProbabilityTheory.charFun_inv_sqrt_mul_sum

-- Lévy's continuity theorem: present, and it is the hinge of both routes'
-- final step.
#check @MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun

-- The characteristic-function toolkit the CLT proof is built from.
#check @MeasureTheory.charFun
#check @ProbabilityTheory.charFun_gaussianReal
#check @MeasureTheory.taylor_charFun_two
#check @ProbabilityTheory.iIndepFun

-- Convergence in distribution is indexed by a *family* of measure spaces
-- `(i : ι) → Ω i → E`, so the arithmetic setting (the space changes with N)
-- fits the existing definition without a new one.
#check @MeasureTheory.TendstoInDistribution

-- Moments: the definitions exist; no theorem links moment convergence to
-- convergence in distribution.
#check @ProbabilityTheory.moment
#check @ProbabilityTheory.centralMoment
#check @ProbabilityTheory.centralMoment_two_eq_variance
#check @ProbabilityTheory.mgf
#check @ProbabilityTheory.iteratedDeriv_mgf_zero   -- `mgf ↔ moment` link
#check @ProbabilityTheory.analyticAt_mgf

-- The Gaussian: mean and variance only.
#check @ProbabilityTheory.gaussianReal
#check @ProbabilityTheory.integral_id_gaussianReal
#check @ProbabilityTheory.variance_id_gaussianReal

-- Tightness / Prokhorov, the plumbing a method-of-moments theorem would need.
#check @MeasureTheory.IsTightMeasureSet
-- root namespace, not `MeasureTheory`; the qualified spelling is a miss
#check @isCompact_closure_of_isTightMeasureSet

-- The uniform measure on a finite set, for the arithmetic probability space.
#check @ProbabilityTheory.uniformOn
#check @ProbabilityTheory.uniformOn_apply_finset

end Probability

section NumberTheory

-- ω, in Mathlib's own vocabulary.  `ZetaLean.HardyRamanujan.omega` is `rfl`
-- to this.
#check @ArithmeticFunction.cardDistinctFactors
#check @ArithmeticFunction.cardDistinctFactors_mul

-- Chebyshev: explicit two-sided bounds on π.  These are what bounds the
-- k-fold error term `O(π(y)^k)` of the moment route.
#check @Chebyshev.pi_le_log4_mul_div
#check @Chebyshev.pi_ge
#check @Chebyshev.theta_le_log4_mul_x
#check @Chebyshev.psi_le_const_mul_self

-- Divergence of ∑ 1/p, with no rate.  Mathlib has no Mertens theorem.
#check @Nat.Primes.not_summable_one_div

-- The sieve Mathlib has: the Selberg setup and the Λ² upper bound.  There is
-- no lower-bound sieve and no fundamental lemma.  (Root namespace
-- `BoundingSieve`, not `SelbergSieve.*`; the latter spelling is a miss.)
#check @BoundingSieve
#check @BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
#check @BoundingSieve.upperMoebius_lambdaSquared

-- Smooth numbers, for the y-truncation of ω.
#check @Nat.smoothNumbers

-- The counting lemma the k = 2 moment already uses.
#check @Nat.Ioc_filter_dvd_card_eq_div

end NumberTheory

section Combinatorics

-- Stirling numbers of the second kind: the recurrence and small values only.
-- No bijection to set partitions, no falling-factorial identity, so the
-- partition bookkeeping of the k-th moment gets no help here.
#check @Nat.stirlingSecond
#check @Nat.stirlingSecond_succ_succ

-- Double factorial: the definition and the factorial identity.  `(2m-1)‼` is
-- the Gaussian moment the route has to land on; nothing states that.
#check @Nat.doubleFactorial
#check @Nat.factorial_eq_mul_doubleFactorial

-- The half-integer Gamma values, which are one change of variables away from
-- the even Gaussian moments.
#check @Real.Gamma_nat_add_half
#check @Real.Gamma_nat_add_one_add_half
#check @integral_gaussian

-- Partitions of a finite set, the natural index for the k-th moment
-- expansion.  Present as a structure; no `Finset.sum` reindexing lemma ties
-- it to `stirlingSecond`.
#check @Finpartition

end Combinatorics

section ThisTree

-- The base this run is pricing against, all on `main`, zero sorrys.
#check @ZetaLean.HardyRamanujan.hardy_ramanujan
#check @ZetaLean.HardyRamanujan.hardy_ramanujan_pointwise
#check @ZetaLean.HardyRamanujan.hardy_ramanujan_cardDistinctFactors
#check @ZetaLean.HardyRamanujan.omega_eq_cardDistinctFactors
#check @ZetaLean.HardyRamanujan.sum_sq_dev_le          -- Turán, constant 275
#check @ZetaLean.HardyRamanujan.second_moment_upper    -- the k = 2 moment
#check @ZetaLean.HardyRamanujan.card_dvd_pair          -- the k = 2 pair count
#check @ZetaLean.Mertens.mertens_second_theorem        -- band 16
#check @ZetaLean.Mertens.mertens_first_theorem         -- band log 4 + 3

end ThisTree
