# Private stock

Lean 4 declarations this laboratory formalized because it needed them, kept here
rather than sent upstream. Every one of them is a real gap in Mathlib 6f1ef4e:
each was found by an agent that grepped for it first and reported the absence,
and none is exotic. They are the ordinary lemmas that nobody happened to write.

Produced on 2026-09-04 while attacking `annals_chowla_and_twin_prime_over_fq_t`
on the lean-eval board, in the course of measuring what the Sawin-Shusterman
theorem actually needs. They outlived that question: the theorem is out of reach
(see the note at the end), these are not.

**Grade.** Kernel-checked, rung 3. `#print axioms` on every headline declaration
reports exactly `propext, Classical.choice, Quot.sound`. **Original** in the
sense the house uses the word: this laboratory produced them, and the git
history says so. **Not novel.** Every statement below is classical mathematics
that had not been written in Lean. The root-multiplicity characterisation is
Hasse, 1936. Recovering individual bounds from power sums is older than that.
Nothing here is a new theorem and the file does not claim one.

## What is in here

| Declaration | What it says |
| --- | --- |
| `Polynomial.card_isMonicOfDegree` | the monic polynomials of degree `n` over a finite field number `q^n` |
| `Polynomial.finite_isMonicOfDegree` | and there are finitely many of them |
| `Polynomial.card_mul_le_natDegree_of_le_rootMultiplicity` | `s` roots each of multiplicity `>= l` force `s.card * l <= P.natDegree` |
| `Polynomial.le_rootMultiplicity_iff_forall_hasseDeriv_eval_eq_zero` | `l <= rootMultiplicity x P` iff the first `l` Hasse derivatives vanish at `x` |
| `Polynomial.numMonicIrreducibleOfDegree` + `sum_degree_mul_..._eq_pow` | the mass formula for monic irreducibles |
| `Polynomial.isBigO_mul_numMonicIrreducibleOfDegree_sub_pow` | the prime polynomial theorem with its error term |
| `Polynomial.finsum_moebius_isMonicOfDegree_eq_zero` | the Moebius divisor-sum identity over `F[X]`, built from scratch |
| `Complex.norm_le_of_forall_norm_sum_pow_le` | if every power sum obeys `‖∑ ω i ^ k‖ <= C * B ^ k` then each `‖ω i‖ <= B` |
| `MulChar.sum_isMonicOfDegree_eq_zero` | character orthogonality over `F[X] / (Q)` |
| `Submonoid.map_pow_atTop_powers` | `atTop` on `Submonoid.powers q` transfers to `atTop` on the exponent |

The last two thirds of that list are the standard ingredients of **Stepanov's
elementary method** for the Weil bound on character sums, which is the reason
they were built. `Complex.norm_le_of_forall_norm_sum_pow_le` is the endgame move
of every proof of RH for curves: it is how you get from a bound on the power
sums to a bound on the individual Frobenius eigenvalues.

## Why this is private stock

No upstream submission is planned. The laboratory needed these declarations,
proved them, and will maintain them here for its own work and for anyone using
this repository. A previous upstream contribution remains unmerged, so more
submission work is not a useful allocation now. If a better library emerges,
or this laboratory eventually builds one, this stock can move there. Until
then, `PrivateStock` is its home.

## Provenance and how to re-check

Proved by agent cells a-0090 through a-0106 on the `lean-eval-unsolved` board,
each gated by `check-task.sh`: `lake build Submission`, no literal `sorry` in the
lines the attempt added, and `#print axioms` restricted to the three permitted
axioms. Re-verified here as a standalone set against Mathlib `6f1ef4e` on
`leanprover/lean4:v4.33.0`: 11 modules, 11 compiled, 0 failed, axioms clean.

## What is NOT here, and why

Five further declarations proved in the same run are bolted to the benchmark's
own definitions (`ChallengeDeps`: the norm on `F[X]`, `primes`, the singular
series `𝔖_q`) and do not stand alone:
`ChowlaAndTwinPrimeOverFqT.finite_monicBounded`, `.finite_setOf_norm_eq`,
`.ncard_setOf_norm_eq_isMonicOfDegree`, `.singularSeries_pos`, and
`.isBigO_one_tsum_moebius_monicBounded`. They live on the branch
`ost/lean-eval-unsolved/trunk` in the `lean-eval` checkout.

And the thing they were all for is not here either. Chowla and twin primes over
`F_q[T]` needs square-root cancellation in all `n` coefficient variables at once,
not in one. The classical one-variable Weil bound provably cannot reach it: a
mapper computed that naive fibering gives `k(n-1) * q^(n-1/2)` against a trivial
`q^n`, a ratio of `k(n-1)/sqrt(q)`, which exceeds 1 once `n > sqrt(q)/k + 1`.
Kowalski's Bourbaki exposition confirms Sawin and Shusterman needed three
separate bespoke cohomological arguments, because the off-the-shelf Betti number
bounds (Katz; Sawin's own quantitative sheaf theory) give a super-exponential
constant where an exponential one is required. That is the honest edge of what
this run established.
