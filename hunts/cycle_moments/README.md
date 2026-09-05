# Cycle moments and simple-real counting

Two finite counting improvements are proved here. Their application to a
stronger zeta-zero proportion remains open. The useful distinction is now
exact: second and third moments alone cannot force the improvement, whereas
a matched finite fourth-moment bound suffices.

The operator's intuition about repeated-term corrections led to a further
finite construction: one fixed positive Fourier kernel gives two point sets
with identical spectra and all power traces, but different distinct fourth
cycles. This isolates information discarded by a spectral summary. It does
not identify a defect in exact Möbius inversion or an improved zeta count.

The starting point is the adapted-subspace argument in
[Lamzouri, Proposition 2.1](https://arxiv.org/html/2609.02882v1).
The extensions and obstruction below were derived in this hunt. They are
original constructions, with no claim of established novelty. External
verification of the complete argument remains pending.

## What is proved

For the signed operator A representing simple points, multiple points, and
nonreal conjugate pairs, put M_j=tr(A^j) and N=M_1. If s counts simple real
points, the general theorem is

    tr f(A) <= s

for every globally concave f with f(0)=f(2)=0 and f<=1. A quartic family gives

    s >= [2N-M_2-t(M_3-3M_2+2N)
          +t^2(2N-5M_2+4M_3-M_4)] / [1+t^2/(4(1-t^2))],
    8t^2 <= 5.

[FINITE-THEOREM.md](FINITE-THEOREM.md) proves this and identifies every M_j
with the actual ordered kernel cycle sum of a finite conjugation-invariant
multiset. Multiplicities and nonreal contributions are retained. An exact
two-vector example improves the quadratic lower bound from 3/2 to 15/8.

At the Montgomery-Taylor profile the explicit third discrepancy is

    delta_3 = (6k-5)(6k^2+6k-1)/24 < 0,
    k = cot(1/sqrt(2))/sqrt(2).

Its negativity is proved by elementary inequalities and independently checked
with direct integration and 160-bit interval arithmetic. If the same counting
operator has the corresponding second and third limits and any finite
normalized fourth-moment bound, a small positive t gives a strict asymptotic
gain. Those matched analytic hypotheses are not established here.

[THIRD-MOMENT-OBSTRUCTION.md](THIRD-MOMENT-OBSTRUCTION.md) proves that the
fourth-moment or other tail control is necessary in the general signed-vector
class. Two allowed pairs give eigenvalues b+2,b+2,-2b. Adding this block to
quadratic-equality configurations matches both desired moment limits while
the limiting simple proportion stays at the quadratic bound. This is not a
construction of zeta zeros.

[MIXED-MOMENTS.md](MIXED-MOMENTS.md) supplies another finite improvement:

    s >= 2N-tr(A^2) + max(J,0)^2 / [9tr(B^4)],
    J = 3tr(AB^2)-tr(A^2B^2)-2tr(B^2),

for any self-adjoint B with tr(B^4)>0. It gives an exact 1/144 gain in a finite
example. Narrow profiles make the necessary mixed correlation statistics fit
within published Fourier support, but the tested profiles have negative J.

## Exact formal scope

The Lean files are standalone Mathlib inputs for Lean 4.33.0.

| File | What the kernel checks |
|---|---|
| [SpectralJensen.lean](SpectralJensen.lean) | Spectral Jensen from the matrix spectral theorem; the concave three-block argument; their composition given explicit diagonal-block hypotheses. |
| [QuarticScore.lean](QuarticScore.lean) | Actual derivatives, global concavity, endpoint identities, normalized upper bound, and the third-discrepancy sign under the stated bounds on k. |
| [CycleMomentAssembly.lean](CycleMomentAssembly.lean) | The exact standalone composition of the preceding two inputs, applying the normalized quartic to the explicit diagonal-block hypotheses. |
| [ThirdMomentObstruction.lean](ThirdMomentObstruction.lean) | The obstruction's scalar norm difference, four power sums, discrepancy, slack, and inequalities. |
| [DistinctCycles.lean](DistinctCycles.lean) | Exact third-order repeated-index inversion, including the +2N add-back, for a symmetric kernel over any commutative ring. |
| [IsospectralCycles.lean](IsospectralCycles.lean) | Complete unit-Gram counterexample: all power traces agree, but directly enumerated distinct fourth cycles differ. |

The construction of the adapted basis from signed vectors, the kernel-cycle
identification, the mixed matrix inequality, and the asymptotic arguments are
ordinary mathematical proofs. They are not included in the Lean claim.
AXLE receipts and exact source hashes are recorded in [FORMAL-CHECKS.json](FORMAL-CHECKS.json).

## What the repeated-term corrections retain

[MOBIUS-CORRECTIONS.md](MOBIUS-CORRECTIONS.md) derives the complete third and
fourth Möbius corrections. The triangle is exactly M_3-3M_2+2N. At fourth
order, two extra overlap statistics occur: the sum of squared row energies
and the sum of entrywise fourth powers. Replacing them with ordinary traces
would be an incorrect simplification.

[SAME-KERNEL-EXAMPLE.md](SAME-KERNEL-EXAMPLE.md) gives one fixed positive even
Fourier density and two explicit real point sets. Their full-rank Gram
matrices have identical eigenvalues, 15/16 twice and 17/16 twice, but their
distinct fourth cycles are -9/320000 and -225/14623232. The ordinary proof,
exact rational enumeration, and independent Fourier quadrature agree.
The example establishes loss of a statistic, not loss of a known percentage
in a zeta bound. Both point sets consist of four simple real points.

## Experiments and their limits

- [results.json](results.json): independent integration, interval sign check,
  exact finite example, direct complex cycle sums through degree four, and
  300 random signed configurations, including 238 indefinite operators.
- [cue_results.json](cue_results.json): 36 Haar-unitary draws at dimensions
  128, 256, and 512, with two frequency widths and two profiles per draw.
  These explore the quartic score. Optimizing its parameter on these samples
  is exploratory and does not establish a population gain.
- [mixed_integral_results.json](mixed_integral_results.json) and
  [mixed_integral_refined.json](mixed_integral_refined.json): complete
  two-, three-, and four-cycle constants, all pairing terms included, at
  two grid resolutions. The listed narrow and shifted profiles do not give
  a positive mixed numerator, even with optimized deterministic centering.
- [mixed_cue_results.json](mixed_cue_results.json): 12 further Haar-unitary
  draws at dimension 256. Mean-centered mixed observers also have negative
  averaged numerators in every tested case.
- [distinct_cycle_results.json](distinct_cycle_results.json): exact direct
  enumeration, independent partition inversion, and reduced formulas, with
  deliberately wrong simplifications detected by nonconstant kernels.
- [same_kernel_results.json](same_kernel_results.json): exact rational Gram
  identities and independent 45-digit Fourier integration for the fixed-kernel
  construction.

The cloud runs completed under Modal app IDs
`ap-kczpMD2GBPTaRhTYnB80L2` and `ap-yxAuPSoMKkEjFs6ZeLYQS2`.
These are finite random-matrix experiments, not estimates for zeta zeros.
No statement here gives evidence for RH or changes the laboratory's zeta bound.

## Reproduce

From the repository root:

```bash
.venv/bin/python hunts/cycle_moments/probe.py
.venv/bin/python hunts/cycle_moments/mixed_moments.py --self-check
.venv/bin/python hunts/cycle_moments/mixed_moments.py --grid-points 4801 --self-check
.venv/bin/python hunts/cycle_moments/distinct_cycles.py
.venv/bin/python hunts/cycle_moments/same_kernel.py
.venv/bin/python -m modal run hunts/cycle_moments/modal_probe.py
.venv/bin/python -m modal run hunts/cycle_moments/modal_mixed_probe.py
```

The last two commands start cloud jobs. Their seeds and dimensions are fixed
in the source. Existing JSON files preserve the completed runs.

For a standalone Lean file, use AXLE with `--environment lean-4.33.0`,
`--no-ignore-imports`, and `--no-theorems-only`; check the printed axioms as
well as elaboration. No result with an admitted proof is counted.

## The remaining analytic question

[Rudnick and Sarnak, Theorem 3.1, (3.8)-(3.9)](https://www.math.tau.ac.il/~rudnick/papers/nlevelDuke.pdf)
supplies the relevant smoothed all-index correlation formula, retaining
complex ordinates, within total Fourier support less than two. The mixed
note derives the complete constants and support costs. That theorem does not
itself supply an unconditional transfer to the counting operator's hard
height cutoff, nor the full-width fourth-moment bound required by the quartic
route. Those are concrete mathematical obligations, not completed steps.
