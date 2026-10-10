# MISSION: the Li coefficients of the Davenport-Heilbronn function

**Opened 2026-09-10.** Nothing in this directory is a result. It is a hunt
(`hunts/README.md`): exploratory work, recorded before any control has been run
against it, and the strongest words it may use are *measured*, *observed* and
*consistent with*. The reserved enclosure word belongs to `zeta/rigor.py` and
appears nowhere here except where a quoted artifact forced a visible mask, which
`RESULTS.md` records.

Scope, stated once: **nothing in this hunt is evidence about the Riemann
Hypothesis** (`docs/08`). The Davenport-Heilbronn function is not zeta, it has no
Euler product, and it already violates its own analogue of RH. Every number below
is about that function.

## The question

Bombieri and Lagarias (1999, Theorem 1) prove an equivalence for any multiset R
of complex numbers closed under `rho -> 1 - rho` and satisfying their convergence
condition:

    lambda_n(R) = sum_rho [ 1 - (1 - 1/rho)^n ]  >=  0  for every n >= 1
    <=>  every rho in R has Re rho = 1/2.

The Davenport-Heilbronn function f has an off-line zero pair measured at
`0.80851718... + 85.69934848...i` (`zeta.epstein.OFFLINE_ZERO_RE`,
`hunts/flow_repair`), so the equivalence says that **some lambda_n(DH) is
negative**. No one appears to have computed the sequence.

> **What are the Li coefficients of the Davenport-Heilbronn function, how far can
> n be pushed unconditionally on one 4-vCPU container, are they all positive
> there, and where does a DH background asymptotic measured from those same
> coefficients put the first negative index?**

The route is fixed in advance and it is the one that never reads a zero list:
mirror `zeta.li._li_cauchy` for the completed function

    F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s),   F(s) = F(1-s),

substitute s = 1/(1-z), unwrap the logarithm along the sampling circle, check the
winding number, and read lambda_n = n * [z^n] log F(1/(1-z)) off one equispaced
trapezoid DFT. The analyticity radius is established first, by the argument
principle, and not assumed.

## Why the radius argument is the whole gate

For any zero rho, z = 1 - 1/rho has |z| = |rho - 1|/|rho|, so |z| <= r holds
exactly on the Apollonius disc |s - 1/(1-r^2)| <= r/(1-r^2). Equivalently every
zero with |rho| >= 1/(1-r) is outside the disc of radius r. Zeros **on** the
critical line map to |z| = 1 exactly and can never enter. So the radius is
governed by low-lying zeros with Re > 1/2 only, and r = 0.9 needs f to have no
zero inside the disc centred 5.263157... of radius 4.736842..., whose part with
Re s <= 2 is contained in the rectangle [0.526, 2] x [-3.44, 3.44]. Above Re s = 2
`zeta.epstein` already pins `sum_{n>=2} |a_n| n^{-2} = 0.2666... < 1`, so f cannot
vanish there. This is the same shape of argument as `zeta.li.RADIUS_MAX`, and like
it, it appeals to no unproved hypothesis.

## Preregistered predictions

- **P1.** The identical pipeline pointed at `zeta.core.xi` reproduces
  `zeta.li.li_coefficients` to the digits that module states. Run first.
- **P2.** lambda_n(DH) extracted at r in {0.5, 0.7, 0.9} agree to within the
  round-off amplification r^{-n} that the working-precision rule already charges
  for. Disagreement beyond it means the branch or the winding check is wrong.
- **P3.** The argument-principle scan finds no zero of f with Re s > 1/2 and
  |rho| < 10, so r = 0.9 is admissible.
- **P4.** Every computed lambda_n(DH) with n <= n_max is positive, because the
  dominant off-line quadruple's amplitude 2(R^n + R^-n) with R - 1 = 4.2e-5 is
  still O(1) at n = 2000 while the background is O(n log n).
- **P5.** A background of the form a n log n + b n + c fitted to the measured
  lambda_n(DH) recovers a = 1/2 and b = (log(5/(2 pi)) + euler - 1)/2 = -0.3256...,
  the conductor-5 analogue of `zeta.li.li_asymptotic`, to within the residual
  oscillation.
- **P6.** The first negative index implied by that measured background plus the
  fifteen known off-line quadruples lands in [1e5, 1e6].

## What this hunt is not allowed to do

It may not touch `zeta/`, `tests/`, `docs/`, `hunts/README.md` or any other hunt.
It may not run git. It may not call a positive lambda_n table evidence that the
Davenport-Heilbronn function satisfies anything, and it may not call a computed
sequence a theorem.

```huntspec
id: li_dh_onset
question: What are the Li coefficients lambda_n of the Davenport-Heilbronn function, how far can n be pushed unconditionally on one container, are they all positive there, and where does a measured DH background put the first negative index?
frontier: no published lambda_n(DH) at any n; the one prior estimate is hunts/jensen_clock phase 3 Q6, n ~ 3.3e5, from a zeta-shaped background and hedged by its own page as order-of-magnitude
proposed_attack: mirror zeta.li._li_cauchy on the completed DH function, equispaced trapezoid DFT of the unwrapped log of F(1/(1-z)) on |z| = r, with the analyticity radius established first by the argument principle
dead_routes:
  - the envelope-crossing indicator of hunts/jensen_clock phase 3, which compared 2 r^n against lambda_n itself and fired at n = 1 because lambda_1 is 0.023; that page declares it useless and it is not reused here
  - reading lambda_n(DH) off a zero list as the primary route, which would import every completeness assumption the zero hunt carries
required_oracles:
  - the same Cauchy pipeline pointed at xi, reproducing zeta.li.li_coefficients to its stated digits
  - radius independence of the extracted coefficients across r in 0.5, 0.7, 0.9
  - zeta.epstein.dh_functional_equation_defect and dh_mean_value_defect on the evaluator
  - argument-principle zero counts from zeta.epstein.count_zeros_box
  - a partial zero-side reconstruction from measured on-line ordinates and the known off-line quadruples
kill_conditions:
  - the extracted lambda_n(DH) differ across radii beyond the stated round-off amplification, in which case the branch or the winding check is wrong and every number here is withdrawn
  - the xi control fails to reproduce zeta.li.li_coefficients
  - the argument-principle scan finds a zero of f with Re s > 1/2 and modulus small enough to force the radius below 0.7, in which case only the small-n table survives
  - a computed lambda_n(DH) goes negative at small n, which is first a defect in this pipeline and not a discovery
agents_may:
  - derive
  - code
  - measure
  - attack their own pipeline
  - state a grade on the certainty ladder
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - write any sentence implying a computation bears on the Riemann Hypothesis
```
