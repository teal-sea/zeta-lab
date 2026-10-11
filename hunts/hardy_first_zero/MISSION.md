# MISSION: `hardy_first_zero`, a kernel-checked zero of zeta on the critical line near 14.13

The lab's Hardy Z development (`lean/ZetaLean/HardyZ.lean`: `hardyZ`, `hardyZReal`,
`|Z(t)| = |zeta(1/2 + it)|`, `hardyZReal_zero_iff`, `continuous_hardyZReal`) has been
accepted upstream into Mathlib. The owner approved the next goal on 2026-10-11: a Lean
theorem, zero sorrys and standard axioms only, of the form

    ∃ t ∈ Set.Ioo a b, riemannZeta (1/2 + t * I) = 0

with `a`, `b` rational near `gamma_1 = 14.134725141734694`, proved by a sign change of
`hardyZReal` and the intermediate value theorem.

## The exact target

    theorem first_zero_on_line :
        ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50), riemannZeta (1 / 2 + t * I) = 0

that is, a zero `1/2 + it` with `14.13 < t < 14.14`. The interval is the smallest one with
two-decimal endpoints that contains `gamma_1`; `RESULTS.md` section 4 prices narrower ones.

## Scope

- **In scope.** The map of what Mathlib (at the revision `lean/lake-manifest.json` pins) and
  the lab's own Lean already provide for `riemannZeta` on `Re s = 1/2`; the choice of route,
  sized by measured constants before any Lean is written; the prior-art search; Lean under
  `hunts/hardy_first_zero/lean/`, compiled file by file against the pinned Mathlib and the
  lab's built `ZetaLean` modules.
- **Out of scope.** Edits to `lean/ZetaLean/`, `zeta/`, `ontology/`, `harness/`. A full
  `lake build` of the certificate packages (about 10 GB). Any statement about zeros beyond the
  one interval. Nothing here bears on RH (`docs/08`): one zero on the line says nothing about
  the others.
- **Budget.** One session for the map, the sizing, the search and the first Lean; the box
  evaluation to be priced before it is spent. Lean compiles run one at
  a time and never beside the numerics (`CLAUDE.md`, compute discipline).

**Status at the end of the opening session, 2026-10-11.** The target theorem compiles, zero
sorrys, standard axioms (`RESULTS.md`). The box evaluation was priced by measurement first
(`RUNS.md`, `decide-one-term` and `decide-sum30`) and then spent: about three minutes of
kernel time. What remains is review and the owner's decision on landing.

```huntspec
id: hardy_first_zero
question: Can Lean 4 with Mathlib prove that zeta has a zero 1/2 + it with t strictly between 1413/100 and 707/50, by a sign change of hardyZReal and the intermediate value theorem, with zero sorrys and standard axioms only?
frontier: at the pinned Mathlib revision riemannZeta has no representation on Re s = 1/2 with an explicit error bound, no Euler-Maclaurin formula and no bound on the digamma function; the lab has hardyZReal with continuity and the zero criterion, rational interval boxes for n^(-s), and a trapezoid remainder lemma; no formal localization of an explicit nontrivial zero was found in the searched set
proposed_attack: reduce the zero to Re(zeta(s_a) conj zeta(s_b)) < 0 plus a crude bound on how far the phase of Gammaℝ turns between the endpoints, prove that bound from Euler's limit GammaSeq to Gamma, and evaluate zeta at the two rational endpoints through an order-4 Euler-Maclaurin remainder and rational interval boxes
dead_routes:
  - Riemann-Siegel with Gabcke's remainder, one main term at t = 14.13 but a long unformalized remainder analysis
  - the order-2 trapezoid remainder alone, which needs 471 terms per endpoint against 15 at order 4
  - bounding the Gamma phase through the integral for Gamma prime, an absolute bound of order 1 against a Gamma value near 2e-5
  - deciding the sign of Lambda(1/2 + it) by quadrature of the theta integral, whose integrand cancels to 1e-7 from terms of size 1e-2
required_oracles:
  - the Lean 4 kernel at the pinned Mathlib revision, with zero sorrys and printed axioms
  - Arb ball arithmetic through python-flint, cross-checked against mpmath interval arithmetic
  - the bit-exact rational mirror of the interval layer in scripts/61_rung3_mirror.py
kill_conditions:
  - an Arb enclosure of zeta at either endpoint violates the order-4 remainder bound the plan relies on
  - the kernel refuses the box evaluation at every parameter set the mirror says should pass
  - a formal localization of an explicit nontrivial zero turns up in prior work, in which case this hunt reports a reproduction and not a first
agents_may:
  - compute, derive and formalize under hunts/hardy_first_zero/
  - search the literature and say what was searched and found
agents_may_not:
  - edit lean/ZetaLean, zeta, ontology or harness
  - call a lemma kernel-checked that carries a sorry or was not compiled
  - declare novelty
  - promote their own claim
```
