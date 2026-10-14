# MISSION: `hardy_ten_zeros`, ten kernel-checked zeros of zeta on the critical line below height 50

Hunt #132 (`hunts/hardy_first_zero/`, merged as `91848c0c`, PR #302) proved in Lean 4 with
the pinned Mathlib, zero sorrys and standard axioms only, that `riemannZeta (1/2 + t*I) = 0`
for some `t` strictly between `14.13` and `14.14`. The owner's next goal: at least ten
distinct zeros on the critical line with `0 < t < 50`, each localized in a short explicit
rational interval around the known ordinate (`14.134725`, `21.022040`, `25.010858`,
`30.424876`, `32.935062`, `37.586178`, `40.918719`, `43.327073`, `48.005151`, `49.773832`).

## The exact target

    theorem ten_zeros_on_line_below_fifty :
        ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
          ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ts k * I) = 0

together with one theorem per interval, of the form

    ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + t * I) = 0

with `a`, `b` the two-decimal rationals around each ordinate, as hunt #132 used for the
first. **What this is not**: it shows that there are at least ten zeros on the line below
height 50. It does not show that these are the ten lowest zeros, that each interval holds
exactly one zero, or that there are no other zeros below 50; that needs a zero count
(Turing's method, for example), which is out of scope.

## Scope

- **In scope.** Sizing first, in Python, before any heavy Lean: whether the phase lemma of
  hunt #132 survives at `t` near 50 (its window carries a term `2 K delta` with
  `K = ab/4`), how many Euler-Maclaurin terms each endpoint needs at order 4 and at higher
  orders, and the measured kernel cost of one term box at that height. Then Lean under
  `hunts/hardy_ten_zeros/lean/`, importing the `HardyFirstZero` modules compiled from the
  sibling directory's sources, generalizing that hunt's lemmas inside this directory; one
  generated box file per zero so builds are incremental and checkpoint per zero; a CI
  workflow that rebuilds the proof and audits its axiom reports fail-closed.
- **Out of scope.** Edits to `lean/ZetaLean/`, `zeta/`, `ontology/`, `harness/`, and to the
  files of hunt #132. A full `lake build`. Any claim about which zeros these are or about the
  zeros between them. Nothing here bears on RH (`docs/08`): ten zeros on the line say
  nothing about the others.
- **Budget and stop rule.** A few hours of kernel time in this container in total. If the
  sizing shows more, or the phase lemma needs mathematics that cannot be finished, stop and
  report the measured wall; a partial result (fewer than ten intervals) is landed as such.
  Lean compiles run one at a time and never beside heavy numerics (`CLAUDE.md`).

```huntspec
id: hardy_ten_zeros
question: Can Lean 4 with Mathlib prove that zeta has at least ten distinct zeros 1/2 + it with 0 < t < 50, each in an explicit two-decimal rational interval around a known ordinate, with zero sorrys and standard axioms only, by extending the sign test, phase lemma and order-4 Euler-Maclaurin evaluation of hunt 132?
frontier: hunt 132 proved one zero with 14.13 < t < 14.14 through a sign test, a quarter-turn bound on the phase of Gammaℝ from Euler's limit whose window grows like ab/2 times half the bracket width, an order-4 Euler-Maclaurin remainder with N = 30 fixed in its instantiation, and 60 kernel-checked term boxes; no formal localization of an explicit nontrivial zero other than that one was found in the searched set
proposed_attack: sharpen the lower end of the phase window by dropping the first terms of the partial phase so it no longer grows with ab, generalize the remainder instantiation to any truncation N with a squared-norm bound on s(s+1)(s+2)(s+3), choose the truncation per endpoint by measured cost, and generate one kernel-checked box file per interval
dead_routes:
  - the phase lemma of hunt 132 as stated, whose window exceeds a quarter turn at two-decimal brackets from the fourth ordinate on, because its lower end carries 2 K delta with K = ab/4
  - one decide +kernel over a whole recursive box sum, which hunt 132 measured at more than 30 minutes for 29 terms
required_oracles:
  - the Lean 4 kernel at the pinned Mathlib revision, with zero sorrys and printed axioms
  - Arb ball arithmetic through python-flint, cross-checked against mpmath interval arithmetic
  - the bit-exact rational mirror of the interval layer in scripts/61_rung3_mirror.py
kill_conditions:
  - an Arb enclosure of zeta at any endpoint violates the order-4 remainder bound the plan relies on
  - the measured kernel cost of the box evaluation for all ten intervals exceeds a few hours in this container
  - the sharpened phase window fails to stay inside a quarter turn at any planned bracket
  - a formal localization of several explicit nontrivial zeros turns up in prior work, in which case this hunt reports a reproduction and not a first
agents_may:
  - compute, derive and formalize under hunts/hardy_ten_zeros/
  - import and compile the hunt 132 Lean modules from their sources, without editing them
  - add a CI workflow that rebuilds this proof and audits its axioms
  - search the literature and say what was searched and found
agents_may_not:
  - edit lean/ZetaLean, zeta, ontology, harness or the files of hunt 132
  - call a lemma kernel-checked that carries a sorry or was not compiled
  - word the result as the ten lowest zeros or as a zero count
  - declare novelty
  - promote their own claim
```
