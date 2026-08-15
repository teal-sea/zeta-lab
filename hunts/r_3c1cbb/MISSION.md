# Hunt R-3C1CBB — Formalize: Mertens's theorems

## The question

Mathlib's wanted-theorems tracking records Mertens's theorems (Wikidata
Q1196729) as wanted and unbuilt. Can any of the three classical Mertens
statements be brought to kernel-checked status in this tree's Lean arm,
within a 90 minute budget, using only the pinned Mathlib
(v4.33.0-rc2) and one new file?

The three statements, in increasing order of difficulty:

1. **First theorem**: sum over primes p <= x of (log p)/p equals
   log x + O(1), with an explicit constant.
2. **Second theorem**: sum over primes p <= x of 1/p equals
   log log x + M + o(1); the in-budget target is the weaker
   log log x + O(1) form with an explicit constant.
3. **Third theorem**: the product over primes p <= x of (1 - 1/p) is
   asymptotic to e^(-gamma)/log x. Out of reach in budget; requires the
   Mertens constant machinery.

The stepping-stone ordering follows the operator addendum: land the first
theorem, then attempt the second by Abel summation.

## Scope

Writes allowed: `lean/ZetaLean/Mertensstheorems.lean`, its import line in
`lean/ZetaLean.lean`, this directory, and the Hunt #30 case-log entry in
`hunts/README.md` (granted explicitly by the brief). Nothing else.

Nothing here is evidence for or against RH (docs/08).

```huntspec
id: r_3c1cbb
question: Can Mertens's first or second theorem be kernel-checked in ZetaLean against pinned Mathlib v4.33.0-rc2 inside a 90 minute budget?
frontier: Mathlib v4.33.0-rc2 carries Chebyshev.theta with theta_le_log4_mul_x and Abel summation; no Mertens statement located in it at hunt open; ZetaLean.ChebyshevBounds already consumes the theta bound
proposed_attack: Legendre-formula route to the first theorem with explicit constants, then Abel summation to the second; report the exact obstruction if either fails to compile
dead_routes:
  - Mathlib.NumberTheory.Chebyshev polynomials namespace, which is about Chebyshev polynomials rather than prime counting
  - the third theorem in budget, which needs the Mertens constant and gamma
required_oracles:
  - the Lean 4 kernel via lake build, exit status plus a zero sorry count
  - grep over the added file for sorry as an independent count
kill_conditions:
  - the toolchain will not install or Mathlib will not fetch
  - the budget is exceeded
  - progress requires editing an existing Lean file other than the ZetaLean.lean import list
agents_may:
  - search the pinned Mathlib source
  - write the one permitted new Lean file and its import line
  - build with lake and read the kernel's answer
  - report an obstruction as the result when the build does not close
agents_may_not:
  - add a sorry and present the file as a result
  - edit existing proofs
  - declare novelty
  - promote their own claim
```
