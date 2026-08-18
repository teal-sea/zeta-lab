# Hunt r_8c3b94: pricing Erdős–Kac, the moment method against a Berry–Esseen route

**This is a mapping run, not a proving run.** It buys coordinates. It does not
attempt Erdős–Kac and it must not: starting to prove the theorem is a declared
kill condition, not a stretch goal.

## The question

Runs `43d363c1` (hunt r_0339c1) and the r_233abe follow-up both left
Erdős–Kac as prose: "a real project", "needs either moment control to all
orders or a formalised Berry–Esseen route, each a real project", "out of reach
and should be said so". None of those sentences is a coordinate. A future
proving run funded from them would be funded from a vibe.

So: **what does each of the two standard routes to Erdős–Kac actually cost in
Lean, given exactly what Mathlib carries at this repository's pin and what this
tree already has on `main`?**

Concretely, for each route:

- the obligation list, lemma by lemma;
- which obligations Mathlib already discharges, **named**, with the misses
  named too;
- an estimate in lines of Lean, split into novel mathematics and bookkeeping,
  justified against measured line counts in this tree;
- the single hardest step.

And then the comparison the operator can fund from: which route, at what cost,
with what first obligation, and the conditions under which the answer is "do
not fund this yet".

## Scope

Writes: `hunts/r_8c3b94/` and one case-log entry in `hunts/README.md`
(**Hunt #48**, assigned by the brief; #48 was free when this run took it, the
highest previously used being #45). Reads: anything under `lean/` and
`hunts/`. Touches no existing Lean file, no `zeta/`, no `meta/`, no
`harness/`, no root markdown file. Two other runs are live in
`hunts/frontier_math/`; this run stayed out of both.

`Probe.lean` in this directory is the scratch file the addendum permits: it
`#check`s the declarations the pricing depends on and it is imported by
nothing.

## Standing rules

Nothing here is evidence for or against RH (`docs/08`). The reserved
certification word is not used. Erdős–Kac is a classical theorem of 1940; no
part of this run claims novelty in the mathematics, only in the pricing of its
formalization against this tree.

```huntspec
id: r_8c3b94
question: What does each of the two standard routes to a formal Erdős–Kac cost in Lean, given Mathlib at mathlib4 rev 51e6992e (toolchain v4.33.0-rc2) and this tree's zero-sorry base?
frontier: base on main is the k=2 moment only - hardy_ramanujan (density), hardy_ramanujan_pointwise, Turán variance constant 275, Mertens band 16; Mathlib carries an i.i.d.-only CLT and no Berry-Esseen, no Lindeberg, no method of moments, no Mertens
proposed_attack: enumerate each route's obligations, resolve every Mathlib claim by compiling a #check against the pinned toolchain, and calibrate line-count estimates against measured file sizes in lean/ZetaLean
dead_routes:
  - naive Möbius inclusion-exclusion over y-smooth squarefree divisors for the characteristic function of omega_y - the error term is 2^(pi(y)), which forces y around log N, at which point loglog y is no longer asymptotic to loglog N and the route closes on itself
  - Mathlib's tendstoInDistribution_inv_sqrt_mul_sum_sub applied directly - it requires iIndepFun and IdentDistrib, and the prime indicators satisfy neither
required_oracles:
  - the Lean 4 kernel and elaborator at leanprover/lean4:v4.33.0-rc2, resolving names against mathlib4 rev 51e6992efd06126df61a496bebf8f49482a4e129
  - measured line counts of the existing zero-sorry files in lean/ZetaLean
  - the telemetry record of run 43d363c1 for wall-clock and token cost of a comparable build
kill_conditions:
  - the toolchain will not install or Mathlib will not fetch
  - eighty minutes elapse
  - the run begins proving Erdős–Kac rather than pricing it
  - any cost estimate cannot be tied to a named declaration or a measured line count
agents_may:
  - search Mathlib source at the pinned revision
  - compile a scratch #check file against that pin
  - read every existing Lean file in this tree
  - estimate, compare and recommend
agents_may_not:
  - edit any existing Lean file
  - add a lemma toward Erdős–Kac
  - declare novelty
  - declare theorem status
  - promote their own claim
```

```runmanifest
id: r_8c3b94-2026-08-18-run1
hunt: r_8c3b94
started: 2026-08-18T00:00Z
finished: 2026-08-18T01:05Z
ran:
  - git fetch --depth 1 leanprover-community/mathlib4 51e6992efd06126df61a496bebf8f49482a4e129
  - cd lean && lake exe cache get
  - cd lean && lake env lean ../hunts/r_8c3b94/Probe.lean
  - cd lean && lake build ZetaLean
outcome: both routes priced against 43 verified Mathlib declarations and 14 named misses; the moment route is recommended and the characteristic-function route is blocked on a sieve nobody has formalized
artifacts:
  - hunts/r_8c3b94/RESULTS.md
  - hunts/r_8c3b94/results.json
  - hunts/r_8c3b94/Probe.lean
  - hunts/r_8c3b94/HANDBACK.json
```
