# MISSION: `rh_height_lean`, a kernel-checked RH to finite height for Mathlib's zeta

**Opened 2026-10-21. Hunt #137.** This is the second track of the campaign the owner
directed on 2026-10-21. It is the result that the campaign's compute-leverage and
solid-original strategy lenses both ranked first. Nothing in this directory is a
result until the case log in `hunts/README.md` says how it ended.

Grades used here: *measured*, *hardened* (independent routes agree, or ball enclosures
carry every step), and *kernel-checked* (Lean, zero `sorry`, only `propext`,
`Classical.choice` and `Quot.sound`). The reserved enclosure word belongs to
`zeta/rigor.py` and the Lean arm and appears nowhere in this directory, including in
the names of `rigor.py`'s own routines, which are cited here by role and line number.

## The question

> Can the laboratory kernel-check, for Mathlib's own `riemannZeta`, that every
> nontrivial zero with `0 < Im rho <= T` lies on the critical line and is simple:
> first at T = 50, where there are exactly 10 such zeros, then at T = 100, where
> there are 29?

## Why this is worth a theorem

RH has been verified numerically to height 3.0e12 (Platt and Trudgian, 2021). That
verification, like every earlier one, is a computer calculation in floating-point
or interval arithmetic and is not a formal proof. On 2026-10-21 this campaign ran two
web searches for a kernel-checked finite-height verification in any proof assistant
and found none. It found only formal results on the proportion of zeros on the line,
such as `anthropics/zeta-23-lean`, `lixiang90/RH-Zero-Proportion-Formalization` and
AxiomProver's certificates. That is not a search of the literature, so no novelty is
claimed. A kernel-checked statement at T = 50 is still a theorem about the actual
zeros of zeta. It is finite and says nothing beyond height T, and like every
finite-height verification it cannot tell zeta from the Davenport-Heilbronn function
below that function's first off-line zero, at height 85.699.

## Starting point

- Hunts #132 and #133 kernel-checked at least ten zeros on the line below height 50,
  in two-decimal brackets, from sign changes of Hardy's Z. They prove no upper count,
  so they do not exclude off-line zeros or multiple zeros.
- The vendored `zeta23` package (Anthropic's `zeta-23-lean`, at the lab's pins)
  supplies the folded argument principle `N_eq_halfContour_completedZeta`, the exact
  Gamma-side identity `gamma_side`, `Re zeta(2 + it) > 0` and an explicit vertical
  Stirling bound `digamma_stirling`. The Hardy hunts' route maps never registered
  these.
- `zeta/rigor.py` already runs the Backlund-style contour count with ball arithmetic
  at T = 50 and T = 100, in its zero-count routine (near line 763) and its
  RH-to-height routine (near line 1110), with about 20 contour sub-segments. Its plan
  and margins are the numerical template.
- The campaign's Lean-arm map names four missing Lean pieces: an enclosure of the
  Gamma-side increment (theta(T2) - theta(T1))/pi, boxed control of zeta on the
  horizontal legs, an exact-argument lemma, and a low-height exclusion.

## Scope

- **In scope.** The Lean statement and its proof at the root package's pins (Lean
  v4.35.0-rc2, Mathlib 0653561, vendored `zeta23`); new Lean files under this
  directory, or under `lean/` where the root package needs them; Python only for
  planning and cross-checks.
- **Out of scope.** Any claim beyond height T, any claim about RH itself, and any
  change to `zeta/`.
- **Compute.** The campaign box (32 vCPU, 115 GiB). Under `CLAUDE.md` compute rule 6
  as ruled for that machine, Lean and numerics may run side by side while
  `MemAvailable` stays above 20 GiB. Rule 7 applies: never run Lake in a copied
  `.lake`.

```huntspec
id: rh_height_lean
question: Can the laboratory kernel-check, for Mathlib's riemannZeta, that every nontrivial zero with 0 < Im rho <= T lies on the critical line and is simple, first at T = 50 (exactly 10 zeros) and then at T = 100 (29 zeros)?
frontier: hunts 132 and 133 kernel-checked at least ten zeros on the line below 50 with no upper count; the vendored zeta23 package supplies the folded argument principle, the Gamma-side identity, Re zeta(2+it) > 0 and a Stirling bound; zeta/rigor.py runs the same count with ball arithmetic at T = 50 and 100; no kernel-checked finite-height verification was found by the campaign's two searches on 2026-10-21
proposed_attack: port rigor.py's contour count to Lean at the root package's pins, building the four missing pieces (Gamma-side increment enclosure, horizontal-leg control, exact-argument lemma, low-height exclusion) on the vendored zeta23 argument principle, and close the upper count against hunt 133's located zeros
dead_routes:
  - counting sign changes of Hardy Z alone, which gives a lower bound on zeros on the line and never the count of all zeros in the strip
required_oracles:
  - the Lean kernel, with axioms printed for the final statement
  - a second kernel check (NanoDa or Comparator) where one is available on the box
  - mpmath zetazero and nzeros as an independent numerical cross-check of the count, never as the proof
  - Arb ball enclosures from python-flint for the contour plan and its margins
kill_conditions:
  - a formal finite-height zero count for Mathlib's riemannZeta is found to exist, in which case the hunt is repositioned as a replication
  - any of the four missing pieces is still open after a bounded attempt, recorded with the exact obstruction
  - the final statement does not use Mathlib's own riemannZeta, or needs an axiom beyond the standard three, or contains a sorry
  - the count disagrees with mpmath's nzeros at T = 50 or T = 100
agents_may:
  - read
  - derive
  - code
  - formalize
  - build with lake under that machine's rules
  - attack the construction
agents_may_not:
  - declare novelty
  - declare theorem status for anything not kernel-checked
  - add a sorry or an axiom
  - promote their own claim
  - push, publish or contact outside parties
```
