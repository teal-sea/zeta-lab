# HANDOFF — session records and continuation state

Concise records: what was believed, what invalidated it, what now catches the
problem, what conclusion is currently justified. Decisions live in
`ROADMAP.md`; this file is the between-session state. Last snapshot:
2026-08-10.

---

## Record: rung 3 — the steeper tail exponents are kernel-checked (2026-08-10)

- **Built, zero sorrys (`DHTailBound2.lean` completed, `DHAssembly.lean`
  extended):** the project scoped in the previous record, delivered whole.
  Domain-independent half: `norm_trapezoid_sub_integral_le` (trapezoid rule
  with remainder `((b−a)²/8)·∫‖g''‖`, by integrating the weight `(t−a)(b−t)`
  by parts twice — the first Euler–Maclaurin correction with no Bernoulli
  machinery) and the two summed half-line comparisons
  `norm_tsum_sub_integral_le` / `norm_tsum_sub_integral_trapezoid_le` for any
  Banach-valued `C¹`/`C²` function. DH half: the block at a *generic
  exponent*, `dhPair w x = (5x+1)^w − (5x+4)^w + κ((5x+2)^w − (5x+3)^w)`, so
  that one derivative lemma (`d/dx dhPair w = 5w·dhPair (w−1)`) and one
  mean-value bound (`norm_dhPair_le`, exponents `Re w ≤ 1`) serve the block,
  both its derivatives, and the antiderivative
  `dhAnti = dhPair (1−s)/(5(1−s))` — closed-form precisely because the
  coefficients sum to zero, `∫_K^∞ B = −dhAnti K` by FTC-on-`Ioi` plus the
  vanishing limit. Payoff theorems: `DH_tail_bound_order1` (radius
  `(3+κ)‖s‖‖s+1‖(5K+1)^{-σ-1}/(σ+1)`) and `DH_tail_bound_order2` (radius
  `(5/8)(3+κ)‖s‖‖s+1‖‖s+2‖(5K+1)^{-σ-2}/(σ+2)`, requiring the corrections
  `+ dhBlock K/2 − dhAnti K` on the partial sum), both for `Re s > 0`,
  `s ≠ 1`, `K ≥ 1`; assembly variants `DH_mem_of_partial_enclosure_order1/2`
  take a box around the corrected sum and a rational dominating the radius.
- **Validated before formalizing, pinned after.** The exact statements
  (signs, constants, exponents) were checked with mpmath at five points
  (oracle zero, DHDemo point, `0.05+20i`, `0.95+200i`, `0.99+10i`) over
  `K ≤ 4096` before any Lean was written; the measured order-2 error decay
  matches `σ+2` to three digits. Now standing tests
  (`tests/test_epstein.py::test_dh_tail_bounds_hold_at_all_three_orders`,
  `…_order2_decay_exponent_is_sigma_plus_2`,
  `…_required_K_pins_the_cost_model`) pin the formulas against `dh_f` — the
  Hurwitz route, which never touches the Dirichlet series.
- **Re-priced (model plus fresh measurements, not yet a run):** minimal `K`
  for a 1e-3 tail at the oracle zero: 195,301 blocks (order 0) → 1,741
  (order 1) → **243** (order 2), an 804× reduction. Full-square model with
  `|DH'(ρ)| ≈ 1.256` (measured), boundary box size
  `δ ≈ 1/(4‖s‖) ≈ 0.0029`, per-box budget `|DH'|·w/2`: optimum moves to
  `w ≈ 0.003` with ~9 boundary boxes, total ≈ 9,550 certified terms
  (order 1: 60k terms; order 0: 1.6M). Per-term cost **re-measured here at
  oracle parameters** (Taylor-20, `p = 64`, `kE = 10`, `kL = 9`, ten-term
  differential under `lake env lean`): **≈ 0.84 s/term**, so the whole
  order-2 run is ≈ 2.2 h of single-core elaboration — the earlier 5 s/term
  figure appears to be slower hardware or CPU contention (a first
  measurement here under a running pytest read 17 s/term; measure idle).
  Headline stays a conservative *half a day single-core*. The corrections
  cost the run nine extra certified cpow values (`(5K+j)^{1−s} =
  (5K+j)·(5K+j)^{−s}` reuses `dirichletTermBox`; `1/(5(1−s))` is an exact
  Gaussian rational at a rational `s`).
- **Proof-engineering notes, so the next Lean session starts warm:** (1)
  `HasDerivAt.smul` orders the derivative `c x • f' + c' • f x` — state the
  IBP integrands in that order or fight the unifier. (2)
  `integral_eq_sub_of_hasDerivAt` needs `(f := …)` explicitly when the RHS
  is not literally `f b − f a` (higher-order unification will not read it
  off). (3) `simp [Function.comp]` no longer unfolds compositions — use
  `Function.comp_def`. (4) `HasDerivAt.scomp` wants the point as its first
  explicit argument and `(𝕜 := ℝ)` helps it find the tower. (5) `ring`
  cannot factor `5` out of `(10 + 5σ)⁻¹` — carry denominators in factored
  shape or `field_simp` with an explicit `≠ 0`. (6) The `module` tactic
  closes every smul-linear telescope here (the trapezoid endpoint sums)
  where `abel` cannot.
- **Pipeline proved out end to end (`DH_demo2_enclosure`, zero sorrys):**
  `DH_mem_of_partial_enclosure_order2` instantiated at the DHDemo point
  with the same `K = 2`: certified radius `1/10` versus order-0's `2/5`
  (the true order-2 radius there is ≈ 0.008; the slack is deliberately
  crude norm bounds, not the theorem). The two genuinely new mechanical
  steps of the offline run are both exercised: `(5K+j)^{1−s}` boxes by
  `cpow_add`-splitting into `(5K+j)·(5K+j)^{−s}` (reusing
  `dirichletTermBox`), and the exact Gaussian rational
  `(5(1−s₀))⁻¹ = −2/185 + (12/185)i` certified by
  `inv_eq_of_mul_eq_one_right` plus `Complex.ext`. Correction cost measured:
  five extra term boxes, negligible against the 5K-term sum.
- **Next stone (nothing left but scale):** the oracle-point offline run per
  the runbook in the next record — `DH_demo2_enclosure` is its exact
  template, and the new pricing shrinks it to about half a day single-core.

## Record: rung 3 — the target is forced, and the cost model corrected (2026-08-10)

- **Negative result, now a standing test.** The pinned zero at
  `t ≈ 85.699` is the **lowest** off-line zero: a box with
  `Re ∈ [0.55, 2]` contains only off-line zeros by construction, and
  scanning `0 < t < 80` in ten-wide windows finds none, while the window
  holding the pinned zero finds one (`test_no_offline_zero_below_the_pinned_one`,
  slow tier, 47 s). This matters because the Lean certification cost scales
  like `‖s‖^2.2`, so a lower-height zero would have been worth orders of
  magnitude. There is none. The avenue is closed, permanently.
- **The previous record's compute estimate was too optimistic; corrected
  here.** It said "weeks single-core" and "~tens of boxes". Both were
  wrong: the boundary box count is set by `δ ≈ 1/(4‖s‖) ≈ 0.0029`
  (DH oscillates at scale `1/‖s‖`), and the error budget must be split
  between enclosure width and in-box variation. Redone properly, the
  direct route costs **~230 days** single-core at the measured ~5 s per
  certified term — minimized near `w = 0.1`, and *worse* for smaller
  squares, because a smaller square needs proportionally finer accuracy
  and the current tail bound only decays like `K^{-σ}` with `σ ≈ 0.81`.
- **What changes the picture: a steeper tail exponent, which makes small
  squares cheap.** Comparing the block sum to its integral turns
  `K^{-σ}` into `K^{-(σ+1)}` (remainder `∫|B'|`), and the trapezoid
  refinement into `K^{-(σ+2)}` (remainder `(1/12)∫|B''|`). Modelled cost:
  ~5 days at order 0, **~1 day at order 1**, with the optimum shifting to
  `w ≈ 0.002` (6–8 boundary boxes instead of 275). Crucially **no
  Bernoulli numbers and no general Euler–Maclaurin are needed** — Mathlib
  has neither, and the trapezoid error bound is elementary. The block
  antiderivative is available in closed form precisely because the
  coefficients sum to zero: `F(x) = Σ_j c_j (5x+j)^{1-s} / (5(1-s))`
  converges to 0 at ∞ even though each summand diverges, so
  `∫_K^∞ B = -F(K)` is computable by the machinery already built.
- **Next project, scoped:** `DHTailBound2.lean` — (1) the per-step bound
  `‖g(k) − ∫_k^{k+1} g‖ ≤ ∫_k^{k+1} ‖g'‖` and its trapezoid refinement,
  (2) `∫_K^∞ B = -F(K)` by FTC plus the vanishing limit, (3) a
  third-difference bound on `∫_K^∞ ‖B''‖`. Several hundred lines,
  structurally identical to the estimates already proved in
  `DHTailBound.lean`. That plus a ~1-day offline kernel run finishes
  rung 3; nothing else is missing.

## Record: rung 3 — the pipeline demonstrated end to end (2026-08-10)

- **Built, zero sorrys (`DHDemo.lean`):** `DH_demo_enclosure` — a computed
  rational rectangle, inflated by the certified tail radius `2/5`,
  kernel-checked to contain `DH(3/2 + 3i)` — and `DH_demo_ne_zero`: the
  box excludes the origin, so `DH(3/2 + 3i) ≠ 0`. The first
  kernel-certified facts about a *value* of the Davenport–Heilbronn
  function, with no oracle input anywhere: κ coefficient boxes from
  `kappaI`, term boxes from `dirichletTermBox`, ten containment steps,
  `DH_mem_of_partial_enclosure`, `normLower_le_norm`.
- **Rung 3's honest state:** the mathematics is complete and the
  instantiation template is proven. What separates this from
  `davenport_heilbronn_statement` is scale alone: the same pipeline at the
  oracle point `0.808517 + 85.699348i` (via
  `davenport_heilbronn_of_certified_square`, centre plus four boundary
  segments subdivided) needs the offline kernel compute priced in the
  previous record — weeks single-core at measured `norm_num` rates — or a
  faster certified evaluation (Euler–Maclaurin with explicit remainder for
  `(x+a)^{-s}`, a formalization project of its own) to cut `K` from ~10⁴·5
  to ~10². Neither fits a session; both are now *engineering*, with every
  theorem they need already kernel-checked. The runbook: pick `w = 1/10`
  square, `ε' = 1/100`; centre via `DH_mem_of_partial_enclosure` with
  `K ≈ 11300`; each boundary segment split until per-box
  `normLower` clears `ε'` (oracle cross-check says min `‖DH‖ ≈ 0.121`, so
  ~tens of boxes suffice if the enclosure width stays ≪ 0.1, which needs
  the higher log Taylor order noted in the scale record).

## Record: rung 3 assembly — machinery built, scale measured (2026-08-10)

- **Built, zero sorrys:** `DHAssembly.lean` (`DH_mem_of_partial_enclosure` —
  the K-generic partial-box-plus-tail-radius enclosure theorem; `Interval.inv'`;
  `contains_sqrt_of_sq`; `kappaI`: κ ∈ [0.2840788, 0.2840794] kernel-checked);
  the square-contour criterion (`davenport_heilbronn_of_certified_square`,
  `frontier_dhSquare` — four segments, coverable by boxes, replacing the
  sphere); boxed-`s` term enclosures (`dirichletTermBox`); norm lower bounds
  read off boxes (`normLower_le_norm`); and `Interval.coarsen` — outward
  dyadic rounding, the primitive Arb has and the exact layer lacked.
- **Measured, so nobody re-learns it:** (1) without `coarsen`, one term at
  the oracle point has 562,971-bit endpoints (squaring doubles digits;
  eight squarings); with `p = 64` coarsening, 61 bits and instant. (2)
  `decide` cannot evaluate ℚ arithmetic under Mathlib **at all** — even
  `1/3 * (1/7) ≤ 1` sticks in the instance chain; the evaluation route for
  instantiations is simp-unfold + `norm_num`, which the smoke tests already
  prove out. (3) `norm_num` costs ~5 s per tame term, so the oracle-point
  center inequality (~56k terms at Taylor-20/kE-10) is roughly two weeks of
  single-core kernel compute, the boundary several times that: an offline
  compute project, not a session task. Parameter discipline for that run:
  `kL = ⌊log2 m⌋ + 1` per term (a fixed `kL` sends small-`m` log series
  far from convergence), `kE = 10` covers all `m ≤ 10^5`
  (`kE = 8` silently overflows at `m ≥ 20` — the definition computes
  garbage exactly where the theorem's hypothesis refuses to apply, which
  is the interval discipline working).
- **Next stone:** an end-to-end tame-point demo — kernel-certify
  `DH(3/2 + 3i) ∈ box` through the whole pipeline (coefficient boxes from
  `kappaI`, term boxes, `sumList`, tail radius, assembly theorem): the
  first certified enclosure of a Davenport–Heilbronn value, and the
  template the offline run scales up.

## Record: rung 3 Phase B — the tail bound is kernel-checked (2026-08-10)

- **Built, zero sorrys (`DHTailBound.lean`):** the analytic continuation of
  the DH series, as computation. The route deliberately avoids
  measure-theoretic integrals in the estimates: (1) a two-point bound
  `‖b^{-s} − a^{-s}‖ ≤ ‖s‖·a^{-σ-1}·(b−a)` from Mathlib's convex mean value
  inequality on `t ↦ (t:ℂ)^{-s}`; (2) the series regrouped into five-term
  blocks whose coefficients `(0, 1, κ, −κ, −1)` pair into two differences,
  so each block obeys a `(3+κ)`-constant bound and the block series
  converges *absolutely* on `Re s > 0`; (3) blocks sum to `DH` for
  `Re s > 1` by `Nat.divModEquiv`-regrouping, and on all of `Re s > 0` by
  Weierstrass (`differentiableOn_tsum_of_summable_norm`, localized to
  balls) plus the identity theorem; (4) `DH_tail_bound`: the explicit
  error `(3+κ)·‖s‖·5^{-σ-1}·(K−1)^{-σ}/σ` for the `5K`-term partial sum,
  tail summed by the integral test. With `contains_dirichletTerm` this
  makes `DH` at any strip point a finite computation plus an explicit
  error — the mathematics gap of Phase B is closed; only assembly remains.
- **Honest scale note, recorded so nobody wastes a session:** at the oracle
  point (`σ ≈ 0.808`, `‖s‖ ≈ 85.7`) the bound needs `K ~ 5·10⁵` blocks for
  1e-3 accuracy. Direct kernel summation at that scale is not realistic;
  the assembly step should either formalize a faster certified evaluation
  (Euler–Maclaurin remainder, or the smoothed series) or budget a very
  long offline kernel run. The tail bound itself is scale-independent.
- **Proof-engineering notes:** Mathlib's `Nat.mul_add_mod` wants `m*x+y`,
  not `x*m+y` — commute first. `tsum_le_tsum` is now protected
  (`Summable.tsum_le_tsum`), and the range-split lemma is the primed
  `Summable.sum_add_tsum_nat_add'` with *shifted* summability. An
  off-by-one in a shift constant (`k+1+(K−2) ≠ k+K`) was caught by omega
  refusing the goal — when omega balks at "obvious" index arithmetic,
  recheck the arithmetic before blaming omega.

## Record: rung 3 Phase B — the term enclosure is kernel-checked (2026-08-10)

- **Built, zero sorrys:** `Interval.logQ` (log of any positive rational by
  the binary reduction `IntervalExp.lean` had promised; kernel-checked
  digits of `log 10`), then `IntervalCExp.lean`: `ComplexInterval` Taylor
  sums, remainder inflation from Mathlib's `Complex.exp_bound`, `expC` by
  halving-and-squaring, and `contains_dirichletTerm` — a computed rational
  box provably containing `(m : ℂ)^(-s)` with **no oracle input**. Smoke
  tests kernel-check digits of `cos 1`, `sin 1`, `cos 2` through the complex
  pipeline (`exp(it)` gives sin/cos free; no trigonometric development was
  needed, and none should be added).
- **Design notes worth keeping:** simp rewrites `((Real.log m : ℝ) : ℂ)`
  to `Complex.log m` behind you (`ofReal_log` is simp with a positivity
  side-goal) — use explicit `rw` when the `ofReal` form matters. And state
  inflation bounds with `|(r : ℝ)|`, not `((|r| : ℚ) : ℝ)`, or `push_cast`
  normalizes the goal away from the hypotheses.
- **Still open (the honest remainder of Phase B):** the certified tail
  bound for the analytic continuation past `Re s ≈ 0.808`, and assembling
  `davenport_heilbronn_of_certified_disk`'s two inequalities from term
  enclosures. `OracleDH.lean`'s per-term bounds are now redundant in
  principle; they stay until the assembly replaces them.

## Record: full-repo audit on a fresh clone (2026-08-10)

- **Setup verified end to end:** venv from `requirements.txt`,
  `rigor.BACKEND == python-flint` with both backends present (so the
  two-backend cross-check genuinely ran), full suite executed, and the Lean
  arm kernel-checked from nothing (elan + Mathlib cache + `lake build`,
  8709 jobs, zero `sorry`s in the build log).
- **One real failure found and fixed:**
  `test_explicit.py::test_mobius_inversion_of_J_is_exact` failed
  deterministically on glibc at x = 64 — `64**(1/3)` rounds to
  `3.9999999999999996`, `J_exact` drops its `π(√4)/2` term, and the Möbius
  sum comes back `π(64) + 1/6`. Fixed by snapping perfect-power roots to
  the integer in the test helpers; the identity is now tested at the
  mathematical J instead of at whichever side of the boundary the
  platform's `pow` lands on. The failure was invisible on the author's
  libm — a platform-fragility class worth remembering for any future test
  that composes exact π with float roots at exact powers.
- **Hygiene restored:** the tracked `.wav` (against the tree's own
  `*.wav` rule) and `zeta_lab.egg-info/` untracked; `scratch/` folded into
  `scripts/20_music_of_the_primes.py`; `interactive_lab/` documented with
  its contract; the duplicate doc number resolved
  (`08-detector-strength-findings.md` → `22-…`, so a bare `docs/08` is
  unambiguous again); AGENTS.md layout now names `compiler/`,
  `interactive_lab/` and the ontology rogue-lab scripts; the learn/refute
  door commands got the pinning test the doors policy promises
  (`tests/test_doors.py`); `CONTEXT.md` regenerated.
- **Lean arm state (supersedes the earlier "trust the commits" note):**
  rungs through `DHZeroCriterion` build clean. The two files missing
  copyright headers have truthful MIT ones; the Mathlib header linter is
  disabled in `lakefile.toml` because it hard-requires Apache-2.0 wording
  this MIT project cannot honestly write. ~24 pre-existing longLine/style
  warnings remain in `HardyZ`/`Epstein`/`OracleDH`; cosmetic, untouched —
  wrapping lines inside kernel-checked proofs was judged not worth the
  churn.

## Record: Hunt #2 (factorization-position rigidity) — claim withdrawn

- **Believed:** a "verified" correlation between factorization defect D(F)
  and a Weil position residue R_F(c) on principal forms of imaginary
  quadratic fields (`hunts/factorization_vs_position/experiment2.py`).
- **Invalidated by:** (1) the completeness gate was never called —
  `online_list_is_complete` appears nowhere in `hunts/`, and the zero list
  came from a `step=0.05` sign-change scan that skips close pairs, so a
  missing on-line zero is indistinguishable from an off-line one;
  (2) the planted-fault control reproduces the signal at zero defect (ζ with
  one on-line zero removed: residue 0.0038 → 1.99; the recorded Epstein
  residues 4.07–4.33 are about twice that); (3) the test set is the negative
  control set — the −23 principal form `(1,1,6)` is registered in
  `zeta.epstein.battery` *because* it lacks a scalar Euler product, so
  finding that it lacks one distinguishes nothing; (4) the recorded data
  does not show the claimed relationship (`results2.json`: defect varies
  2.7×, residue moves 6%; `results.json`: `argmax_c` pinned at 86.0 for all
  nine rows — the scan-window signature `docs/17` §2 says to distrust).
- **Now caught by:** `tests/test_hunt_probe_discipline.py`.
- **Justified conclusion:** no relationship demonstrated. The reusable part
  (a generalized residue detector) is retained.

## Record: scope wording (`4c7e480`, then `f47a490`)

- A commit had changed the scope rule to claim the repo "is a proof by
  construction via the spectral operator", contradicting the rule itself.
  Reverted; then the replacement hedge-heavy wording was itself replaced at
  the owner's direction with the current plain form: *Zeta Lab is a
  computational and formal workbench that reconstructs, tests, connects, and
  falsifies ideas around RH, without claiming to advance RH.* All statements
  of scope (CLAUDE.md, README, ROADMAP, docs/00) agree. Substance unchanged.

## Record: strengthened gates (docs/09 §5.1, `c0fa48d`)

Weil positivity over the full admissible class is *equivalent* to RH, so
"prove the form is positive" is RH restated, not a strategy. The positive
target is factorization: −W(f ∗ f̃) = ‖Φ(f)‖² inside a genuinely positive
structure. Requirements A (arithmetic provenance, mechanically checkable),
B (exact trace realization — where the analytic difficulty relocates),
C (structural positivity; naturality is where the lab's writ ends). §5.1
also records the five-entry pseudo-solution taxonomy and the
linear-combination sharpening of gates 3/4 (the gate is eliminative, never
probative). Battery default rivals extended to Davenport–Heilbronn plus both
discriminant −23 forms; pinned by `tests/test_epstein.py`.

## Record: the Lean arm

- `lean/`: Lean 4 + Mathlib package `ZetaLean`, elan toolchain, binary
  cache. Rule: kernel plays the role of `rigor.py`; nothing counts with a
  `sorry`.
- **Zero-sorry repair (2026-08-07):** tree `2640f0a` carried six `sorry`s
  and `ZetaLean.lean` imported only three of eight modules, so `lake build`
  never compiled the files carrying them — "build green" was not evidence
  about most of the package. Fixed: root imports all modules; interval layer
  proved (`Rigor.lean`, `DirichletEval.lean`); the stage-3 statement is a
  named `Prop` (`davenport_heilbronn_statement`), deliberately a `def`, not
  a sorried theorem.
- **Status by stage:** 1 (ground truth) done; 2 (κ derivation) finite
  algebra kernel-checked in `Epstein.lean` incl. root-number reduction —
  open: the analytic inputs (functional equation of L(s, χ mod 5), Gauss-sum
  value of w); 3 (Davenport–Heilbronn theorem) statement done, interval
  layer done, analytic half landed (`eb6997f`, `8967d9a`), certified
  exp/log in progress (`da79291`) — open: tying `n^{-s}` to its enclosure
  and the tail bound for the continuation. `lean/oracle_dh.py` emits
  exact-rational enclosures and states its own provenance (oracle claim, not
  a certificate).

## Record: the upstream (Mathlib) track (2026-08-06, `f5a1cbd`)

`scripts/mathlib_gaps.py` → `references/mathlib-open-targets.md`: 970 of
1179 famous theorems in Mathlib's `1000.yaml` carry no `decl:`. Verified by
code and open-PR search: Hardy Z / RS-ϑ / Sturm / critical-line theorem are
unclaimed; N(T) is owned by PrimeNumberTheoremAnd — do not duplicate. Two
decisions worth not re-deriving:

1. Build Hardy Z from `completedRiemannZeta`, not e^{iϑ}ζ — the textbook
   route needs a continuous log Γ branch Mathlib lacks; the Λ route gets
   realness from `riemannZeta_conj` + `completedRiemannZeta_one_sub`.
2. Hardy Z precedes Sturm: a multi-thousand-line first PR from a contributor
   with no merged history does not get reviewed. Impact alone argues the
   opposite order; that is the trap.

Porting work lives in `../contrib-lab` (separate repo; nothing here depends
on it). Not done: Lean scoping of either target; Zulip not checked for
unannounced claims.

## Record: department architecture (2026-08-06, `0bb04c3`..`499d632`)

`harness/` landed; rationale in `ROADMAP.md`, how-to in `harness/README.md`.
Repairs found on the way: `make_context.py` pointed at the dead `discovery/`
directory (that CONTEXT.md section had been silently empty; stale name was
live in five other files); `-n auto` hung twice in teardown after all tests
passed — `-n 4` completes cleanly, and `-p no:xdist` does not work because
`-n auto` is already in `addopts`. Open: three `zeta/` instruments not wired
into the battery (`spectral_gate` ablations, `detectors`' Li/Weil planted
faults, `quasicrystal`); `factorization_defect` cannot referee Epstein
(2,1,3) (a₁ = 0; recorded in `docs/doors/zeta.md`, pinned by
`tests/test_harness_zeta_department.py`). Merged branches `five-longshots`
and `worktree-factorization-gate` still exist locally; the
`factorization-gate` worktree is on disk and locked.

## Record: croniter department + resumption benchmark (2026-08-09)

- **Croniter admitted** — first subject born outside this repo; vendored,
  byte-pinned fixtures; five calibration mutants as exact source patches;
  distinguishing reference claim is agreement with a calendar-arithmetic
  oracle that never calls the subject. `harness/protocol.py` untouched,
  pinned lexically by the department test. Caution: the magnitude
  measurement initially hung on the exact backward-jumping fault it was
  measuring; bounded now, pinned by
  `test_the_reemission_lesion_is_measured_boundedly`.
- **Dossier admission stays closed** — docs/19 §6's bar (typed beats flat
  notes on a scoreable resumption task) was not met: typed ≈ prose, lesions
  partly at ceiling. Surviving measurement: agents caught recorded
  contradictions nearly everywhere and reliably missed hollow verification.
  "Did not demonstrate," not "disproved."
- **Not to be inferred:** departments authored under one orchestrating
  process say nothing about outside adoption (open: someone not this process
  builds a valid department from the docs alone). Nothing here bears on RH.

---

## Continuation checklist

1. `git pull`; confirm fast tier green
   (`.venv/bin/python -m pytest -q -m "not slow"`).
2. `cd lean && PATH="$HOME/.elan/bin:$PATH" lake build` — zero `sorry`s
   before adding theorems.
3. Lean stage-3 open items above are the active front.
4. Regenerate `CONTEXT.md` after any public API/doc/script change.
5. Adding a department: battery first, list it in
   `harness/departments/__init__.py`, then
   `.venv/bin/python -m pytest -q -o addopts='' tests/test_department_conformance.py`.
   The audit is parametrized over that listing.
