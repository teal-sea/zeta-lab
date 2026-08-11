# HANDOFF — session records and continuation state

Concise records: what was believed, what invalidated it, what now catches the
problem, what conclusion is currently justified. Decisions live in
`ROADMAP.md`; this file is the between-session state. Last snapshot:
2026-08-10.

---

## Record: the director run — six defects, and rung 3's recorded cause was
## wrong (2026-08-11)

Full record in `docs/25-the-director-run.md`; ledgers in `hunts/director_run/`.
The two things a next session must not re-derive:

**1. `zeta/rigor.py` could return a wrong proof, and the two-backend
cross-check could not see it.** `_exact` parsed unrecognised numeric types from
their printed decimal, so `proven_sign(np.float32(21.02203941345215))` returned
`-1` where the true `Z` is `+2.56e-7`, on **both** backends — the fault is
upstream of the split. Fixed and pinned. Standing consequence: a cross-check
bounds only what is actually duplicated, and `_exact`, the contour policy, the
grid policy and the final `S(T)`/`N(T)` interval summation are shared.

**2. The record immediately below is corrected in two places.** Its
"the per-term floor is set by nExp, at ~7e-7" is **not reproduced**: the box
width is bit-identical across `nExp ∈ {16,20,24,28}` and across `p`, and the
floor is the width of the κ enclosure (`kappaI`, 6e-7, in `DHAssembly.lean`),
confirmed analytically. And its "the centre needs the exp order raised — that
trade is the one genuinely unresolved thing in rung 3" is **false**: the centre
could not have passed at any parameters, because `normBound(B.inflate r)` is
`max|re| + max|im| + 2r` while the plan budgeted `r` once, and
`2·r_c = 7.47e-4 > ε′ = 5e-4`. `K = 444` (+415 terms) gives margin 1.164.

A third defect the previous session never reached: the boxed-`s` width constant
is `ρ_W ≈ 5.9` measured against the plan's 2.6, **all 11 sampled big boxes fail**,
and `ρ_W` is invariant under every parameter — it is the rectangle
representation of a rotating complex value under repeated squaring. The next
move is therefore a choice, and it is the run's one genuine question for the
operator: re-plan at the measured constants (~130k terms against 79.5k, same
literal sizes, margins ≥1.1), or first replace the rectangle enclosure of
`m^{-s}` with a polar or mean-value one, which is worth ~2× on the entire
certificate and is mathematics rather than parameters. Measure `ρ_W` on the
low-σ left edge before either: it is the one number the cost estimate leans on
that has not been sampled where it matters.

**Also:** the Lean arm rebuilds from a cold machine (elan + Mathlib installed
from nothing, 8715 jobs, zero `sorry`s), and the flagship `W(h) ≈ 8.86e-18`
enclosure was reproduced to 43 digits by a blind replicator that was forbidden
the package and given only the mathematical statement.

**One caveat above is retired by work that landed in parallel.** This record's
rung-3 measurements carried the caveat that *the mirror's bit-exactness is
itself an assumption*, spot-checked here only two ways (it reproduces the
previous session's published digits, and an independent re-derivation of the
tail radius from the Lean lemma's hypotheses matches the stored `r_c`).
`tests/test_rung3_mirror.py`, merged from `main` at 01f40c6, now pins mirror
soundness against an mpmath oracle at dps 40 on a completely different route —
which is a stronger check than either of mine and was authored without
knowledge of them. The feasibility numbers in `docs/25` §4.3 rest on a mirror
that a third party has since tested. Its second pinned fact, that boxed-`s`
evaluation can never certify a *lower* bound, is the same negative result the
re-plan already routes around.

---

## Record: rung 3 — plan v2 is infeasible as generated, and the cause is one
## constant (2026-08-10, fourth session of the day)

> **Corrected 2026-08-11 (see the record above and `docs/25` §4.3): the two
> conclusions this record draws about *cause* — the nExp floor and the centre's
> Taylor-order trade — are both wrong. Its measurements reproduce exactly; its
> diagnosis does not.**

**The blocker was never the evaluation engine.** Running the *unmodified*
generator on a grid site asserts before emitting a line:

```
AssertionError: g_bottom_00: normLower 0.017520903235754424 < beta 0.052147503410769
```

That is the mirror's exact box evaluation refusing the site, which is the
safety net the previous record claimed for it, firing. **11 of 11 sampled grid
sites fail their own β**, by factors of 2× to 43×. The big boxes and the centre
pass (the smallest big box gives normBound 2.374 against M = 2.5499). So the
grid — the whole small-frontier half of the certificate — could not have been
certified at plan v2's emitted parameters no matter how fast the engine got.

**Cause, isolated by measurement.** The box width is not coarsening, not
squaring, and not the exp remainder. It is `Interval.logQ`'s Taylor truncation
at `TAYLOR_N = 20`. At the worst sampled site (`g_left_18`, K = 113):

| quantity | at n=20 | at n=28 | at n=32 |
|---|---|---|---|
| width of `logQ` (m=4) | 7.6e-6 | 3.0e-8 | 1.9e-9 |
| width of the term box | 3.0e-3 | — | 7.3e-7 |
| 505 terms contribute | 1.52 | — | 3.7e-4 |

against a β of ~0.05. Raising `kE` or the coarsening precision does **nothing**:
at `kE = 14`, `kE = 18` or `p = 128` the term width is still 3.0e-3. Only the
log order moves it.

**The fix, and its measured threshold.** On `g_left_18` (β = 0.0382898):

| config | normLower | verdict |
|---|---|---|
| n = 20, tower (as shipped) | 0.000889 | FAIL, 43× short |
| n = 28, tower | 0.0383896 | OK, margin ×1.00 |
| n = 32, tower | 0.0385272 | OK, margin ×1.01 |
| n = 32, composite chain | 0.0385252 | OK, margin ×1.01 |
| n = 40, composite chain | 0.0385363 | OK, margin ×1.01 |

Two things to read off it. The margin **saturates at ×1.01**, so past n ≈ 28 the
residual gap is the inflation radius (r = 0.0134 against β = 0.0383) and the
geometry, not the series — there is nothing further to buy by raising the order,
and β was planned with ~1% headroom. And the **composite chain matches the tower
to four significant figures** (0.0385252 vs 0.0385272) while running 3.4× faster
in the mirror (96 s vs 329 s), so chains cost no usable width. n = 28 is the
threshold and is too thin to ship; **n = 32** is the choice.

**The two orders must be split, and that is now in the build.** `TAYLOR_N` was
one constant feeding both series, and they want opposite things: the log sets
the width, the exp sets the literal size (`expSmall` forms `powI x i` up to
`i = n`, which is where the multi-thousand-bit rationals of the previous
record's negative result #2 come from). Measured: the log's own endpoints go
from 91 to 158 bits between order 20 and 32 — negligible. So
`dirichletTermBox2 nLog nExp p kL kE m S` and `contains_dirichletTermBox2` are
kernel-checked in `IntervalCExp.lean`, with `dirichletTermBox2_self` proving by
`rfl` that the old definition is the diagonal `nLog = nExp` case. Target
configuration: **nLog = 32, nExp = 20, p = 64, kE = 10, composite chains.**

**Not done.** `scripts/60_rung3_generate.py` still emits one tower per m at the
single order 20. It needs: the split orders, per-`m` `pw_` boxes with primes on
towers and composites on `contains_cpow_mul_coarsen`, and `term_{sid}` as a
match over those. Then regenerate and compile. The mirror already has
`dirichletTermBox2`, `cpowBox`, `cpow_plan` and `term_chain` for exactly that
shape, so the generator change is codegen, not mathematics.

**And the constant is not sufficient — measured.** A sweep at the target
configuration (nLog = 32, nExp = 20, p = 64, kE = 10, composite chains) got
through 60 of the 215 sites before being stopped. Of 59 grid sites:

| | value |
|---|---|
| fail | **30 of 59 (51%)** |
| margin range | 0.9931 … 1.0065 |
| median margin | 0.9991 |
| worst failure | ×0.9931 (0.7% short) |
| best pass | ×1.0065 (0.65% over) |
| within ±2% of the line | **59 of 59 (100%)** |

So the grid is not *wrong*, it is sitting exactly **on** the line: β was drawn at
the achievable bound, the total spread is 1.3%, and which side of it a site lands
on is effectively a coin flip. A uniform ~1–2% improvement in box width — or ~1%
of slack in β — turns all 30 failures into passes. That is a headroom bug, not a
geometry bug.

**The centre is a different and real problem: FAIL at ×0.6321**, normBound
7.9e-4 against an ε of 5e-4, 37% short. Its budget explains why: the plan gives
it `r_c = 3.736e-4` out of 5e-4, leaving 1.26e-4 for the box itself, and the box
uses 4.2e-4. Raising nLog does not reach it, because with nLog high the per-term
floor is set by **nExp**, at ~7e-7, and the centre sums 1805 terms. So the centre
needs the exp order raised too — which is the order that inflates the literals
and revives negative result #2. That trade is the one genuinely unresolved thing
in rung 3.

**What this means for the next session.** The remaining work is a **re-plan**,
not codegen: pick nExp and `r` (equivalently K) with real headroom instead of
0.3%, re-derive β and ε, and only then regenerate. `ROADMAP.md`'s
"Open: scale alone … nothing else is missing" is corrected in the same commit —
it was written before the mirror could price a site exactly, and it is false.

**Caveats.** 60 of 215 sites, one machine, and the grid numbers are the 59
evaluated of 104. The centre was evaluated once. Big boxes were not reached in
this sweep, though a separate spot check had the smallest one passing
(normBound 2.374, later 2.4076 on chains, against M = 2.5499 — also thin).

## Record: rung 3 — the composite-chain step is kernel-checked, and its cost
## is measured (2026-08-10, third session of the day)

The previous record named composite-chain term evaluation as "next session's
first move". The lemma it rests on is now in the build, and the reason to
believe the route is now a measurement rather than an estimate.

- **Built, zero sorrys (`DHCertSupport.lean`):** `contains_cpow_mul` and
  `contains_cpow_mul_coarsen`. `cpow` of a natural is multiplicative
  (Mathlib's `Complex.natCast_mul_natCast_cpow`, no side conditions), so a
  composite `m = a·b` needs no `expCr` tower of its own — it is one
  `ComplexInterval.mul` of the two boxes already computed for its factors,
  optionally rounded outward. Towers are then needed only for the primes below
  `5K`, i.e. ~`π(5K)` of them instead of ~`5K`.
- **The cost, measured.** Four generated-shaped obligations on realistic
  64-bit-coarsened literals — one two-factor product; a four-factor chain
  uncoarsened; the same chain coarsened after each product; and reading
  `normLower` off a product — cost **4.48 s user against a 2.47 s
  import-only baseline, so ~0.5 s per obligation**. Compare negative result
  #2 in the previous record: one `dirichletTermBox` literal equality took
  ~8 min and still exceeded simp's step limit. The composite step is roughly
  three orders of magnitude cheaper than the tower it replaces, and it
  discharges rather than failing.
- **Coarsening between factors is load-bearing, not cosmetic.** Measured by
  `#eval`: one `ComplexInterval.mul` takes endpoints from denominator `2^64`
  to `2^127`, so an uncoarsened four-factor chain reaches ~508-bit rationals
  and keeps doubling. `coarsen p` after each product holds the width flat and
  reduces cleanly under `norm_num` — the `Int.ceil` in `Interval.coarsen` is
  handled by the numeric extension, which was the open question.
  `contains_cpow_mul_coarsen` is therefore the form the generator should emit.
- **Not done, and the honest remaining scope.** The generator
  (`scripts/60_rung3_generate.py`) still emits a tower per `m`; it has to be
  changed to emit a factor-ordered chain plus staged prime towers, with the
  per-`m` adaptive `kE` and Taylor `n = 12` from the previous record. The
  ~78k-term / ~25 core-hour run has not been attempted. What changed is that
  the step at the bottom of that plan is now kernel-checked and priced, so
  the remaining risk is engineering rather than feasibility.
- **Caveat on the measurement.** The 0.5 s figure is four hand-written
  obligations on one machine, not a run over the plan's real sites, and the
  chain lengths there follow the factorisation of each `m` rather than a flat
  four. It is a go-ahead signal, not a cost model.

## Record: rung 3 — the certification architecture is proved; the evaluation
## engine needs one more stage (2026-08-10, second session of the day)

- **Built, zero sorrys, in the build (`DHCertSupport.lean`):** everything the
  offline certificate needs beyond arithmetic. `ComplexInterval.invC` (boxed
  complex inverse via `conj z/|z|²`); `rpow_neg_div_le` (the `b`-th-root
  trick: `x^{-(a/b)} ≤ P` from the single rational check `1 ≤ P^b·x^a`);
  `DH_mem_of_partial_enclosure_order2_boxed` (assembly with `s` ranging over
  a box — every hypothesis beyond two structural containments is a rational
  inequality); `dhSumBoxes`/`contains_dhSumBoxes` (partial-sum box as a fold,
  containment by induction); packaged correction-term lemmas; and the
  **maximum-modulus + Cauchy + mean-value layer**: `norm_DH_le_on_closure`,
  `norm_deriv_DH_le` (via Mathlib's
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`), and
  `DH_lower_on_hcell`/`vcell` (MVT along frontier segments through the 1-D
  parametrization `t ↦ DH ⟨t, y⟩`, `HasDerivAt.comp_ofReal`).
- **Negative result #1 — the old boundary runbook is dead.** Boxed-`s`
  interval evaluation of the partial sum has width ≈ `δ·Σ_m m^{-σ}·ln m`
  (per-term variations add with no cancellation): at any feasible geometry
  that is ~0.3 against a lower-bound headroom of ~0.009 — *infeasible at
  every subdivision*, killing "split the boundary segment until normLower
  clears ε′" (this file's earlier records and the half-day pricing in the
  previous record inherited that blind spot for the boundary; the centre
  evaluation is unaffected). Quantified by the planner
  (`lean/cert/rung3_plan2_report.md`). The fix that works: boxed evaluation
  gives cheap **upper** bounds (width only inflates them) on a *big* square's
  frontier → maximum principle → Cauchy ⇒ Lipschitz `L = M/(w₂−w)` on the
  small frontier → certified **point grid** with MVT between grid points.
  Verified plan v2 (`lean/cert/rung3_plan2.json`, 3137 exact checks):
  w = 3/64, ε′ = 1/2000, w₂ = 7/32, L = 16, 100 grid points (K 85–114),
  110 big boxes (K 17–61), centre K = 361; 77,675 certified terms.
- **Negative result #2 — one-shot `norm_num` cannot evaluate a full term
  box.** A single `dirichletTermBox 20 64 kL 10 m S = ⟨literal⟩` equality
  takes **8 min and then exceeds simp's step limit**: ~500 interval ops with
  multi-thousand-bit rational literals make simp's traversal explode.
  (`DHDemo`'s final blast survives only because its `n = 8, kE = 4` terms
  are ~100× lighter.) The *containment* lemmas per term stay cheap
  (0.3–0.5 s — they never evaluate the box; the measured 0.84 s/term from
  the previous record was containment-only and does not cover reading
  `normLower` off a box).
- **Built and working: the staged-evaluation toolchain.**
  `scripts/61_rung3_mirror.py` is a bit-exact `Fraction` mirror of the whole
  interval layer (a wrong mirror value cannot weaken the theorem — the
  kernel refuses the equality lemma), and `scripts/60_rung3_generate.py`
  emits per-site certificate files: per-term containments, literal-value
  lemmas, chunked partial-sum folds, corrections, the boxed assembly
  instantiation, and the site's `β`/`M`/ε′ fact. The mirror also computes
  exact `normLower`/`normBound` per site at generation time, so infeasible
  margins are caught in Python seconds — the planner's width-model
  uncertainty is retired. The pilot (K = 8 upper box) compiles everything
  *except* the literal-value lemmas, which hit negative result #2.
- **Negative result #3 — the log Taylor order, found here and then found
  better elsewhere.** This session measured that `logQ`'s width
  (`≈ k·2^{-n}`, amplified by `‖s‖ ≈ 85.7` into the term box) is what blows
  the ε′ budget at `n = 20`, and proposed raising the single coupled
  `TAYLOR_N`. The **fourth session's record below supersedes that**: it
  isolated the same cause against the grid's own β values, measured the
  threshold (`n = 28` marginal, `n = 32` shipped, margin saturating at
  ×1.01 because the residual is the inflation radius, not the series), and
  did the thing this record only noted as "a cheap future refinement" —
  **split the two orders**, `dirichletTermBox2 nLog nExp`, kernel-checked.
  Read that record, not this bullet, for the parameters. What survives here
  is the mechanism and its test:
  `tests/test_rung3_mirror.py::test_the_log_order_sets_the_width_and_the_exp_order_does_not`
  pins that the log order sets the width and the exp order does not, so the
  split cannot silently regress. An earlier draft of this record guessed
  the budget was loose and suggested *lowering* to `n = 12` (width 4.4e-3,
  hopeless); that guess is withdrawn.
- **The scoped fix — also now superseded.** This record proposed
  composite-chain term evaluation (`(mn)^{-s} = m^{-s}·n^{-s}`, towers only
  for primes) as the next move; it is **built and kernel-checked** in the
  record below (`contains_cpow_mul`, `contains_cpow_mul_coarsen`), measured
  at ~3 orders cheaper and matching the tower to four significant figures.
  `tests/test_rung3_mirror.py::test_composite_chain_agrees_with_the_tower`
  checks the chained box against mpmath rather than against the tower it
  replaces.

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
