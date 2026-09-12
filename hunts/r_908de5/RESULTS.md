# `beta := normLower`, the remedy lands, the predicted slack does not

**Status: settled, with one prediction in `docs/25` refuted.**

Two findings, and the second is the one worth the run:

1. **The remedy works.** Setting `beta := normLower(B.inflate r)` makes the
   rung-3 grid site inequality true by construction, and the obligation that
   then carries the weight, `eps' + L*h/2 <= beta`, the hypothesis of
   `ZetaLean.DH.DH_lower_on_[hv]cell`: still holds at all 104 grid sites, in
   both arithmetics measured. No statement is weakened, nothing is dropped,
   `L = 16` and `eps' = 1/2000` are untouched.
2. **`docs/25` §4.3 defect 2's prediction is wrong.** It states that after the
   remedy "the cell condition then carries >= 10x slack". Measured exactly in
   rationals over all 200 cell obligations: the worst clears by **1.3697x** in
   ball arithmetic and **1.3566x** in chained-rect. The prediction overstates
   the worst case by a factor of ~7.3. Worse for the prediction's logic, the
   remedy barely *moves* the worst case at all, it was already 1.3647x under
   `pred_beta`, so beta going up (ball) buys +0.4 % and beta going down
   (chained rect) costs -0.6 %. The slack did not move into the cell
   condition, because it was never the grid inequality's to give.

Nothing here bears on RH (`docs/08`). Nothing here is a result until it goes
through the battery or the funnel; this directory is exploratory by
construction.

## What the defect was

`pred_beta` in `lean/cert/rung3_plan2.json` came from mpmath dps-40 point
evaluations minus a 2e-11 sampling slack, i.e. it was drawn *at the achievable
bound*. So the site obligation

    normLower(B.inflate r)  >=  pred_beta                            (GRID)

sits at the line by construction in **any** arithmetic. Commit 44d3133
measured exactly that: 104/104 pass in ball arithmetic, 12 of them by under
1 %, the thinnest `g_right_15` by 0.03 %. A margin computed against a number
drawn at the bound is not evidence about the enclosure; it is evidence about
where the prediction was drawn.

## Before / after

`(GRID)`, ball arithmetic, 104 grid sites:

| beta source | worst margin | 12 thinnest | meaning of the margin |
| --- | --- | --- | --- |
| `pred_beta` (commit 44d3133) | 1.0003 (`g_right_15`) | under 1 % | how close the prediction was drawn to the bound |
| `normLower` (this hunt) | 1.0000, every site |, | nothing: true by construction, and it says so |

`(CELL)`: `eps' + L*h_i/2 <= beta_i`, one obligation per cell endpoint (200
over 104 sites), exact rational arithmetic over the plan JSON:

| beta source | obligations | failing | worst | worst site | median | best |
| --- | --- | --- | --- | --- | --- | --- |
| `pred_beta` (as shipped) | 200 | 0 | 1.3647 | `g_left_22` | 1.3924 | 8.9875 |
| `normLower`, ball | 200 | 0 | **1.3697** | `g_left_09` | 1.6179 | 11.6236 |
| `normLower`, rect + composite chains | 200 | 0 | **1.3566** | `g_top_20` | 1.3928 | 8.9576 |
| `normLower`, rect non-chain (`scripts/60` as shipped) | 24 | **24** | **0.2348** | `g_left_10` | 0.5557 | 0.7743 |
| `docs/25` §4.3's prediction |, |, | ">= 10x" |, |, |, |

Two things to read off it. The worst case moves by under 1 % in either
direction, the remedy is a change of *what the number means*, not a change in
headroom. And the median only improves in ball arithmetic (1.3924 -> 1.6179,
i.e. +16 %); in chained rect it is flat at 1.3928, because chained-rect
`normLower` tracks `pred_beta` to a fraction of a percent at 104 of 104 sites.
The improvement is a property of the ball enclosure, not of the beta source.

Read the fourth row before the third. It is the one that decides whether the
remedy is landable today.

## The arithmetic the remedy needs

There are three enclosure arithmetics in this tree, not two, and only the
first of them is what `scripts/60_rung3_generate.py` actually emits:

* **rect, non-chain**: `mirror.term(m, S, 20, 64, 10)`, a single Taylor order
  per term. This is the arithmetic bit-identical to the `ComplexInterval`
  literal in every generated Lean file today.
* **rect, composite chains**: `mirror.term_chain` at `nLog 32 / nExp 20`,
  building `m^-s` from a coarsened product of its prime factors' boxes. What
  `scripts/62` and `scripts/64` measure, and what `docs/25` §4.3's "30 of 59
  sites fail by under 1 %" was measured in.
* **ball**: `scripts/63_rung3_ball_mirror.py` on the same chains. What
  `scripts/65` ran for commit 44d3133.

Measured at the two thinnest sites, `normLower` relative to `pred_beta`:

| site | rect non-chain | rect + chains | ball |
| --- | --- | --- | --- |
| `g_left_10` | 0.1716 | 0.9997 | 1.0081 |
| `g_top_10` | 0.3659 | 0.9937 | 1.0005 |
| `g_right_15` | 0.5281 | 0.9993 | 1.0003 |

Over the 12 sites measured in all three, non-chain `normLower/pred_beta` runs
0.1716 to 0.5462, the enclosure is 2 to 6x too wide at a point. Setting
`beta := normLower` there yields betas a fifth to a half of `pred_beta`, and
`(CELL)` fails outright at every one of the 24 obligations they carry, the
worst at 0.2348. **So the remedy is
not free: it is contingent on the generator emitting composite chains.** The
Lean support for that already exists and is unused by the generator:
`ZetaLean.ComplexInterval.dirichletTermBox2` (split Taylor orders),
`contains_coarsen`, and `contains_cpow_mul` in `DHCertSupport.lean` (the
multiplicativity step `m^-s = a^-s * b^-s`). What is missing is only the
emission: one chain lemma per composite `m` instead of one flat term lemma.

That is a bounded piece of generator work, and it is not this hunt's budget.

## What changed in the tree

* `scripts/60_rung3_generate.py`: grid `beta` is now **read off the
  enclosure** (`beta_literal(normLower)`, rounded down to a multiple of
  `2^-40` so the Lean literal stays small and the claim stays true) instead of
  copied from the plan's prediction. `--beta plan` restores the old source.
  New: `cell_requirements(plan)` computes `eps' + L*h/2` per site and the
  emitter now **asserts it at generation time**, so a site whose beta cannot
  support its grid cell fails loudly at generation rather than passing at the
  line. Under the non-chain emission that assertion fires, correctly. It is
  naming the real blocker instead of hiding it behind a drawn-at-the-bound
  prediction.
* `scripts/65_rung3_full_validation.py`: the grid verdict was
  `normLower >= pred_beta`, which under the remedy is vacuous. It is now
  `normLower >= eps' + L*h/2`, the obligation the certificate actually spends
  beta on. `grid_margin_pred` is kept per site so the run stays comparable
  with commit 44d3133.
* No Lean source changed. `le_norm_of_enclosure` already accepts any rational
  at most `normLower`, so the remedy needs no new kernel-side machinery, and
  since nothing under `lean/` was edited, the axiom audit is unchanged by
  construction.
  `lake build` was run from a cold toolchain (elan installed from scratch,
  toolchain `v4.33.0-rc2`, Mathlib cache fetched, 8681 files). **It did not
  come back green in this container**: 8801 of 8803 targets built, and two
  heavy modules unrelated to this change, `ZetaLean.ChebyshevBounds` and
  `ZetaLean.Pub1.CertAtoms`, were killed with exit 137 (out of memory) after
  489 s and 733 s, because the build was sharing a 4-core, 15 GB container
  with this hunt's exact-rational sweep. That is a resource verdict, not a
  proof verdict, and it is recorded rather than rounded up. A targeted rebuild
  of the two on an idle machine put `ChebyshevBounds` through in 8.5 s and
  carried `Pub1.CertAtoms` past 1245 s, well beyond the 733 s at which it was
  killed, without failing, but it had not finished when this hunt closed, so
  what is on the record is "8801/8803 built, two OOM kills under contention,
  rebuild in progress", and not the word green.

  **Settled 2026-08-17, after this hunt closed.** The rebuild the paragraph
  above left unfinished was run to completion on an idle 64 GB machine, from
  the same `origin/main` (`ba657c7`) with `lean/` byte-identical to it,
  `git diff ba657c7 HEAD -- lean/` empty, so this reads the tree the hunt
  reported on and not a repaired one. **`lake build` completed all 8803
  targets, exit 0, zero `error:` lines**, and exits 0 again on an immediate
  second invocation. `ZetaLean.Pub1.CertAtoms`, the module killed at 733 s,
  elaborated in **27 m 33 s** without approaching failure;
  `ZetaLean.ChebyshevBounds` was never in doubt after its 8.5 s clear. So the
  reading the hunt declined to round up was the right call and the answer it
  was waiting for is: **the two kills were the container, not the proofs.**

  Recorded here rather than by editing the paragraph above, because the
  hunt's refusal to say *green* on the evidence it had is the part worth
  keeping. What this still does not settle: it is one machine, so it bounds
  the memory a clean build needs from above and nothing else, and CI has not
  been shown to have that headroom. The operator note that Lean builds and
  heavy Python sweeps must be scheduled serially in a 15 GB container stands
  unchanged, this measurement is the reason it stands, not a reason to drop
  it.

## What this does not settle

* **The 12-site sample in the non-chain row.** The full 104-site non-chain
  sweep was not run; 12 sites were, chosen thinnest-first by ball margin,
  carrying 24 cell obligations between them. All 24 fail, by 1.3 to 4.3x, so
  the conclusion is not delicate, but the number quoted is a sample, not a
  census, and it is a sample deliberately drawn from the hardest end.
* **Whether the generator's chain port keeps the literals small.** Coarsening
  at `p = 64` is what keeps chained products from reaching ~508-bit rationals
  (`DHCertSupport.lean` records the measurement). The port was not attempted
  here, so its literal sizes and kernel cost are unmeasured.
* **Whether 1.37x is enough.** It is above 1, which is what the Lean lemma
  needs, and that is all this hunt claims. Whether a certificate whose worst
  cell obligation clears by 37 % is one you want to spend ~18 h of kernel time
  on is an allocation question, not a mathematical one.
* **The big boxes and the centre.** Untouched. Their margins (2.14-3.85 and
  1.30) come from commit 44d3133 and carry no drawn-at-the-bound caveat.

## Loose threads

* **`docs/25` §4.3 says ">= 10x", the measurement says 1.36-1.37x.** The document
  is on main and is cited as the remedy's justification. It has not been
  corrected, this hunt has no licence to edit `docs/`, and the correction is
  one sentence. *First step*: amend `docs/25` §4.3 defect 2 to state the
  measured worst-case 1.3697x with a pointer here, or open an issue if the
  document is meant to stay a frozen record of what that run believed.
* **The cell condition is gap-limited, not beta-limited.** Every one of the
  five worst cells sits at the *largest* adaptive gap `h`, not the smallest
  beta: `L*h/2` is 98 % of the requirement and `eps'` only 2 %. Raising betas
  therefore buys almost nothing at the margin, which is exactly why the
  remedy moved the worst case by 0.4 % rather than by 10x. *Why it matters*:
  the plan's own hostile-referee note 4 prices a direct enclosure-carrying
  `|DH'| <= ~2` bound at "the grid collapses to ~15 points and the total to ~10k
  terms", a 7.5x cost cut, and the same change is what would give the cell
  condition real slack. *First step*: price a direct interval bound on `DH'`
  on the small square against the current Cauchy route's `L = 16`.
* **Two rect arithmetics are silently interchangeable in the scripts.**
  `scripts/60` uses non-chain, `scripts/62`/`64` use chains, both call
  themselves "rect", and the 2-3x width difference between them is what makes
  `docs/25`'s "fail by under 1 %" and this hunt's first measurement disagree
  by 60 %. *First step*: give `61_rung3_mirror.py`'s two entry points names
  that cannot be confused in a report, and state which one a measurement used
  wherever a rect number is quoted.
* **`beta_literal` rounds to `2^-40` with no measurement behind the 40.** It
  is comfortably below the enclosure widths seen here, but it was chosen, not
  derived. *First step*: check the smallest gap between `normLower` and the
  cell requirement across the 104 sites and set the rounding from it.
