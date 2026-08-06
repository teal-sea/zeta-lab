# ROADMAP.md — what was built, why, and what is next

`README.md` says what the lab *is*. `AGENTS.md` says how to work in it. This file
records the **decisions**: why the work went the way it did, what is deliberately
not being attempted, what is known to be missing, and what the next build is.

It exists because the reasoning behind a project is the first thing lost between
sessions, and the cost of losing it is repeating settled arguments.

The latest session snapshot and exact continuation checklist are in
`HANDOFF.md`; this roadmap remains the source of project decisions.

---

## What is built

| phase | what landed | why |
| --- | --- | --- |
| 1 | `core`, `zeros`, `explicit`, `statistics`, `heatflow` + docs 00–08 | the classical machinery, each identity measured rather than assumed |
| 2 | `weil`, `epstein` + docs 09–11 | the two ontology gates that can be made computational (positivity; the counterexample constraint) |
| 3 | `rigor`, `li`, `finitefield`, `criteria` + doc 12 | certified arithmetic; the real-rootedness lane; the universe where RH is a theorem; the remaining equivalence faces |
| 4 | `discovery/` + `scripts/13` | the conjecture funnel, schema-first, with conversion metrics |

The organising chain is in `README.md`: theta is the heat kernel → Poisson
summation → the functional equation → the mirror at `Re s = 1/2` → the explicit
formula → the same heat flow on `Ξ` gives the de Bruijn–Newman constant, where
RH ⟺ Λ = 0 and Λ ≥ 0 is a theorem.

---

## The strategic bet, and its honest status

Of the attacks catalogued in `docs/08-why-it-is-hard.md`, every one has a
standing no-go result against it. The **ontology route** — new objects, new
actions, new rulebooks (`docs/09`) — is the only strategy with a win on the board
(the Weil conjectures, 1974) and no impossibility theorem against it. That is why
phases 2–4 point that way.

Three independent lines converge on the same corner, which is the reason for the
emphasis on heat flow and real-rootedness (`docs/05`, `zeta/li.py`):

1. Λ ≥ 0 says the zeros sit at an exactly *marginal* configuration — the
   signature of an equilibrium of some dynamics.
2. GUE statistics say they behave like the spectrum of a chaotic system.
3. Poincaré fell to a smoothing flow with singularity control; Kadison–Singer
   fell to real-rootedness control via its equivalence web (`docs/12`).

**Honest caveat, recorded deliberately.** Calling this "the field's consensus"
overstates it. The content is standard; the confidence is not. Many number
theorists would say plainly that nobody knows what RH needs. The bet is a bet.

---

## What is deliberately *not* being attempted

- **Proving RH, or any part of it.** See `docs/00` §scope and `docs/08`. Nothing
  computed here is evidence. If a computation appears to settle something, the
  correct inference is a bug.
- **Representing ontology *proposals* inside the discovery funnel.** The schema
  has no representation of a mechanism (`discovery/README.md` §7, blind spot 5),
  and a proposed new ontology is nothing but a mechanism. Forcing it in would
  make the schema pretend. Ontology work stays in `docs/` and is judged against
  the four gates in `docs/09` directly.
- **Chasing computational reach for its own sake.** mpmath, Arb, PARI/GP,
  SageMath and LMFDB already exist and are better at raw computation than
  anything written here. This repo uses them as engines and independent oracles.
  What it adds is the assembled workbench and the written course.

---

## Completed audits

**Phase 4's cross-cutting audit is complete.** It forced plug-in exceptions and
an operating-system kill, resumed the open checkpoint, exercised duplicates,
grepped code/docs/console output for novelty leakage, recomputed the scorecard
from raw run records, mutation-tested the Mertens adjudicator by forcing a false
`survives`, and mechanically checked the domain-agnostic seam. Two accounting
defects were fixed: crash-interrupted candidates now remain in per-generator
denominators, and `refuted` no longer counts as `unsettled`.

**Schema 1.1 follow-up shipped.** Candidates can carry typed `related_to` edges:
`implies` for a directed implication and `equivalent_to` for a symmetric claim.
Edges are unhashed annotations, so adding one never changes candidate identity.
The schema validates their shape but deliberately does not require targets,
reciprocal edges or verdict propagation; those are whole-ledger concerns.

**Reference run reproduced on 2026-08-04.** Starting from an empty private
ledger with seed `20260802`, all six generators emitted 26 candidates in 4.29 s:
20 known, 1 trivial, 5 inconclusive, 0 refuted and 0 survivors. The append-only
ledger contains 52 records because each candidate has an initial and a terminal
record; the run stream contains one complete run. Raw records remain gitignored.

**The ledger is shared between machines without being published (2026-08-04).**
A second machine cloning this repo got an empty `conjectures/`, which is the
ignore rule working as designed. The fix was *not* to relax that rule: this
repo is public, and committing the ledger would publish unreviewed leads as if
they were checked claims. The records live in a separate **private** repository
cloned in place at `conjectures/`, driven by `scripts/ledger_sync.sh`
(`init`, then `pull`/`push`/`sync`). The public tree still carries no record and
`.gitignore` is unchanged. The record files are append-only JSONL marked
`merge=union`, so two machines that both ran the funnel merge without conflict;
the script drops the exact-duplicate lines a union merge can leave behind.
Syncing is manual and deliberately so — pull before a run, push after.

## Known gaps

Listed because an undocumented gap becomes an assumption.

1. **The documents were audited by agents, not by domain experts or against the
   literature.** The audits caught real errors, which is evidence they work, but
   correlated blind spots are exactly what that method cannot catch. No one with
   domain expertise has read a line of it. This is the largest unhedged risk in
   the repository.
2. **Expected funnel yield is approximately zero, by design.** Nearly everything
   will return already-known or refuted. The first real run: 26 candidates → 20
   known, 1 trivial, 5 inconclusive, 0 survivors. That is the machine working.
   A conjecture factory that produced discoveries on its first run would be
   broken. The value is the discipline and the record, not the hits.

---

## Next build: moments

Ladder rung 1 from `docs/12`'s closing section, and the most realistic target
identified so far.

**First increment shipped.** `zeta/moments.py` ingests LMFDB plain-text exports
and all six tables on Odlyzko's public index, including the offset headers at
the `10^12`, `10^21`, and `10^22` landmarks. It verifies caller-supplied
checksums, records the actual input digest, and validates declared counts,
contiguous indices, positivity and strict ordering. Absolute ordinates stay as
exact decimal base-plus-offset data: converting the `10^22` window to float64
would collapse neighbouring zeros to the same number. It computes no zeros.

**Second increment shipped.** The finite estimator consumes separately sourced
samples of `|ζ(1/2+it)|` inside an imported zero window. This separation is
mandatory: zero ordinates do not determine the values between them. It reports
the caller-supplied value error and a nested-grid sampling-error estimate in
different fields. The reference layer derives the Keating–Snaith/CFKRS leading
constant, recovers the proved coefficients `1` and `1/(2π²)` for the second and
fourth moments, and keeps the Euler-product truncation visible for the
conjectural sixth and eighth moments. The scorecard withholds those open rows
unless both proved rows pass a caller-stated calibration tolerance; a mutation
test changes the fourth-moment constant and verifies that the gate fails.

**Third increment shipped.** A critical-line sample loader now reads exact
`offset abs-zeta absolute-error` rows, detects gzip, verifies caller-supplied
checksums and row counts, and binds every value file to the SHA-256 of its
imported zero window. The estimator handoff refuses a different zero-table
digest. A 2026-08-04 source audit found published methods, aggregate results,
selected extrema and plots, but no public dense row table suitable for moment
estimation; `docs/13-moments.md` records the sources checked.

No external critical-line **value** dataset is bundled. Odlyzko and LMFDB zero
tables supply the window and provenance, not `|ζ|` samples. Acquiring such a
dataset therefore remains an operator/data task, not something the estimator
silently fabricates. The complete contract is in `docs/13-moments.md`.

**Why.** The 2nd (1918) and 4th (1926) moments of `ζ` on the critical line are
proven; the **6th and 8th are open**, with exact constants predicted by random
matrix theory (Keating–Snaith). Moments are self-convolutions — `ζ(s)² = Σ d(n)n^{-s}`,
and the `2k`-th moment corresponds to the `k`-fold divisor function — so this is
the analytic face of the same convolution algebra that produces the Euler
product. It is also the retail version of the Lindelöf Hypothesis, the domino
most likely to fall before RH.

**Critical design constraint.** Do **not** compute the zeros for this. The lab
holds ~10⁴ zeros reaching height ≈3.5×10³; the moment behaviour worth measuring
lives many orders of magnitude higher, and Odlyzko's published tables reach the
10²⁰–10²² landmarks. Build an ingestion path for external zero tables
(LMFDB, Odlyzko) and run the verified machinery against real data at real
heights. Computing our own would be both slower and worse.

**Fourth increment shipped.** `scripts/14_moment_experiment.py` generates its own
critical-line values at modest height and measures the finite moments, rather
than waiting on an external dataset. The 2nd moment calibrates against the
Ingham two-term global main term; this is an instrument-validation step within
the research program, not an end in itself.

The same increment checks the leading terms against Cauchy–Schwarz. The result
is deliberately narrow: pairwise consistency thresholds of `3.6e8` (4th/8th),
`1.2e18` (6th/12th), and `1.1e30` (8th/16th). Below one, both named leading
forms cannot be dominant; it does not identify which one fails and is not a
computational-reach bound. See `docs/13-moments.md` §10.

**Fifth increment shipped.** The full CFKRS moment polynomial of degree `k²` is
implemented for `k=1,…,4`, in the convention `Pₖ(log(t/(2π)))`. The theorem
cases calibrate the factor convention; published sixth/eighth coefficients
retain their conjecture labels and stable-decimal, non-certified provenance.
The scorecard gate and local experiment now integrate every polynomial term
over the actual window. Leading-only results remain a separate
Cauchy–Schwarz diagnostic.

**Sixth increment shipped.** A single finest-grid run now accumulates all nine
combinations of three nested prefix windows and three nested spacings. At
`t=10⁵`, width `4000`, spacing `0.005`, grid drift is below `1.1e-6` for all
four moments, but window-ratio drift grows from `0.52%` for the second moment to
`18.05%` for the eighth. The quadrature is resolved; finite-window variation is
now the identified limitation, with peak concentration still to be measured.
These observed drifts are explicitly not error bounds or independent samples.

**Seventh increment shipped.** The same one-pass sweep now supports deterministic
disjoint blocks and ranked trapezoidal contributions. Across eight width-500
blocks, ratio dispersion rises from `1.28%` for the second moment to `34.63%`
for the eighth. The largest `1%` of grid intervals carries `25.81%`, `67.06%`,
`88.67%`, and `96.49%` of the second through eighth integrals. This directly
identifies peak concentration in the pinned run without calling block
dispersion a standard error or treating disjoint blocks as independent draws.

**Eighth increment shipped.** The block/peak study now replicates at `10⁴`,
`10⁵`, and `10⁶` with 6,000 nominal local zero gaps, 128 points per gap, and
768,001 samples per window. All aggregate moment-polynomial ratios remain
within `6.4%` of one. Meanwhile the top-one-percent share of the eighth moment
rises `90.25% → 96.52% → 98.96%`, and its block-ratio CV rises
`17.91% → 34.93% → 76.81%`. Agreement replicates while concentration and local
volatility increase; three deterministic windows still do not form a sampling
distribution.

**Ninth increment data retained; verdict withdrawn.** The four-window-per-height
table is numerically valid, but the claimed pre-registration was contaminated:
window zero in every band exactly reused the earlier replication window, and
the monotone concentration gate was chosen after seeing those values. The
historical gates have no falsification weight or calibrated error rate. At
`10⁶`, the observed eighth-moment range `0.5831–1.4362`, pooled ratio `1.0628`,
and median top-one-percent share `99.12%` remain descriptive data only.

**Next work is not exposure scaling.** First perform the primary-literature
novelty audit. Then build a matched log-correlated Gaussian null through the
identical measurement pipeline and add a Davenport–Heilbronn negative control.
Any future zeta attack must use wholly untouched windows and gates calibrated
against the null before evaluation. If the null reproduces concentration plus
pooled recovery, record the observation as explained/generic and stop; invoke
the formal counterexample battery before any RH-explanatory structural claim.

**That programme is now complete and the answer was "explained".** Both
prerequisites were carried out and the exposure-scaling attack was never run,
because the controls settled the question it was meant to ask. Details and
limits in `NULLCONTROLS.md`; the instrument is `zeta/surrogate.py` and
`scripts/15_null_control.py`.

*Literature.* The concentration heuristic is Soundararajan's (Annals 2009):
values of size `(log T)^k` on measure `T(log T)^{-k²}` supply the CFKRS-sized
moment. Odlyzko–Rubinstein already reported that finite-height CFKRS agreement
converges slowly with large window-to-window fluctuation driven by rare large
values. The candidate observation restates known material; only the specific
"top x% carries y%" phrasing appears non-standard, which is a choice of
statistic, not a result.

*Controls.* `zeta.surrogate.interval_statistics` reproduces `block_peak_sweep`
on real zeta data to `1.7e-16`, so every control runs the same code path. Both
randomised Euler product surrogates reproduce the rise of concentration with
moment order and height using no arithmetic input; the arithmetic factor is not
the explanation, since a top-share is a ratio of integrals and any scale factor
cancels. Neither is the variance: zeta's exceeds both surrogates' while its
upper tail is *shorter*, because `log|ζ|` diverges at each zero and both
surrogates are zero-free — so calibrating a zero-free null to zeta's variance
is the wrong move. The CUE control, whose only quantity `N = round(log(T/2π))`
is fixed by the height and not fitted, matches within a couple of points at
`10⁶` (`31.58/76.25/93.68/98.39` against `30.26/78.26/95.75/99.26`) and matches
the `p99.9` tail at `3.3707` against `3.3605`. The Davenport–Heilbronn function
shows the same rise with order and height, so under gate #3 the pattern
distinguishes nothing structural.

*Rate of approach.* With the band taken from 200 CUE seeds per height rather
than a chosen threshold, the eighth-moment gap to the CUE median runs `-19.03%`
at `10³`, then `-7.26%`, `-2.01%`, `+0.84%`, `-0.23%`, `+0.63%` through `10⁸`.
Zeta lies outside the central 95% only at `10³` and only for the 6th and 8th
moments. The band is wide enough that "inside" is a weak test — the 2nd and 4th
moments are inside at every height — so this bounds the residual rather than
demonstrating agreement.

*Byproduct worth keeping.* `a_k` from the random Euler product's exact
intensity moment times `g_k` from the Keating–Snaith product converges to the
CFKRS leading coefficient derived independently in
`scripts/14_moment_experiment.py` (ratio `1.0016` at `N = 40000`, falling
tenfold per decade of `N`). Each control supplies one factor and neither is
read from a table.

**Decision: no `conjectures/` ledger entry.** The pattern is generic, the
RH-violating counterexample shares it, and the quantitative gap to the
random-matrix control closes with height. Nothing here is evidence for or
against RH.

**What is actually open in moments.** Exact `N(T)` exposure in place of nominal
mean-gap windows (carried over from the W7 follow-up below). Seed replication
of the CUE and Davenport–Heilbronn rows, which are single-realisation. The
mild drift of the 2nd and 4th moments above the CUE median at `10⁷`–`10⁸`
(`+7.73%`, `+10.64%`, both inside the band), which is window luck until
replicated across offsets.

**Red-team W7 follow-up.** The unusually close `10⁴` pooled ratios were audited
for circularity, pointwise evaluator error, and grid error; no defect was found.
A fresh `1.5×10⁴` anchor reproduced near-unity pooling (largest deviation
`0.156%`). This remains descriptive pending null calibration. Replacing nominal
mean-gap windows with exact `N(T)` exposure remains open.
