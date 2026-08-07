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
| 5 | `lean/` (Lean 4 + Mathlib) + docs/09 §5.1 | the certified arm (kernel-checked theorems, rung 1 done) and the strengthened gates: factorization through a positive structure, not positivity estimates |
| 6 | `harness/` + `docs/doors/` | the referee factored out of the laboratory: the lab becomes extensible by **department**, and gains a front page per audience instead of one per repository |

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
  correct inference is a bug. (The `lean/` arm does not bend this rule:
  formalizing *known* theorems — ground-truth values, Davenport–Heilbronn — is
  certification of the literature and of this lab's reference points, not an
  attempt on RH.)
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

**Seventh generator shipped and the reference run re-measured (2026-08-06).**
`zeta_legendre_weil` runs the Riemann–Weil explicit formula through
`zeta.weil.legendre_pair(n)` — a triangle bump supported exactly on
`[log n², log (n+1)²]`, so the prime term sees only the Legendre interval.
Per interval it emits the identity instance (dies `known`: it instantiates a
theorem, matched by a custom catalogue matcher) and the prime-detection
inequality (dies `known`: finitely verified for every reachable n, with the
range guard `(n+1)² ≤ 4e18` in the matcher). Default reference run: 32
candidates → 26 known (81.2 %), 1 trivial, 5 inconclusive, 0 survivors — the
no-survivor headline is a pinned design property, so the third observation is
**opt-in**: with `legendre_mass_constant` in the context, the widest
interval's Λ-mass is emitted as a measured constant no catalogue tabulates, a
designed survivor. Its one recorded run (2026-08-06, in the private ledger)
exercised the full path — escalation to 60 digits, sympy
cross-summation, PSLQ non-identification — and then the operator-level
literature check the offline gate refuses to fake: a networked search
(2026-08-06) found the localisation device standard in the explicit-formula
literature, the specific triangle-weighted statistic untabulated (an ad-hoc
derived quantity, not an invariant), and a structural reason the instrument
cannot decide Legendre — compact support forces a non-sign-definite zero
side, so RH-strength bounds give cancellation, not positivity. Disposition:
instrument documented, lead closed as generic; no claim. The ancestor
script `scripts/40_legendre_weil.py` overprinted "mathematically proves
primes exist"; it now defers to the library pair and states the honest scope.

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

## Five longshot probes, run to their walls (2026-08-06)

Five deliberately improbable attacks, each pushed until it produced a
measurement or hit a named obstruction. Full account in `docs/18`; modules
are `zeta/inverse.py`, `leeyang.py`, `relations.py`, `quasicrystal.py`,
`synthesis.py`. None advances RH. The decisions worth recording:

- **Existence of a Hilbert–Pólya operator is not a fact about ζ.** Wu–Sprung
  inverse spectral reconstruction hits the first 25 ordinates to 1.2e-4 mean
  gaps — and hits the *Davenport–Heilbronn* on-line ordinates to 2.5e-4. The
  Abel inversion consumes a list of reals and cannot see off-line zeros.
  Gate #3: distinguishes nothing. Any future Hilbert–Pólya claim in this repo
  must be about a *property* of the operator, never its existence.
- **Ferromagnetic inequalities do not see RH.** The free energy of the Φ spin
  model is exactly log ξ (normalization ∫Φe^{hu}du = ¼ξ(½+h/2), derived not
  recalled). GHS holds for ζ at every probe — and equally for DH. Lee–Yang
  membership *is* RH; it is a restatement, not a route.
- **The quasicrystal gate is the sharpest one in the repository, and it is
  about factorization.** The zero measure's Fourier transform is atomic at
  log n with weights ∝ Λ(n)/√n; ζ is silent at composite non-prime-powers
  (26.8× separation with 1000 zeros) precisely because of the Euler product,
  while DH's −f′/f is loud there (b₆, b₁₄, b₂₁, b₂₆ all > 1.9 in modulus).
  **This is the only probe of the five that the counterexample fails.** It
  detects the Euler product, not RH — but it is a measured instance of
  `docs/09` §5.1's strengthened gate: factorization, not positivity.
- **PSLQ nearly lied, and the guard is now permanent.** At the textbook
  precision the n=20 search returned a "relation" (coefficients ~7e5,
  residual 4.4e-104) that survived recomputation at 300 digits and was pure
  pigeonhole accident. `zeta/relations.py` now carries a 40-digit guard, a
  residual gate, and a third status `inconclusive_floor_noise`. Standing rule
  reinforced: a finding that does not shrink when you improve the
  approximation is an artifact of the search.
- **`mp.diff` is unsafe on this repo's rounded functions.** Both `dh_f` and
  `xi` round internally and are bit-constant across `mp.diff`'s step, so it
  returns exactly 0 with no warning. Hand-rolled stencils with explicit steps
  are mandatory; both traps are pinned by regression tests.

Also recorded: RH ⟺ the prime signal (ψ(e^u)−e^u)/e^{u/2} has finite mean
power, whose value under RH is 2 + γ_Euler − log 4π = 0.0461914179 (RMS
0.2149), verified by three independent routes. The wall is Goldston–Montgomery:
proving finiteness from the prime side is equivalent to pair correlation.

**No `conjectures/` ledger entry.** Four probes are refuted by gate #3 or are
restatements; the fifth detects a property (Euler product) that was already
known to separate these two functions.

### Follow-ups: what the probes taught, made quantitative (2026-08-06)

Three further decisions came out of pushing the above to conclusions.
Modules `zeta/factorization.py` and `zeta/detector.py`; full account in
`docs/18` §6–7.

- **Gate 4 is now a decision statistic, not a judgement call.** For
  −f′/f = Σ bₙn^{−s}, D(f) = (composite-supported energy)/(prime-power
  energy) is **exactly zero iff f has an Euler product** — both directions
  are proved, not heuristic — and is computed from coefficients alone, which
  is §5.1's Requirement A on provenance. ζ and the quadratic characters mod
  3, 4, 5 score ~1e-32; DH scores 0.979. Crucially, against a matched null
  of random non-factoring sequences (median 1.33, 5–95% band 0.53–4.31) **DH
  sits at the 27th percentile — typical, not an exotic near-miss.** Anything
  claiming to "almost" factor must beat that null by orders of magnitude.
- **The functional equation and the Euler product are independent
  constraints.** DH's κ is forced to twelve digits by F(s) = F(1−s), yet on
  the family aₙ = [1, t, −t, −1, 0] it is *not* a critical point of D
  (slope +1.154); no member of the family factors, and the minimum sits at
  t = 0. This is Gate 2's "symmetry alone is provably insufficient" measured
  *locally at DH*, which is finer than arguing it from DH's mere existence —
  and it is why Gate 4 cannot be derived from Gates 2 and 3.
- **Position-sensitivity is the axis that matters, and one statistic has
  it.** The organising lesson of the whole session: ζ(s−δ) has the *same
  ordinates* as ζ with its zeros on a different vertical line, so **no
  ordinate-only statistic can locate the critical line** — which retroactively
  explains why the Wu–Sprung and Lee–Yang probes had to fail. The Weil
  explicit formula evaluates zeros at γ_ρ = (ρ−½)/i, complex off the line, so
  `residue(c) = [arithmetic side] − [on-line zeros only]` isolates exactly
  what the on-line zeros fail to explain. ζ is silent at 1.6e-15; DH spikes
  at its off-line ordinate with **+4.096324360133627** against a predicted
  quadruple contribution of **+4.096324360133638**, and the peak height
  recovers |β−½| = 0.30851718245662 (true: …64). Off-line zeros detected and
  *measured* without being solved for. Not a proof over any range, not
  certified, and it cannot distinguish an off-line zero from a missing
  on-line one — so it is only meaningful paired with an independent count
  (`online_list_is_complete`).

**Standing methodological rule, earned three times today.** PSLQ returned a
fake relation stable at 300 digits; `mp.diff` returned exactly 0 on both `xi`
and `dh_f`; a sign-flipped derivative stencil produced order-1 ζ residues
that looked like signal. All three shared one signature: **the error did not
move when the approximation was improved.** A real quantity responds to added
precision; an artifact does not. Every new instrument here gets a control
whose job is to detect exactly that.

## The department architecture (2026-08-06)

**The decision:** the laboratory extends by *department*, not by directory, and
a department is defined by what can kill its claims.

`ontology/` had already solved half of this — a domain-agnostic core plus
subject-coupled plugins, seam enforced by tests rather than by intention. But
the falsification instruments were welded to zeta, so a second subject could
inherit the funnel and not the referee. The referee is the part worth
inheriting: it is the only thing here a textbook, a notebook or a literature
survey does not already do (docs/17).

`harness/protocol.py` abstracts the four instruments the lab already ran by
hand into roles — **Subject** (the genuine article and its rivals), **Decoy**
(ablation), **Surrogate** (null control), **Lesion** (detector power) — bundled
into a `Battery`. A `Department` is a battery plus a door plus reference claims
with known verdicts.

**The admission rule: no department without a battery.** `validate_battery`
refuses one with no rival (no modus tollens available to it), with neither
decoy nor surrogate (no way to show an observation empty), or with no lesion
(detector power assumed rather than measured). A department must further
declare at least one reference claim its battery kills and one it passes,
because a battery that has only ever said "no" cannot be told apart from one
that says no to everything.

The cost of a purpose is therefore a door plus a battery plus a listing in
`KNOWN_DEPARTMENTS` — and `tests/test_department_conformance.py` is
parametrized over that dict, so listing it is what turns its audit on. There is
no step where a human waves it through.

**Non-goals, stated so they are not re-litigated:**

- *Not* a plugin system for the mathematics. `zeta/` is department #1, not a
  template; nothing was moved and no import changed.
- *Not* a claim that the protocol is subject-neutral in practice. It is
  domain-agnostic by test (AST scan, `sys.modules` check, lexical scan), which
  is a weaker and checkable claim. Whether the four roles carve a *second*
  subject well is unknown until there is one.
- *Not* evidence machinery. A claim surviving every instrument is a candidate
  for where a real argument must live. Nothing more, per docs/08.

**What it caught on day one.** `zeta.factorization.factorization_defect` —
Gate 4 as a decision statistic, D = 0 exactly when f has an Euler product —
looked like an ideal third distinguishing claim. It is not: the Epstein form
(2,1,3) does not represent 1, so that series has a₁ = 0 and the statistic
raises. `run_battery` recorded the exception and left `distinguishes` False,
because a rival that did not answer has not been excluded. Had it counted the
crash as a refutation, D would have been promoted from "works on three of four
subjects" to "the decision procedure for Gate 4". Pinned in
`tests/test_harness_zeta_department.py`.

---

## Research dossiers: a probe that stayed a probe (2026-08-06)

**The decision:** `dossier/` is an experiment in representing mathematical
research state — intent, definitions, provenance, evidence, failed attempts,
proof obligations and verification status — as data an agent can resume from.
It ships as a **probe**, registered in no department and given no door.
Design and full rationale: `docs/19-research-dossiers.md`.

Two ideas are under test, both narrow on purpose:

- **Intent is data.** What an object is *for*, in prose, before any formula,
  plus what it is most likely to be confused with. A definition can be checked
  against a formula; an intent can only be stated, and stating it is what makes
  a later mismatch visible. The worked example is Hardy's Z, chosen because
  `|zeta(1/2+it)|` is real, even, and vanishes at exactly the same points — and
  is useless, because the whole purpose of Z is that it changes sign.
- **"Verified" is four independent things.** Numeric agreement, enclosure
  arithmetic, the published record and a proof kernel fail differently.
  `dossier/status.py` keeps four axes, offers no aggregate, and makes
  `Support.__bool__` *raise* so `if support:` is an error rather than a silent
  collapse.

**Why it is not a department, which is the useful part.** The admission rule
needs rivals: things that share the claimed structure and lack the property.
A dossier has none of its own. Killing the `|zeta(1/2+it)|` candidate is a
claim about zeta, adjudicated by the *zeta* department's subject matter; the
dossier layer contributed the bookkeeping, not the refutation. And a battery
built from malformed dossiers would be a unit test of a validator wearing a
battery's clothes. So:

> A department whose battery is another department's battery is not a
> department.

The rule was not weakened to admit it. What would change the answer: making the
subject *representations of research state* rather than the mathematics being
represented, so that a rival is a competing representation — a flat notes file
plus a `verified: bool` — measured on a resumption task the dossier claims to
do better. That needs two more worked examples and a scoreable task first.

**Non-goals:** not a platform, not a framework, not a replacement for Mathlib,
not a second ledger or verdict vocabulary (`ontology` owns those and
`Provenance` is imported from it), and not a certificate issuer ("certified"
stays reserved). Nothing in it is evidence for RH.

**One thing it produced beyond bookkeeping.** Checking the dossier's claim that
the two in-tree definitions of Z agree settled a convention question: the
completed-zeta route needs no branch of log Gamma because `Gamma/|Gamma|` is an
honest complex number, and the branch is required only when theta is wanted as
a real continuous phase counter for Gram points and N(T). Measured agreement
3.4e-31 at dps=30. Defining Z and counting zeros are different requirements,
and only the second needs the branch.

---

## Known gaps

Listed because an undocumented gap becomes an assumption.

1. **The harness has one department, so its generality is untested.** The
   protocol is domain-agnostic by test, but "would work for a chemistry lab"
   is an argument, not a measurement. Until a second department exists, the
   four roles are a generalisation of exactly one case, and the honest reading
   is that `harness/` refactored the zeta instruments rather than that it
   discovered a universal shape.
2. **The dossier probe has one example and no evidence that it helps.** The
   schema can be filled in; that is not the same as being the right schema.
   Nothing has moved an axis by machine, and the Hardy Z example is
   retrospective — nobody was about to define Z as `|zeta(1/2+it)|`. It earns
   its place the first time an obligation fails against a definition somebody
   actually intended to use. `docs/19` SS7 lists what extraction would require.
3. **Expected funnel yield is approximately zero, by design.** Nearly everything
   will return already-known or refuted. The first real run: 26 candidates → 20
   known, 1 trivial, 5 inconclusive, 0 survivors. That is the machine working.
   A conjecture factory that produced discoveries on its first run would be
   broken. The value is the discipline and the record, not the hits.

---

## Next build: the formalization ladder (lean/)

The lab's newest arm, and the current continuation priority (see `HANDOFF.md`
for the checklist). Rung 1 shipped: a Lean 4 + Mathlib project under `lean/`
with the ground-truth facts kernel-checked (ζ(2) = π²/6, ζ(0) = −1/2,
ζ(4) = π⁴/90, no zeros on Re s ≥ 1), zero `sorry`s, ~6 s rebuilds against the
cached Mathlib toolchain.

- **Rung 2 (next):** the κ derivation from `zeta/epstein.py` — the
  self-duality linear solve behind the Davenport–Heilbronn combination,
  formalized. First theorem Mathlib does not have; "derive conventions, never
  remember them" made kernel-checked.
- **Rung 3 (the prize):** the Davenport–Heilbronn theorem — a Dirichlet
  series with functional equation, real coefficients, and an off-line zero
  exists. Puts gate 3 (`docs/09`) into the certified library. Hard part:
  certified interval evaluation of Dirichlet series in Lean; `zeta/rigor.py`
  is the working blueprint.

Why this is in scope: it certifies the literature and the lab's reference
points. It is not an attempt on RH, and the deliberate-non-goal above stands.

### The upstream track: what of this belongs in Mathlib

A rung that only compiles here is worth less than one other people import.
`references/mathlib-open-targets.md` (generated by `scripts/mathlib_gaps.py`)
is the fact half: Mathlib's own `docs/1000.yaml` lists 1179 famous theorems and
**970 carry no `decl:`** — the library's written record of what it wants and
does not have. The judgment half is here.

Verified against Mathlib master and PrimeNumberTheoremAnd (2026-08-06, code
search plus open-PR search):

| target | in Mathlib | claimed elsewhere |
| --- | --- | --- |
| Hardy Z, Riemann–Siegel ϑ | no | no — not in PNT+ either |
| Sturm's theorem (root counting) | no — `1000.yaml` Q1632301 | no |
| Critical line theorem (Hardy 1914) | no — `1000.yaml` Q205966 | no |
| zero counting N(T) | no | **yes** — PNT+ `Backlund/`, `IEANTN/` |
| `riemannZeta_conj` | **yes** — `Harmonic/ZetaAsymp.lean` | — |
| Λ(1−s) = Λ(s) | **yes** — `completedRiemannZeta_one_sub` | — |

Two decisions follow.

- **Sturm's theorem is the contribution target.** It is domain-general — real
  algebraic geometry, decision procedures and interval tactics all consume it,
  none of them care about ζ — and `zeta/li.py` already carries a working exact
  Sturm chain in ℚ[X] to port. Mathlib has no Descartes' rule, no
  Budan–Fourier and no real-root isolation either, so the surrounding shelf is
  bare.
- **Hardy Z stays the lab's own rung, and is not merely vocabulary.** The
  standard route to the Critical line theorem runs through Z, so the rung is
  the on-ramp to Q205966 rather than a detour. Construct it from
  `completedRiemannZeta`, *not* from e^{iϑ}ζ: taking Z(t) = Λ(½+it) divided by
  the real factor π^{−¼}·‖Γ(¼+it/2)‖ makes realness fall out of
  `riemannZeta_conj` plus `completedRiemannZeta_one_sub`, both already in
  Mathlib, and avoids needing a continuous branch of log Γ along the critical
  line — which Mathlib does not have and which is where the textbook
  construction would stall.

**Do not go after N(T).** PNT+ is actively on it via a rectangle argument
principle; duplicating it is the one way this track wastes effort.

Honest risk on both: neither has been scoped in Lean, and Sturm in particular
is a multi-thousand-line development, not a weekend. Sequencing accordingly —
land something small and reviewable before opening a PR that large.

---

## Previous build: moments

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
