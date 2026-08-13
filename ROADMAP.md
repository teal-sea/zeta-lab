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
a department is defined by what can refute its claims.

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
declare at least one reference claim its battery rejects and one it passes,
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
A dossier has none of its own. Refuting the `|zeta(1/2+it)|` candidate is a
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

**What it found on first contact with reality.** A parallel session proved the
Hardy Z properties in Lean while this was being written, and re-reading the
dossier against the new file produced two things nobody had gone looking for.
First, the four-value formal axis could not describe "complete proof, no
`sorry`, no kernel run on record here", so `STATED_UNCHECKED` was added — the
distinction being *who checked*, which is the repo's own "nothing counts until
it compiles" restated. Second, and more useful: Lean proves `hardyZ_is_real`,
`abs_hardyZ_eq_abs_zeta`, `hardyZ_even`, `hardyZ_zero_iff` and
`continuous_hardyZ` — and says nothing about the **sign** of Z, which is the
dossier's only discriminating obligation and the sole property separating Z
from `|zeta(1/2+it)|`. The formalisation is complete about everything except
the thing that makes the object worth defining. Defensible as an ordering
(continuity is the groundwork for an intermediate-value argument), and it was
surfaced by the schema's structure rather than by anyone's memory. Pinned by a
test written to be deleted the moment Lean gains a sign lemma.

**One thing it produced beyond bookkeeping.** Checking the dossier's claim that
the two in-tree definitions of Z agree settled a convention question: the
completed-zeta route needs no branch of log Gamma because `Gamma/|Gamma|` is an
honest complex number, and the branch is required only when theta is wanted as
a real continuous phase counter for Gram points and N(T). Measured agreement
3.4e-31 at dps=30. Defining Z and counting zeros are different requirements,
and only the second needs the branch.

---

## Steering the funnel (decided 2026-08-06)

The observation that forced this section: rediscovering known mathematics
means the generator is *late*, not broken — a lead source whose knowns are
dated theorems is pointed at fertile ground. Three mechanisms, one shipped:

1. **The lateness signal (shipped).** `ontology.metrics.knownness_breakdown`
   splits every generator's `known` verdicts by the matched fact's
   `literature_status` and reports `settled_known_rate` — the share matching
   settled mathematics (theorems, established results, disproofs). It reads
   the ledger's full verdicts, buckets a missing status as `unstated`
   (under-claiming, never inventing), and renders in `render_text`. Steering
   rule: widen generators with high settled shares, starve ones whose rejections
   are definitional. It is a statement about the catalogue's matches, and
   about nothing beyond them.

2. **The review flywheel (protocol, not code).** Every survivor's operator
   literature check must end in one of exactly two places: a new `KnownFact`
   with a citation when the search finds a match (so the funnel rejects the
   observation itself next time), or a closure note in the private ledger
   repo when it does not (the Λ-mass case, 2026-08-06, is the worked
   example). A review that ends anywhere else — a chat transcript, a memory —
   is compute the referee never gets back.

3. **Web-connectedness ranking (next build for the funnel).** Schema 1.1's
   `related_to` edges exist but no generator emits them and no metric reads
   them. The build: generators annotate candidates with `implies` /
   `equivalent_to` edges into the equivalence web (Li/Jensen, moments,
   criteria), and the scorecard ranks surviving leads by connectivity —
   Kadison–Singer fell through its equivalence web, and an isolated lead has
   no web to fall through. Requires whole-ledger edge validation, which the
   schema deliberately left to this layer.

No trained model is needed for any of this: the operator loop plus the
recorded decisions in this file are the adaptive component.

---

## The repository leads with the referee (2026-08-07)

**The decision:** the front door now states the thesis the tree already
implements, instead of presenting the mathematics and leaving the refereeing to
be discovered several sections in.

The realization it encodes: generating a plausible idea is now cheap, so the
scarce resource is no longer ideas but **reliable rejection**. The loop here is
*generate → attack → measure → discard → retain the evidence*, not *generate →
explain convincingly → publish*. What makes that more than a slogan is that
**the rejector is itself under test** — a battery must reject a reference claim
known to be empty *and* pass one known to be sound, lesions measure detector
power rather than assuming it, and the vocabulary is governed too (`certified`
has exactly one owner).

Three changes, all documentation and tests; no mathematics moved:

- `README.md` leads with the laboratory-plus-referee framing and names the
  mathematics **department #1**. The heat-equation chain, the gallery and the
  twelve runnable demos stay exactly where they were.
- A fifth door, `docs/doors/adopt.md`, for the audience that wants the
  refereeing pattern and does not care about ζ. Its first command runs the
  protocol seam tests plus the department conformance suite — the referee
  refereeing itself.
- **Departments keep their own room.** The spine asks one thing (*no department
  without a battery*) and nothing else; a department's doors, reading course
  and gallery are its own business. Stated in `docs/doors/README.md` so it is
  not re-litigated.

### `hunts/` classified as a probe area, and Hunt #2 withdrawn

The same session pulled in `hunts/`, which made the gap concrete: a hunt is an
exploratory attack that may record a claim *before* anything has tried to refute
it. Worth having — but unclassified, it is a directory where a probe can pass
for a result. This follows the `dossier/` precedent above, and for the same
reason: a hunt's rivals are the *zeta* department's rivals, and **a department
whose battery is another department's battery is not a department**.

`hunts/README.md` states the rule (*a hunt is a probe; nothing in `hunts/` is a
result*), lists what a hunt may and may not do, and carries a case log.
`tests/test_hunt_probe_discipline.py` enforces the classification, the reserved
vocabulary, and one measurement.

**Hunt #2's headline was withdrawn on review** — it had reached `HANDOFF.md` as
"successfully verified … definitively placing zeros off the critical line".
Three defects, each checked in-tree rather than argued:

- `zeta/detector.py`'s own docstring names the load-bearing caveat: a
  *missing* on-line zero produces a residue indistinguishable from an off-line
  zero, so the statistic means nothing without a completeness check.
  `online_list_is_complete` is called nowhere in `hunts/`, and the zeros came
  from a `step=0.05` sign-change scan, which skips close pairs.
- The **lesion settles it quantitatively**: ζ — factorization defect
  `2.65e-32`, every zero on the line — given a list with one on-line zero
  removed produces `max|residue| = 1.99`, against `0.0038` for the complete
  list. The hunt's Epstein residues (4.07–4.33) are about twice that. An O(1)
  residue is reproducible at *zero* factorization defect, which is the entire
  claimed signal.
- **The test set was the rival set.** Discriminant −23's principal form
  `(1,1,6)` is a registered rival in `zeta.epstein.battery`, admitted
  *because* it lacks a scalar Euler product. Confirming that restates the
  admission criterion — gate #3, distinguishes nothing.

The recorded data does not show the claimed relationship either: the defect
varies 2.7× against a 6% residue move (`results2.json`), and 67× against 1.36×
with `argmax_c` pinned at `86.0` for all nine rows (`results.json`) — the
scan-window signature `docs/17` §2 says to distrust. No ledger entry. The
generalized residue detector (arbitrary archimedean bracket) is the reusable
part and is retained.

**Why this is recorded rather than quietly fixed.** It is the cleanest in-tree
instance of the failure the whole apparatus exists to prevent, and it happened
*here*, to work that had every instrument available and routed around all of
them. The rule it sharpens: **a probe that bypasses the battery has not
produced a weak result, it has produced no result** — and the place to notice
that is before the claim reaches a status line.

### The certified arm's cross-check was dormant (2026-08-07)

Found while chasing what looked like a hung fast tier. `python-flint` was not
installed and is not something `requirements.txt` used to ask for, so
`zeta/rigor.py` had been running on its mpmath `iv` fallback alone.

Two consequences, and the second is the one that matters:

- **Speed, which is how it was noticed.**
  `test_rigor.py::test_cache_never_replays_a_certificate_for_different_settings`
  took over twenty minutes instead of `0.76 s` — a hang, for practical
  purposes, and one that presents as an infrastructure problem rather than a
  missing dependency. The stack ends in `mpmath/libmpi.py`'s interval trig.
- **The cross-check was not running.** `test_rigor.py` carries five
  `skipif(not HAVE_FLINT)` cases, three of them reasoned *"needs both backends
  installed"*. Those are the Arb-vs-mpmath comparisons — the reason `rigor.py`
  may use the reserved word *certified* is that two independent ball
  implementations agree, and only one was present. The suite reported `5
  skipped` and looked green.

`python-flint>=0.6` is now pinned in `requirements.txt` and the Setup section
of `AGENTS.md` carries a backend check with the explicit warning that **"5
skipped" here means the cross-check did not run**. With both backends live the
fast tier is `1654 passed, 0 skipped` in 5m37s.

**The general lesson, which is this repository's own thesis turned on itself:**
a skipped test is a silent verdict. The apparatus is built so that a claim
cannot promote itself without a referee — and here the referee for the word
*certified* had been switched off by an absent optional dependency, reporting
its own absence only as a skip count nobody reads. A control that can be
disabled by the environment needs to say so where the verdict is read, not in
a summary line. Same failure shape as Hunt #2 above: the instrument was
trusted without checking that it was running.

## Department #2 admitted: curves over F_p (2026-08-07)

The finite-field department is registered, listed in `KNOWN_DEPARTMENTS`, and
under the conformance audit. Its subject is the RH that is a theorem, and the
architectural point is that here every instrument can be **exact**: the rivals
are counterfeit Lefschetz profiles — integer traces with `a² > 4p`, run
through the same fixed-point formula a genuine curve obeys, giving integral
positive counts with exact functional-equation self-duality (`αβ = p`) and
both Frobenius roots off the circle. Hasse's theorem is precisely the
statement that no curve realises them, which is what makes them fair rivals:
the structure alone does not exclude them, only the theorem does. The
calibration pair mirrors department #1's exactly — the functional equation is
rejected (shared with every counterfeit), the Hasse bound distinguishes.

**How it got here is the part worth recording.** The first draft found in the
tree was a sham: its decoys, surrogates and lesions were placeholder objects
with comments naming the conformance test each was written to satisfy
(`return [1, 2, 3]` as a surrogate), and its rivals carried a `virtual_a_p`
payload field — a label a claim could read to tell the target from the rival.
That is a battery that can never fail, hidden one level below where
`validate_battery` can see, and it had already been staged for admission. The
structural audit catches missing instruments, not empty ones; emptiness was
caught here by review. The rebuilt department pins the counter-measures in
`tests/test_harness_finitefield_department.py`: every payload has exactly the
keys `{"p", "counts"}` (no tells), and a counterfeit whose trace sits inside
the Hasse bound is refused by its own constructor.

Three measurements out of the build:

- **Lesion magnitude is quantised by the subject.** The smallest integer
  trace violating Hasse at p = 1009 is |a| = 64, magnitude 0.129 off the
  circle; a smaller lesion needs a fractional trace, which breaks integrality
  of the counts and would be detectable for the wrong reason. Department #1
  plants δ = 0.001; department #2 provably cannot. Detector power below the
  floor is unmeasurable in this domain — a fact about subjects, not about
  either battery.
- **All four instrument runners now have a real client.** The compiler probe
  (git 2041d86) recorded that zeta only ever drives `run_battery`; the
  finite-field tests drive ablation, nulls and power with honest measures —
  including a coarse detector shown to be `blind_to` the floor lesion by name.
- **`AblationVerdict.survives` is the correct aggregate for exactly one of
  the two departments.** Zeta's decoy pair has opposite polarities by design
  (a spectrum must move under prime replacement and must *not* move under
  permutation — the payload is a set of places), so for that battery an
  honest measure scores `survives is False`, and a measure scoring `True` is
  reading a Python list index. The finite-field payload is a sequence indexed
  by r, both decoys must move honest measures, and `survives` means what it
  says. Both polarities are pinned by tests; a draft test asserting zeta
  ablation `survives is True` with a position-reading measure was corrected
  in review. The protocol is unchanged — the aggregate is departmental, and
  reading it without knowing the department's polarity is the mistake.

`zeta.finitefield` moved from department #1's module list to department #2's;
no code moved and no import changed. Door: `docs/doors/finitefield.md`.

## Department #3 admitted: LLVM IR rewrites (2026-08-08)

The compiler candidate (git 2041d86, verdict PROVISIONAL) graduated by
clearing its own §11 checklist; `compiler/FINDINGS.md` §13 is the admission
record. The two blockers, and what cleared them:

- **The poison blindness.** `compiler.semantics` gained a second backend,
  `pymodel.refinement_i8`: a pure-Python poison-aware interpreter of the
  supported IR subset, run exhaustively over the 65536-point domain — over a
  domain that small, enumeration decides what an SMT query would, with
  nothing installed. Its verdicts are refinement **with respect to the
  model** (`EVIDENCE_MODEL_I8` travels with every one), and the hand-written
  model is bounded the way this repo bounds everything, by a second backend:
  at every input where the model claims a defined value, compiled output
  must match at both optimisation levels — pinned for all ten fixtures.
  On the `nsw` lesion the compiled tables agree exactly (rung 1's blindness
  remains pinned) and the model reports 32768 poison violations, zero value
  violations — exactly the declared magnitude 0.5. All four lesions now
  measure at exactly their declared magnitudes; `run_power` with the model
  detector reports full power, and with the concrete detector still reports
  the blindness, because the power *difference* is the measurement of what
  the new rung added.
- **The conformance suite's zeta shapes.** FINDINGS §7's `probe` convention
  was applied as proposed: instruments may declare a representative payload,
  read via `getattr` with the historical values as fallback, and
  `harness/protocol.py` needed no change. The lesion rule strengthened from
  `len(apply(())) > 0` to `apply(probe) != probe`, which catches the
  identity lesion the old rule passed — the change is a strengthening, not
  an accommodation, which is what made it reviewable on its merits.

One deliberate deviation from the probe's own instruction: the test asserting
the concrete detector's blindness said *delete me when a refinement backend
arrives*. It was renamed, not deleted — the new backend does not un-measure
the old one's blind spot, and un-pinning it would let rung 1 verdicts be
read as covering the poison class again.

## Department #4 admitted: croniter — the first foreign-born subject (2026-08-09)

The croniter department is registered, listed, and under the conformance
audit. Its subject is a frozen implementation of union day-of-month/day-of-week
semantics under cron's `#` and `W` special forms, from a codebase this
repository had never touched — vendored and byte-pinned in
`harness/departments/croniter_fixtures/` so the refereed subject cannot
drift. `harness/protocol.py` is untouched, and
`tests/test_harness_croniter_department.py` pins that mechanically (a lexical
scan: the seam knows no cron vocabulary).

What makes this admission different from #2 and #3, and why it bears on
known gap #1: an external referee suite for this subject was first authored
*blind* by a party independent of the implementer and proven against five
planted mutants — five caught, the surgical ones by exactly one aimed check
each. That external suite is not vendored here; the in-repo instruments are
the implementing process's re-expression, admitted only because they
reproduce the independent calibration's verdicts (the same five mutants,
still all rejected). The department carries those mutants as exact source patches: the two
semantic ones as rivals, the other three as lesions whose magnitudes are
measured at import (share of a bounded behavioral fingerprint each patch
changes: 0.05 / 0.35 / 0.05), never asserted. The distinguishing reference
claim is exact agreement with an independent calendar-arithmetic oracle that
never calls the subject; the rejected claim — "accepts the API flag," true of
every rival — pins that an API's presence proves nothing about its
semantics.

One lesson re-learned during the build, recorded because it is the
department's own subject matter: the first draft of the magnitude
measurement iterated `croniter_range` until its stop date — and the
re-emission lesion makes iteration jump backward, so that measurement hung
exactly the way the calibration run had already demonstrated. The
measurement is now bounded (fixed pulls, never iterate-until-done) and a
test pins that the lesion is *recorded* rather than waited for. An
instrument that can hang on the violation it exists to measure is an
instrument with an unmeasured blind spot.

Honest scope, stated on the door: this measures the *ingestion* half of
known gap #1 — a foreign subject, an unchanged protocol, independently
authored battery content. It does not measure adoption by an outside team;
every step was still orchestrated from this repository's own process.

## Field report #1: the referee discipline on a production business system (2026-08-09)

The croniter department measured foreign-domain *ingestion*. The next
question — does the discipline survive contact with a production system
whose subject is money rather than mathematics — is now running as a field
deployment: a calibrated checker (`booking-check`) for an AI booking agent's
proposed reservations, built in a separate repository by a separate session
against this lab's published method (battery calibrated in both directions,
planted failure classes, integrity labels on every verdict per docs/20,
read-only against production throughout). Same operator as this lab, so the
outside-*team* half of known gap #1 stays open; the new axes this deployment
does test are domain (business operations, not code or mathematics) and
stakes (revenue).

Everything below is **the deployment session's report, relayed — not
verified by this repository**, and is recorded at that strength:

- Battery calibration reported: 8/8 planted failure classes caught
  (AM/PM flip, cross-market timezone shift, wrong airport, off-rate price,
  passenger-count slip, double-booked vehicle, authorization-described-as-
  captured, claimed-sent-without-provider-receipt). False alarms reported
  driven 57 → ~1 per 100 clean records by three *named* root causes
  (round-trips misread, a deposit cap misapplied to legacy records, two
  same-named columns with different meanings) — root-cause repair, not
  sensitivity reduction.
- Census findings reported before any code ran, each the shape this lab
  predicted: rates overwritten in place with no history (past prices not
  re-derivable — the price probe carries two integrity labels, structural
  over history, full over live data); the written rate-algorithm document
  twenty minor versions behind the executable (doc is not the record); 42 %
  of "message sent" rows carrying only self-written receipts (the sender
  vouching for itself); a conversation-to-booking join column populated on
  0 of 3,566 rows; voice claims-checking scoped OUT of v1 because the only
  available join is a 53 % guess — refusing to build a checker on a
  foundation that violates its own standard.
- First live catches reported: three reservations with an authorization
  recorded as "deposit paid" where no capture exists — the exact
  vocabulary-collapse class this lab plants as a lesion. **Unverified**:
  the operator's stated posture is disbelief pending his own inspection of
  the payment records, which is the correct posture and is recorded as part
  of the result.

What this bears on: the hollow-verification finding (the resumption
benchmark's surviving measurement) predicted that self-vouching records and
uncalibrated checks accumulate silently in real systems; the census found
both within hours, in the first production system examined. What it does
not bear on: commercial validation, outside-team transfer, or any claim
that the catches are real before the operator verifies them. Further field
reports will be appended as the deployment's shadow phase produces
falsifiable numbers (catch rate, false-alarm rate, operator-confirmed
findings).

## Field report #2: the deployment's build phase closed with a measured spec sheet (2026-08-09)

Still the deployment session's report, relayed and unverified here; recorded
because three of its results are general lessons, not local ones.

- **The spec sheet exists and is machine-regenerated** (a script rebuilds it
  from the measured calibration record, so it cannot go stale by hand — the
  staleness lesson institutionalized at birth). Over 98 real records:
  **7 of 8 planted failure classes caught** above a declared 50% reliability
  floor, each with its smallest-caught magnitude stated (12 hours, $30.96,
  1 airport, 6 passengers, 1 vehicle, $120, 1 receipt).
- **The eighth class is not missed — it is undetectable, and the report says
  so by name.** A whole-booking timezone shift leaves the record internally
  consistent; wrongness lives only against what the customer *asked for*,
  which lives in the conversation, which has no link to the booking (the
  dead join column from the census). The general lesson, worth keeping:
  **record-internal checking can only catch contradictions; a coherent-but-
  wrong record needs a linked origin artifact, and if the link does not
  exist the class is structurally unverifiable** — declare it, never
  average it away. This is the field version of the missing-vs-empty
  distinction.
- **The false-alarm number was interrogated instead of celebrated:** 16.3%
  overall, but the dominant probe's 13 "false alarms" were hand-checked and
  five of five examined turned out to be one real data defect and four
  undocumented discounts — so the truthful name is *disagreement rate*, and
  the alarms were findings. A checker's false alarms are themselves claims
  requiring verification, in both directions.
- **The deployment corrected its own earlier money claim** — an initial
  "$460 across two bookings" (relayed into field report #1 as unverified)
  was wrong, from a partial query; the measured figure is $264 on one
  booking, plus three stale authorizations wanting voiding. The correction
  came from measuring rather than reasoning, stated as such. Report #1's
  numbers are superseded accordingly; operator verification of the payment
  records remains pending and remains the correct posture.
- Discipline audit as reported: zero write statements, zero mutating calls,
  zero payment-API calls in the new code; migration written, not applied;
  nothing scheduled; verdicts re-derived live, with the calibration record
  the only thing read from disk — "a probe must not be allowed to vouch for
  itself."

Next falsifiable numbers arrive from the shadow phase (live catch rate,
disagreement rate over time, operator-confirmed findings).

## The resumption benchmark ran, and the typed machinery did not earn its keep (2026-08-09)

`docs/19` §6 named the only honest path by which `dossier/` could become a
department: a scoreable resumption task in which the typed representation
beats a flat-notes rival. That benchmark ran, in a private fork: three
snapshots of one frozen HEAD carrying the **same underlying facts** in three
representations (flat notes / governance prose / prose plus the dossier
machinery), ten planted failures drawn from this repository's own incident
history, 18 blinded cold-agent runs across two model families, with the
answer key, scoring boundaries and outcome rules frozen before any data
existed. Scored blind by an independent agent that authored nothing.

- **Outcome under the preregistered rules: ambiguous, with a benchmark
  defect.** One model family fell below the planted-control competence floor;
  its cells are void and support no conclusion in either direction.
- **In the family that counted, the typed condition did not beat the prose
  condition**, and flat notes were not measurably worse on the discriminating
  set — which itself sat partly at ceiling, a design defect recorded for any
  repeat. "Did not demonstrate" — not "disproved"; the distinction is the
  usual one and it is load-bearing.
- **The finding that survives:** agents caught *recorded contradictions* — a
  withdrawn claim restored to a handoff, scope language drifting into
  overclaim, a formal status contradicted by the file it cites — nearly
  everywhere, in every representation, with zero unwarranted promotions and
  zero re-litigations of settled decisions across all 18 runs. The same
  agents reliably missed *hollow verification*: a structurally admissible
  battery whose instruments are placeholders, a battery PASS read as
  substantive truth, an instrument whose stated precondition never ran. The
  distinction this tree keeps drawing — the structural audit catches
  *missing* instruments, only review catches *empty* ones — reproduced under
  controlled conditions, in every representation tested.

Consequence: the dossier department admission path stays closed (the §6 bar
was not met), the probe classification stands, and any revival must first
repair the benchmark (the competence floor, the ceiling lesions) and then
beat disciplined prose from scratch — the burden does not reset.

## The verification-integrity build: the referee, refereed (2026-08-09)

The layer two incidents had already specified — the 431cc74 sham (structurally
complete, hollow, human-caught) and the resumption benchmark's finding that
agents reliably miss hollow verification — built as architecture. Full record
in `docs/20-verification-integrity.md`; the short version:

- **Claim outcome and battery integrity are now different axes**, and
  `harness/integrity.py` refuses to state one without the other: sixteen
  named checks, five crisp grades (no scalar), and a `ClaimReport` on which
  a green claim from a hollow battery renders as dangerous.
- **The contract grew what the incidents demanded**: `NamedDetector` enters
  admission (FINDINGS §8's gap — lesions without a staked detector leave power
  unmeasured), `DetectorVerdict` measures specificity (a constant-True detector
  previously earned a perfect PowerVerdict), and departments declare `scope`
  and `provenance` (REDTEAM W2's contamination as a declarable field).
- **Department #5 is the referee itself**: batteries as subjects, the
  reconstructed 431cc74 sham as the held-out rival, sham mutations as
  lesions with measured magnitudes, the audit as the detector. Its rejected
  reference claim — `validates_structurally`, true of the specimen and of
  every sham — makes "structural completeness is not verification" a
  re-derived measurement. The audit's two mechanical blind spots
  (value-encoded label leaks, co-designed calibration) are pinned AS blind,
  poison-lesion style, with the countermeasure (independent authorship,
  attested in provenance) named on every report. Recursion bottoms out in a
  documented kernel (docs/doors/referee.md): deterministic re-execution,
  the conformance suite as a second expression of the same requirements,
  one held-out mutant, human-attested provenance. No meta-meta-referee.
- **Department #6 (stateval) was chosen to attack the single-run
  assumption** all earlier departments share, and it broke two shared-layer
  things, both fixed as strengthenings: `run_null_band` (a distributional
  null cannot be judged by one draw and a distance — the W3/W4 failure,
  now an exceedance count over a stated number of draws) and
  `payloads_same` (the audit compared mapping payloads by keys alone and
  raised on arrays — the probe-convention lesson one layer down). Its
  preserved false start is pinned: two drafts of the seed-hacked rival
  acquired *genuine* skill, caught by calibration re-derivation before
  shipping; a rival lacks the property by construction or it is not a rival.
- `python -m harness.demo` runs every department and then the turn;
  `python -m harness.new_department` scaffolds questions, not placeholder
  instruments, because a scaffold that generated runnable placeholders
  would be a sham-battery generator.

## Forward-deployed verification: the grade made enforcing (2026-08-09)

`docs/21-forward-deployed-verification.md` is the record, and the verdict is
**KEEP AS PROBE** — not a capability. The criteria and the prose rival were
committed before any implementation existed (`bf8f6dc`, `c08296d`), which is
the only reason the scoring below is worth reading.

The integrity layer above measures a battery and *renders a banner*
(`ClaimReport.dangerous`); nothing refuses a crossing, and contamination is
whatever the provenance record declares. `harness/promotion.py` and
`harness/preregistration.py` close exactly those two gaps and nothing wider.

- **What was earned.** A preregistration records the digests of evidence that
  already existed when its criteria were frozen, so contamination is a set
  membership and criteria drift a digest inequality — recomputed from
  artifacts, never read off a flag. Two cases diverge from `NaiveGate` (the
  mandatory ~15-line null control that reads declarations and recomputes
  nothing): a report declaring itself clean while its artifacts disagree, and
  a **silently dropped hardest lesion**, where nothing lies at all — the audit
  is honest, still grades `CALIBRATED`, and simply cannot know what was
  removed. Its blindness pin still passes unchanged; a prior record supplies
  what one audit of one battery at one moment cannot have. That moves
  `dropped-hardest-lesion`'s countermeasure from a convention ("pin the lesion
  set in tests") to a mechanism.
- **What failed, recorded rather than reframed.** The mirror condition is
  unreachable — any declared contamination grades the battery `CONTAMINATED`,
  so both gates block together, and on every constructible case this gate is
  only ever *stricter-or-equal* to the naive one. The blind-detector axis is no
  divergence at all: `detector-specificity` already had it, contradicting the
  referee's pre-registered prediction that blindness would be the informative
  case. Against a *legible* criteria record an isolated human reviewer catches
  the dropped lesion by eye, correctly and confidently; the gate wins only the
  cell where the criteria are a digest rather than an enumeration. The
  contribution is **decidability from a compact artifact**, not detection of
  something a person could never see.
- **The worst result, pinned as a test.** The gate **inherits every blind spot
  of the audit beneath it**. It promotes a held-out hollow battery's
  astrological claim with an empty reason list, because `decide` requires the
  grade to be `CALIBRATED` and cannot re-derive whether that grade was earned.
  Forward-deployed verification does not make a hollow referee safe; it makes
  an *unrecorded change* to a referee visible.
- **A default-open bug was found inside the gate**, by review rather than by
  its author: `_check_independence` coerced party identifiers with `str()`, so
  a caller naming no parties read as two independent ones. Fixed, kept as a
  regression pin. `docs/20` §6.4 predicted a further referee layer would move
  the trust boundary rather than remove it; that prediction stands, and the
  honest gain is only that a lie must now be a false digest, which anyone
  holding the artifacts can check, instead of a false boolean.

## The audit was hollowed on the first attempt (2026-08-09)

`docs/20` §8's second experiment — an independent party authoring a hollow
battery **without seeing `SHAM_MODES`** — was run, and is the most damaging
result of the session. Given only `harness/protocol.py` and `harness/README.md`,
the party reached `CALIBRATED` **on the first attempt with zero adaptation
iterations**, passing all 19 conformance tests. Its rivals were distant enough
that `anything AND a target-only property` distinguished, so an explicitly
astrological claim rendered as `distinguishes` under a `CALIBRATED` banner; its
detector was its claim negated, identical on 29/29 payloads while passing both
power and specificity. Separately, a check returning `UNKNOWN` does not prevent
the top grade, so `payload-symmetry` is sidestepped for free by using callable
payloads.

Under §8's own scoring rule these are holes, and `SHAM_MODES` now names two
more — `distant-rivals` and `detector-is-the-claim`, both `caught_by=None`.
**The audit's real constraining power is over *mechanical* emptiness.** It has
no purchase on the two choices that decide whether a battery can reject anything:
how near the rivals are, and whether the detector is independent of the claim.
Both are the author's to pick, and every layer built on the grade — the
promotion gate included — inherits that.

## Closing two blind spots: what shipped and what did not (2026-08-10)

`docs/23-rival-distance-and-detector-independence.md` is the record. Criteria,
threshold and six predictions were committed at `e7d52b6` before a line of the
implementation existed; three predictions failed and are recorded as failed.
The exercise above was repeated at n=6 instead of n=1, with four honest
controls, and the results are worse for the audit than the first run was.

- **The audit does not constrain an adversarial author, and now we know the
  rate.** Six independent parties given only the public contract reached
  `CALIBRATED` with batteries that measure nothing — **six of six**, each
  certifying a transparently absurd claim (a waxing moon over a weather
  station, Mercury retrograde over a shipping manifest) as `distinguishes`.
  Five of the six did it while the new checks were already visible in their
  runner output. The audit as it now stands catches two of the six.
- **The four survivors are one mode, and it is argued unreachable.** Rivals
  matched in structure and disjoint in *value*: no single field is the tell,
  the joint value vector is the label, so any predicate keyed to a target
  value is target-exclusive. Now `structure-matched-value-disjoint-rivals`
  with `caught_by=None`. The obvious fix inverts and the inversion is
  measured: a value-comparison family scores `zeta`, `compiler`, `croniter`
  and `referee` *more* separated than the sham, because ζ and
  Davenport–Heilbronn also agree on no numeric value. Which differences are
  load-bearing is the domain knowledge the seam forbids.
- **`rival-separator-abundance` ships and acts on nothing.** It measures the
  distance (real departments 0.00–0.05, a planted gross-distance corruption
  0.24–0.50) and the threshold frozen before the calibration was read, 0.5,
  sits above the whole range. Not retuned here: a cut chosen after reading its
  own calibration has no falsification weight, and the held-out set is spent.
  Pinned as a blind spot with its numbers rather than quietly adjusted.
- **`detector-claim-agreement` ships and earns it.** It catches its planted
  mutation in isolation, catches one blind-authored hollow battery nothing
  else catches, and catches **`docs/21`'s hollow battery** — whose promotion
  was that document's worst recorded result. (That one is a reconstruction
  authored by this tree's own process, so its chronology is clean and its
  authorship is not; `docs/23` §8.5 says so.) That specific
  promotion no longer happens; `docs/21`'s general finding is untouched and
  its pin now runs against a specimen whose detector is independent, so
  repairing one instance was not allowed to make the gate look safe.
- **The cost of that check: `compiler` and `referee` now grade
  `DETECTOR_INADEQUATE`.** Both declare a detector that is a reference claim
  negated, and in both cases it is a *decision procedure* rather than a
  co-designed detector. The mode has two conjuncts and only the first is
  mechanically visible. Neither department is exempted and the check is not
  weakened: the conformance cases xfail with the reason, and
  `test_the_referee_department_survives_its_own_audit` was renamed to
  `..._does_not_survive_its_own_audit` and asserts the failure. **The referee
  department fails its own audit.** Each department owes an answer; that is
  the next pre-registered change, not this one.
- **The most actionable defect was found by the honest controls, and was not
  predicted.** `decoys-move-their-probe` and `lesions-plant-something` poked
  instruments with department #1's shapes whenever they declared no `probe` —
  an attribute declared nowhere in `harness/protocol.py` and nowhere in
  `harness/README.md`. Two of four honest parties were graded `HOLLOW` for
  writing decoys and lesions faithful to their own payloads; the two that
  passed did so with shape-general fallbacks, which is the same workaround the
  hollow party used to defeat the audit. **The audit was rewarding
  reverse-engineering and punishing fidelity, in both arms.** An instrument
  now has to move one of several candidate probes, inert instruments are still
  caught, and 4 of 4 honest parties now grade `CALIBRATED`. The convention is
  documented in both places it should have been.
- **`UNKNOWN` no longer walks past `CALIBRATED`.** Every hollow-class check
  caps the grade when undecided, matching the numeric arm's rule. Enforcing it
  required making `payload-symmetry` decidable off mappings, which surfaced
  that `croniter` — a department authored outside this tree — hands out bare
  functions as payloads: the "callable payloads sidestep" was never only a
  sham author's trick, and three real departments had been going unmeasured.
- **One new mode, one new check.** party06 reached `CALIBRATED` with a payload
  whose `keys()` is honest and whose `__missing__` answers undeclared names
  with a sentinel equal to anything. `undeclared-field-symmetry` catches it.
  The check was built from that battery, so that battery is not an independent
  test of it, and the catalog says so.
- **A method failure of the exercise itself, recorded in `docs/23` §8.0.** The
  parties ran against the live working tree while the checks were landing in
  it, so §5's claim that blindness was "guaranteed by chronology" is false as
  written. The contamination runs against the parties, so the hollowing rate is
  if anything understated — but check B ends up with no clean blind test and
  check A with one. The frozen corpus and its manifest are in
  `harness/blind_authoring_2026_08_09/`; the set is spent, and a repeat needs
  new parties and a pinned harness.

Net: 16 named checks → 19, `SHAM_MODES` 12 → 15, blind spots 4 → 6, three
previously-uncatchable hollow batteries now caught, four still not.
`ROADMAP`'s thesis from the first hollowing survives unchanged — the audit's
real constraining power is over *mechanical* emptiness — and the choice that
decides whether a battery can reject anything is still the author's.

## The outside memos, triaged (2026-08-11)

Two outside recommendation documents arrived and are landed in
`docs/reviews/` (the directory's contract is in its README: memos propose,
the tree decides, nothing there is a result). One is a strategy memo — evolve
the lab into a research operating system around the harness, under the rule
**"no agent without an oracle"** — and one is a 16-programme research
portfolio with an allocation table for ~30 agents. This section is the
decision: what was adopted, what was already running, what is queued,
deferred, or rejected, and why.

Three constraints were applied before any triage:

1. **Two threads were live when the memos arrived** — the frontier-math
   configuration-realizability campaign (already at Level 7, past the
   portfolio's Level-6 framing) and the Jensen heat-clock hunt. Live threads
   are not reallocated by a memo; they run to their own kill conditions.
2. **Standing decisions stand unless a memo brings new evidence.** Where a
   recommendation restates something this file already decided (Sturm as the
   Mathlib target, no N(T), rung 3 needs a headroom re-plan before compute),
   the memo is agreement, not input.
3. **The ~30-agent table is read as a priority ordering, not a headcount.**
   Real concurrency here is a handful of sessions (2 live threads + 1–2
   interactive), not 30; the portfolio's *ordering* survives that reduction,
   its team sizes do not.

**Adopted — the next three infrastructure builds, in order.**

1. **Verifier-independence measurement** (portfolio §13; strategy memo
   integration #3). The one recommendation both memos make independently and
   that the tree's own newest evidence demands: the director run (`docs/25`)
   found `rigor.py` returning a wrong `proven_sign` on *both* backends
   because the fault sat in shared input parsing — exactly the memo's "two
   implementations sharing a faulty conversion layer are not independent."
   The shape: extend the ancestry discipline `harness/provenance.py` already
   applies to batteries so a cross-check can state its **independence
   radius** — the earliest layer at which two verification paths genuinely
   diverge. First subject: `rigor.py`'s own two-backend paths, whose shared
   layers (`_exact`, contour policy, grid policy, the S(T)/N(T) interval
   summation) are already enumerated in `HANDOFF.md`.
2. **The guard offensive** (portfolio §14). Same evidence base: three of the
   director run's six defects were guards that could not do their job, and
   `docs/22` measured detector strength for departments but not for the
   repo's ad-hoc guards. Per guard: name the intended lesion, build the
   smallest mutant exhibiting it, confirm the guard fires, map the nearby
   lesions it misses, record its true scope. This is `SHAM_MODES` discipline
   applied outside the harness. Destroyer work only — no feature development
   in the same pass.
3. **HuntSpec, on probation** (strategy memo primitive #1). A
   machine-readable contract block inside each new hunt's `MISSION.md` —
   question, current frontier, known dead routes, required oracles, kill
   conditions, agents-may / agents-may-not — plus a validating test. Adopted
   as an *experiment* under the same rule as `dossier/`: the resumption
   benchmark (2026-08-09) showed typed machinery does not automatically earn
   its keep, so no new package and no orchestration until a kill condition
   fires mechanically or an oracle requirement blocks an ungrounded status
   claim at least once. Live hunts are not retrofitted mid-flight.

**Already running — the memos agree with the tree; no allocation change.**

- The portfolio's flagship (configuration realizability, §1) *is* live
  thread 1. Its subteam structure (configuration adversary, independent
  theorem reconstruction, exact certification) matches how the frontier-math
  campaign already operates after the transpose kill.
- The heat-flow lane (§10) is live thread 2's neighborhood.
- The ξ″ bridge past 0.51 (§3) is main's four newest commits. The memo's
  method — a complete exponent budget per α, then classify the *first*
  inequality that fails at 0.6, 0.75, 0.9, 1 − ε — is recorded here as the
  continuation prompt for whoever resumes that lane.
- Kernel-checked Davenport–Heilbronn (§7) is the standing next-build below.
  The memo's one concrete technical idea — replace rectangular enclosures
  for m^{−s} with a polar or mean-value representation to cut dependency
  inflation — is exactly a candidate for the headroom re-plan that rung 3 is
  waiting on, and is recorded there.
- Mathlib upstreaming (§8) restates the decisions already in "The upstream
  track" below: Sturm is the contribution target, Hardy Z is the lab's rung,
  N(T) stays untouched.

**Queued — next new mathematics lanes, opened only as live threads finish,
each behind a HuntSpec.**

- **General higher-ξ hierarchy** (portfolio §2) is first in the queue: it
  grows directly out of the landed Bian/URMS2 work, and the portfolio's
  framing — treat repaired ξ″ as the k = 2 instance of R_k = ξ⁽ᵏ⁾/ξ⁽ᵏ⁺¹⁾ with
  independent Bell-polynomial, Dirichlet-convolution, and generating-function
  constructions — is the right next question. Precondition: the four
  unmerged `agent/*` ξ branches land or close first; opening a new ξ lane
  over unlanded ξ branches invites exactly the collision `AGENTS.md` warns
  about.
- CUE F_k theorem (§4), the local process of derivative zeros (§5), and the
  identification of corrected F₂ (§6) queue behind the hierarchy — same
  family, and §6's own rule (PSLQ may discover, only proof promotes) is
  house style already.
- The local-to-global positivity moonshot (§9) stays alive at most as one
  long-horizon lane. `docs/24` is its entry ledger; the mandatory-adversary
  requirement (structurally exclude Davenport–Heilbronn and Epstein rivals)
  is gate #3 and `zeta.epstein.battery`, already standing.
- The certified adversarial Weil explorer (§12) queues behind adopted item 1
  — its "third implementation sharing no upstream transformation" *is* an
  independence-radius requirement, and `rigor.enclose_weil_functional`'s
  known gap (no `iv` quadrature, so no two-backend cross-check there) is the
  natural first work item when it opens.

**Deferred — right idea, wrong time.**

- Literature scout on `ontology/knownness.py` (strategy memo #1): deferred
  behind the verification builds, but its contract is adopted now — output
  is databases searched, sources inspected, candidate matches, and "no
  matching result located"; never the word NOVEL, because failure to find
  prior art is not proof of novelty.
- Standing (continuous) adversarial review: the practice exists by hand —
  `REDTEAM.md`, the director run — and becomes standing only when durable
  orchestration exists to stand on.
- Orchestration, the research UI, the attention queue, start/pause controls:
  the strategy memo's own build order puts these at positions 6–9 of 11, and
  `meta/`'s rule applies — measure the loop before automating it. The memo's
  constraint is adopted in advance: workflow state may live in an
  orchestration layer, evidence may not; the canonical record stays in tree
  artifacts and git history.
- The equivalence-web scheduler (§16): needs the dependency graph as a data
  model first; nothing exists to schedule against yet.
- The external-referee experiment (§15): already recorded in `docs/20` §8 as
  the experiment most likely to hurt; it needs an actual outside party, which
  is not something a session allocates.

**Rejected.**

- Continuous, indiscriminate funnel generation — rejected by both memos and
  already rejected by this file (known gap #3: expected yield ≈ 0 is the
  machine working).
- Any reading of the memos as bending the honest-scope rule. The portfolio
  speaks of "a genuinely new route to RH"; nothing adopted here is an attempt
  on RH, nothing computed here is evidence for it, and the sanctioned framing
  in `AGENTS.md` stands unchanged.

**Adopted as standing practice, now written down.**

- **Constructor / independent reconstructor / destroyer are separate roles**
  (portfolio's organizational rule). This is how the frontier-math kill and
  the director run actually worked; for major claims the destroyer works
  blind first — hostile examples before the constructor's reasoning.
- **The do-not-fund list** (portfolio's final section) is adopted wholesale.
  Every entry on it matches a kill already recorded in `HANDOFF.md` or this
  file — the memo's contribution is the consolidated form, and the list is
  the standing answer to "why not just re-run X with bigger parameters."
- **The strategy memo's charter** names what the lab already practices and
  is adopted as the phase framing: agents produce artifacts for
  verification, not verdicts; model agreement never substitutes for
  independent evidence; the headline question is *what do we know now that
  we did not know before, and why are we entitled to believe it.* The three
  adopted builds above are its first enforcement mechanisms.

### The AI-implementation half (2026-08-11, same day)

The first pass above triaged the mathematics and buried the automation in one
deferred bullet. That was a gap: the strategy memo's proof-agent adapter is
*not* orchestration, and the external prover/discovery ecosystem the lab sits
next to had never been assessed in this tree (zero mentions before this
section). Assessed 2026-08-11 against live sources, not memory:

- **Aristotle (Harmonic)** is a working public API: key from
  aristotle.harmonic.fun, Python SDK `aristotlelib` on PyPI (latest release
  June 2026), autonomously produces multi-thousand-line Lean 4 proofs, IMO
  2025 gold equivalent. A published case study (arXiv 2605.20120, the
  Grasshopper problem) measured the shape of its competence: it proved the
  four local helper lemmas and left the global counting argument as a
  `sorry`, in a run of roughly eight hours — and its artifacts require
  per-declaration inspection because compilation alone does not exclude
  `sorry`s. That last finding is this repo's existing rule, discovered
  independently by an outside team.
- **AlphaProof Nexus (DeepMind)** is closed — no API, no integration
  possible. Its *results corpus* is public (github.com/google-deepmind/
  alphaproof-nexus-results): kernel-checked Lean proofs of 9 previously open
  Erdős problems and 44 OEIS conjectures (May 2026 paper). A corpus, not a
  service.
- **AlphaEvolve (DeepMind)** is closed, but the pattern — an LLM mutates
  code, a non-model evaluator scores it, evolution keeps what scores — has
  open implementations: OpenEvolve (PyPI), CodeEvolve (arXiv 2510.14150,
  matches or beats AlphaEvolve on 5 of 9 of its own benchmark problems),
  ShinkaEvolve. The pattern is "no agent without an oracle" in loop form.

Three further adoptions follow, numbered continuing the list above:

4. **The proof-agent adapter, with Aristotle as first backend.** Carved out
   of the deferred-orchestration bucket because it is the one integration
   where the model cannot persuade the verifier: the contract is generated
   Lean → this repo's `lake build` → kernel → zero `sorry`s, and nothing
   counts until *our* build says so — server-side verification claims are
   input, not evidence. First targets are bounded lemmas on the Mathlib
   upstream track (the Sturm chain has many), **not** rung 3, whose
   remaining gap is a computation, not a lemma. The case study's economics
   apply: hours per attempt, so submissions batch overnight and each carries
   a precise standalone statement (local lemmas, never "the theorem").
5. **Evolutionary search as a hunt instrument** (OpenEvolve/CodeEvolve
   class, or a hand-rolled loop — the pattern matters, not the framework).
   Admissible only behind a HuntSpec whose `required_oracles` name an exact
   non-model evaluator, which makes HuntSpec (adopted build 3) its
   prerequisite. First natural clients, when their lanes open: hostile
   configuration generation for the realizability programme (score = exact
   violation margin of a candidate inequality) and extremal test-function
   search for the Weil explorer (score = a certified enclosure from
   `rigor.enclose_weil_functional`). Search proposes; only the oracle
   scores.
6. **The AlphaProof Nexus corpus as a prior-art surface.** When the
   literature scout builds (still deferred), that corpus joins its sources:
   kernel-checked proofs to collide claims against are primary sources in
   exactly the sense the scout's contract demands.

And the automation that already exists is named here so it stops being
invisible: the nightly rig (`automation/` in the working checkout, untracked
— mission, journal, arm/disarm switch) has run zero nights. It *is* the
strategy memo's build-order item 10, "run a highly targeted autonomous
frontier hunt," already built and waiting on the operator's switch. Two
consequences recorded: its `mission.md` should carry a HuntSpec block once
that primitive exists, so the nightly agent inherits kill conditions rather
than improvising them; and proof-adapter work cannot ride in a nightly
mission on a machine with no Lean toolchain, because the zero-`sorry` check
must run locally.

**Landed, same day.** Adopted builds 1–4 shipped within hours of the
decision: `harness/independence.py` with the rigor cross-check as worked
subject, `harness/guards.py` with a five-record ledger (three demonstrated
by live mutants, two honestly undemonstrated), `hunts/HUNTSPEC.md` with its
validator, and `lean/proof_adapter.py` exercised once end to end against
the real kernel. `docs/26-the-adopted-builds.md` is the record, including
each piece's honest edge and the alpha-ecosystem inventory
(`external/`, `.venv-tools` — machine state, not repository state).

## Known gaps

Listed because an undocumented gap becomes an assumption.

0. **The guards are the frontier, and two of them did not fire (2026-08-11).**
   The director run (`docs/25`) found six defects in recorded claims; three were
   controls that could not do their job — a completeness check whose "independent"
   reference was the same technique on a coarser grid, a truncation guard that
   encoded "cannot decide" as the favourable verdict, and a scan column that was
   structurally incapable of reading False. A fourth was worse: `zeta/rigor.py`
   could return a **wrong** `proven_sign`, and the two-backend cross-check was
   blind to it because the fault was in a shared input rather than in either
   implementation. Standing consequences, recorded so they are not re-derived:
   a cross-check bounds only what is actually duplicated; and a repetition
   across instruments is evidence about the instruments before it is evidence
   about the subject. The `ROADMAP.md` call that `hunts/local_positivity/`
   asked for is answered there: coefficient-side blindness does **not** become
   a standing constraint on the programme — the universal is false, and
   `criteria.py` face 1 is the in-tree counterexample.

1. **The harness has six departments, and the foreign-ingestion half of
   this gap is now measured.** The protocol survived a decidable-property
   subject (finite fields), a foreign-vocabulary subject (programs), and —
   with department #4 — a subject born entirely outside this tree, with
   battery content authored by an independent party, all without a line of
   `protocol.py` changing. It then changed, once, deliberately: the
   2026-08-09 integrity build added detectors/scope/provenance to the
   contract and `run_null_band`, on the evidence of FINDINGS §8, REDTEAM
   W2 and department #6's distributional null — strengthenings, not
   accommodations, each traceable to a recorded incident. The shared audit
   has now needed exactly two generalisations (the `probe` convention;
   `payloads_same`), and both were the same mistake — payload-shape
   guessing — which is worth treating as a standing prediction about where
   the next false-generic will be found. What remains untested is the
   other half: adoption by an **outside team** — every department was
   still orchestrated by this repository's own process, so "an outsider
   could build a non-sham battery from the docs alone" remains an
   argument, not a measurement (`docs/20` §8 lists this as the experiment
   most likely to hurt). The compiler department's rung 3 (Alive2, LLVM's
   own semantics) also remains absent — its model backend is hand-written
   and its authority stops at the cross-check against compiled output.
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
4. **The certified Weil arm is flint-only and pair-limited.**
   `rigor.enclose_weil_functional` (see "Built: certified Weil positivity"
   below) encloses W(h) rigorously, but only for pairs from
   `rigor.certified_gaussian_pair` / `certified_fejer_pair` /
   `certified_autocorrelation_pair` — the certified siblings of all three
   positive-type families in `zeta.weil` — and only on the Arb backend:
   mpmath's `iv` context has no certified quadrature, so the `mpmath.iv`
   path raises and the two-backend cross-check — the habit that entitles
   the rest of `rigor.py` to the word certified — cannot run there. The
   returned dict states this under `two_backend_cross_check` instead of
   leaving the field silently absent. User-supplied ball-valued pairs are
   refused rather than half-trusted (their tail bounds cannot be audited);
   an interval-Riemann-sum `iv` arch term (wide but honest, enough to make
   the cross-check run) is the natural extension, not scheduled.

---

## Built: certified Weil positivity (`rigor.enclose_weil_functional`)

Formerly the one place where the laboratory measured something the certified
arm could not reach; the placeholder documented here as "not scheduled" is now
implemented. W(h) = pole + archimedean + prime, every step carrying a ball and
every truncation folded in as an explicit error interval, so the returned
enclosure is *true for any* `n_max` and `R` — larger values only tighten it.

- **The blocker fell as predicted**: the archimedean term is Arb's
  `acb_calc_integrate` over the *analytic* integrand h(z)·(ψ(¼+iz/2) − log π)
  — never Re ψ, which is not analytic — with a rigorous tail from the lemma
  |Re ψ(¼+ir/2) − log π| ≤ log(r+2) + 8 (r ≥ 6), derived in the docstring
  from the ψ partial-fraction series and spot-checked in ball arithmetic by
  the tests.
- **Prime tails**: Fejér is exactly finite (cutoff ⌊e^{2b}⌋ proven complete
  by ball comparison); Gaussian is bounded by partial summation against
  Rosser–Schoenfeld ψ(x) < 1.03883x plus an exact erfc identity, one-sided
  because the discarded terms only lower W.
- **The headline number**: the near-tight Gaussian a = 0.2 member — W(h) ≈
  8.86e-18 emerging from pieces of size ~2, eighteen digits of cancellation —
  comes back **certified positive**, enclosure width ~1e-51 at 256 bits.
  Honest scope: finitely many certified instances of W(h) ≥ 0 are not
  evidence for RH (docs/08); what they are is positivity statements that no
  longer rest on floating-point luck. A certified *negative* value would
  disprove RH, so per the house rule the correct first inference from one is
  a bug.
- The safe failure mode holds throughout: an enclosure too wide to decide
  returns `sign: 0` and stays `certified: True` (a wide truth is still a
  truth); every unclosable step lands in `uncertified_steps`; the residual
  mathematical inputs (Rosser–Schoenfeld, the tail lemma, the classical pair
  facts) are named in `assumptions` rather than implied.

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
  exists. Puts gate 3 (`docs/09`) into the certified library. 
  **Status**: Phase A (Structural) is complete with rigorous definitions and theorem statement in `DavenportHeilbronn.lean`; the analytic half and the minimum-modulus reduction are kernel-checked (`DHAnalytic.lean`, `DHZeroCriterion.lean`), leaving exactly two interval inequalities about `DH` on a disk. Phase B (Computational) is partly built: certified real `exp`/`log` for any positive rational (`IntervalExp.lean`), certified complex `exp` with kernel-checked digits of `cos`/`sin` falling out (`IntervalCExp.lean`), and `contains_dirichletTerm` tying each term `n^{-s}` to a computed rational box with no oracle input. The tail bound is also kernel-checked (`DHTailBound.lean`): the DH series regrouped into five-term blocks converges absolutely on `Re s > 0`, equals `DH` there by the identity theorem, and `DH_tail_bound` gives the explicit error `(3+κ)·‖s‖·5^{-σ-1}·(K−1)^{-σ}/σ` for any `5K`-term partial sum — analytic continuation as a finite computation plus an error term, with no integrals in the block estimates (mean-value inequalities) and the integral test only for the final tail sum. The assembly machinery is kernel-checked too (`DHAssembly.lean`, `DHDemo.lean`, the square-contour criterion in `DHZeroCriterion.lean`, outward rounding in `IntervalCExp.lean`), and the pipeline is demonstrated end to end: `DH(3/2 + 3i) ≠ 0` is a kernel-checked theorem (`DH_demo_ne_zero`), the first certified fact about a DH value, produced with no oracle input. **Open: not scale — headroom.** Corrected 2026-08-10 after the mirror priced every site exactly (HANDOFF, fourth record): plan v2 is infeasible as emitted. The generator's own assert refuses grid sites before writing a line, and at the single Taylor order 20 the log truncation alone gives a box width of 1.5 against a beta of 0.05. Splitting the two Taylor orders (nLog 32, nExp 20 — `dirichletTermBox2`, kernel-checked) fixes that, and then 30 of 59 evaluated grid sites still fail, every one of the 59 within 2% of its threshold: beta was drawn at the achievable bound, so a ~1-2% width improvement flips all of them. The centre is 37% short and needs the exp order raised, which is the order that inflates literals. So what remains is a re-plan with real headroom, upstream of any compute. The target is *forced* — `t ≈ 85.699` is the lowest off-line zero, pinned by a standing test (`test_no_offline_zero_below_the_pinned_one`), so the `‖s‖^2.2` cost factor cannot be optimised away by choosing a cheaper zero. The steeper tail exponents are now **kernel-checked** (`DHTailBound2.lean`, 2026-08-10): comparing the block sum to its integral gives `K^{-(σ+1)}` (`DH_tail_bound_order1`), the trapezoid refinement `K^{-(σ+2)}` (`DH_tail_bound_order2`), with no Bernoulli numbers and no general Euler–Maclaurin — the block antiderivative `dhAnti` is closed-form because the coefficients sum to zero, and the corrections cost the instantiation nine extra certified cpow values. Effect, pinned by `test_dh_tail_bound_required_K_pins_the_cost_model`: a 1e-3 tail at the oracle zero needs `K = 195301` blocks at order 0, `1741` at order 1, `243` at order 2 — an 804× reduction; the boundary strategy is a certified point grid under a Cauchy Lipschitz bound (max principle on a larger square; `DHCertSupport.lean`, all kernel-checked), with the verified plan and cost honestly re-measured in HANDOFF (2026-08-10, second record): ~78k certified terms ≈ 25 core-hours once the composite-chain evaluation engine lands — naive boxed-`s` lower bounds and one-shot `norm_num` box evaluation are both measured infeasible and recorded as negative results. That run was believed to finish rung 3; it does not. See the correction above and HANDOFF's fourth 2026-08-10 record: the plan needs re-planning for headroom before any of that compute is worth spending.

Why this is in scope: it certifies the literature and the lab's reference
points. It is not an attempt on RH, and the deliberate-non-goal above stands.

### The upstream track: what of this belongs in Mathlib

A rung that only compiles here is worth less than one other people import.
`references/mathlib-open-targets.md` (generated by `scripts/mathlib_gaps.py`)
is the fact half: Mathlib's own `docs/1000.yaml` lists 1179 famous theorems and
**970 carry no `decl:`** — the library's written record of what it wants and
does not have. The judgment half is here.

Verified against Mathlib master and PrimeNumberTheoremAnd (2026-08-06, code
search plus open-PR search; **superseded in part — see the 2026-08-12
re-audit below**):

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

### Prior-art re-audit (2026-08-12): the 2026-08-06 table is stale in three rows

Web audit (repo inspection, code search, press), run 2026-08-12. These are
web-checked findings with sources, recorded at that strength — leads for the
next in-tree verification pass, not in-tree facts. The landscape moved on
2026-08-10, two days before this audit, and three of the table's rows are
affected.

- **`anthropics/zeta-23-lean` (announced 2026-08-10).** A sorry-free Lean 4 +
  Mathlib formalization that more than two thirds of ζ's nontrivial zeros lie
  on the critical line (`Zeta23.two_thirds_on_critical_line`, liminf
  N₀\*(T)/N(T) ≥ 2/3, stated against Mathlib's `riemannZeta`), including
  kernel-checked Riemann–von Mangoldt zero counting, Backlund's bound via
  Jensen, and the Weil explicit formula for ζ and primitive Dirichlet
  L-functions; reported as externally reviewed (Conrey, Goldston).
  https://github.com/anthropics/zeta-23-lean
  Consequences for the table: the *Critical line theorem (Hardy 1914)* row is
  no longer an open primacy target — the 2/3 result together with N(T) → ∞
  subsumes Hardy's infinitude qualitatively — and kernel-checked zero
  *counting* now exists outside PNT+ as well. Note what it does **not**
  contain: no numerical verification of any specific zero, and its
  Davenport–Heilbronn / Epstein "proves-too-much" controls are numerical
  only, not formalized. Rung 3's target (kernel-checked localization of a
  specific individual off-line zero of an L-function-like object) remains
  unclaimed as of this audit, as does any kernel-checked finite-height
  verification that specific ζ zeros lie on the line.
- **Hardy 1914 is also being attempted directly** by
  `JohnNDvorak/Littlewood_Proof` (Lean 4, sorry-carrying, states Hardy's
  theorem as a named gap). The "claimed elsewhere: no" cell is out of date in
  both directions.
- **Sturm's theorem: still absent from Mathlib, but now contested ground.**
  Loogle confirms only the modular-forms Sturm bound; nearest machinery is
  Descartes' rule (`Polynomial.signVariations`). Two PRs adding Sturm
  (mathlib4 #42558, #42559) were opened 2026-08-08 and **closed unmerged
  2026-08-10 by triage for inadequate AI-usage disclosure**. Two standing
  consequences: the target could be resubmitted by that author any week, and
  any PR from this repository must plan its AI-usage disclosure to Mathlib's
  standard *before* opening — the closure above is what skipping that looks
  like. Also recorded for honest wording: Sturm has long been formalized in
  Isabelle (AFP `Sturm_Sequences`, 2014) and Coq (math-comp `real-closed`),
  so the available first was only ever "first in Lean/Mathlib".
- **PNT+ status re-checked**: `Backlund/ZeroCountCrude.lean` is sorry-free
  (|N(T)| ≤ A·T^{3/2}, unconditional); `IEANTN/` carries explicit-estimate
  work; no critical-line occupancy work found. **"Do not go after N(T)"
  stands, stronger than before.** PNT+ also now consumes `LeanCert`
  (kernel-checked interval arithmetic with root-existence/exclusion/Krawczyk
  certificates for elementary functions — no ζ, no L-functions, no Dirichlet
  series), i.e. the ecosystem is assembling certified-numerics ingredients
  adjacent to this repo's interval layers. The window for finite-height
  firsts is open but should be assumed to be closing.

Decision deltas, recorded so they are not re-litigated: Sturm remains the
contribution target (with the disclosure requirement above); the Hardy Z
construction decision stands unchanged, but its *justification* narrows —
the "on-ramp to Q205966" argument is withdrawn (Q205966's content is
subsumed), and Hardy Z's value is now the lab's own rung: the sign lemma is
the dossier's one discriminating obligation and remains unformalized
everywhere as far as this audit could see.

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
