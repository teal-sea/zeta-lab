# `discovery/` — the ontology of the conjecture factory

**Phase 4, step 1: the schema and nothing else.** No generators, no screens, no
pattern hunting. This document defines what a candidate observation *is*, what
can be concluded about one, what must be recorded so it can be re-derived, and
when two observations are the same observation. Everything downstream —
`funnel.py`, `metrics.py`, `registry.py`, and the domain modules under
`domains/` — is written against these definitions.

The premise the design serves: **most numerical "discoveries" are already known
or trivial, and a system that does not measure its own hit rate is measuring
its operator's enthusiasm.** So the schema is built to make the unflattering
outcomes cheap to record and impossible to skip — `already-known` is a
first-class terminal state with its own detector, `survives` cannot be claimed
without naming the three checks that ran, and a refutation is not accepted
unless it survived a precision increase.

Nothing here, and nothing any funnel built on it produces, is evidence for the
Riemann Hypothesis. A surviving candidate is a lead. The `survives` state
requires you to write down, in the record, exactly what is missing before it
could be a theorem.

---

## The seam

`schema.py` (and its siblings `funnel.py`, `metrics.py`, `registry.py`) contain
**no subject-matter knowledge whatsoever**. They import nothing from the
laboratory package; they name no quantity the laboratory computes. They would
work unchanged for a chemistry lab or a compiler-optimisation search. The only
file that knows what is being studied is `domains/zeta_domain.py`, which
registers generators, screens and catalogues through the registry interface.

`tests/test_discovery_schema.py` enforces the seam three ways: an AST scan for
forbidden imports, a subprocess import that asserts the laboratory package
never enters `sys.modules`, and a lexical scan of the source for subject-matter
vocabulary. `tests/test_discovery_funnel.py` adds a fourth: the whole pipeline
runs in a subprocess with the laboratory made *unimportable* by a meta-path
wall, and it must still generate, screen and report. If the seam leaks, the
design is worthless — a bookkeeping layer entangled with its subject cannot be
trusted to report a number its operator does not want.

**`knownness.py` is one step less strict, and the step is documented.** It knows
general mathematics — π, γ, PSLQ, the standard constant basis — because
recognising a closed form requires it. It does not import the laboratory and no
historical case is decided by its table. Four of its `GENERAL_FACTS` entries
(`prime-number-theorem`, `mertens-third-theorem`, `hasse-weil-bound`,
`gue-wigner-surmise`) are standard results that a number-theoretic laboratory
will find familiar; they are named in the module docstring rather than left for
a reader to discover, because "knows no subject matter" would be the wrong
description of a table that contains them.

*Examples in this document are drawn from the laboratory to make the categories
concrete. The module holds none of them.*

---

## The ledger is private

The funnel writes to `conjectures/ledger.jsonl` and `conjectures/ledger.runs.jsonl`.
**That directory is in `.gitignore` and must never be committed.** The rule is
not administrative tidiness:

- a ledger is a notebook of *unreviewed leads*, and by this package's own
  premise most of them are already known, trivial, or wrong. A list nobody has
  checked, published under a repository that is otherwise checked, would be
  read as a set of claims;
- entries carry `open` and `inconclusive` states by design — work in progress,
  recorded so that it lands in the denominator, not so that it is read;
- **nothing in the ledger is evidence for anything.** A `survives` record is a
  lead whose own `proof_gap` field states what is missing before it could be a
  theorem.

`conjectures/.gitkeep` keeps the empty directory in the tree; `.gitignore`
excludes `conjectures/*` and re-admits only that file. Anything published from
the ledger should be a *report* — `discovery.metrics.render_text` — reviewed by
a human, not the log itself.

The reference run was reproduced from an empty ledger on 2026-08-04 with seed
`20260802`: 26 candidates became 20 `known`, 1 `trivial`, 5 `inconclusive`, and
0 survivors in 4.29 seconds. The committed public summary is in `ROADMAP.md`;
the 52 append-only candidate records and one run record remain private.

### Sharing a ledger between your own machines

Private does not mean unsynced. A fresh clone of this repo has an empty
`conjectures/` by design — that is the ignore rule working, not a fault — so a
second machine starts with no history. To carry the same ledger to both, keep
it in a **separate private repository** cloned in place at `conjectures/`:

```bash
scripts/ledger_sync.sh init   # once per machine — clone the private ledger in place
scripts/ledger_sync.sh sync   # pull the other machine's records, then push this one's
```

The public repo ignores `conjectures/*`, so it never sees that clone or its
records; the privacy rule above is unchanged, and the ledger still never enters
a public tree. The record files are append-only JSONL carrying `merge=union`,
so two machines that both ran the funnel merge without conflict. Pull before a
run and push after, or the two ledgers drift.

---

## 1. The five candidate kinds

Every kind is a **decision procedure**, not a word:
`kind_reasons(kind, claim, evidence) -> tuple[str, ...]` returns the reasons a
payload was refused; empty means accepted. `accepts` is the boolean form and
`classify(claim, evidence)` returns the unique accepting kind or `None`.
`None` is the common, correct answer for a vague observation: it means *this is
not a candidate*, not *this is a new kind*.

A candidate's payload is split in two, and the split is load-bearing:

- **`claim`** — the identity-bearing content, what is being asserted. Hashed.
  Keys are checked strictly against the kind's schema; an unknown key is
  refused, because a stray key would silently change the candidate's identity.
- **`evidence`** — the support: windows, tolerances, controls, counts,
  runner-ups. Free-form, validated for JSON-safety, **not** hashed. Finding the
  same claim again with better support does not create a second candidate.

The decision procedures read *both*: whether an observation is an asymptotic
candidate depends on whether the support qualifies as asymptotic evidence.

An optional top-level **`related_to`** list records graph annotations without
changing the claim. Each entry is `{candidate_id, relation}`, where `relation`
is `implies` or `equivalent_to`. Links are deliberately excluded from identity
and verdict logic: the schema checks their shape, but does not require the
target to be present, add reciprocal equivalence edges, or propagate verdicts.

The five kinds are **pairwise exclusive by construction**, and the test suite
proves it on the key sets rather than on examples: for any two kinds `A ≠ B`,
`required(A) ∪ required(B)` is never contained in
`allowed(A) ∩ allowed(B)`, so no payload can satisfy both.

### 1.1 `constant` — a measured number that may have a closed form

| | |
|---|---|
| **claim** | `subject: text`, `value: measure` (float or decimal text — *not* an `int`) |
| **evidence** | `uncertainty: measure` (absolute error bound) |
| **decision procedure** | `uncertainty > 0`; `value` finite; `value ≠ 0`; `|value| > uncertainty`; at least one significant digit determined, i.e. `floor(log10(|value|/uncertainty)) ≥ 1`; and `dedup_digits` must not exceed the digits the error bound determines |

**Holds:** λ₁ = 0.023095708966121034 with uncertainty 1e-18 — a number determined
to 16 digits, whose closed form `1 + γ/2 − log(4π)/2` a catalogue lookup will
promptly identify (verdict: `known` — which is the point of having the state).

**Rejects:** a quantity measured as `0.0 ± 1e-9`. A vanishing quantity is a
*relation* (`q = 0`), not a constant: its "closed form" question is a different
question, and admitting it here would let every defect function in the
laboratory manufacture a constant candidate. Also rejects `1e-9 ± 1e-8` (no
digit is determined) and any value offered without an error bound (`uncertainty`
is required, and must be positive — an exact integer count is not a measurement
and belongs to `extremal` or `structural`).

### 1.2 `asymptotic` — a growth-rate claim

| | |
|---|---|
| **claim** | `subject`, `index` (the variable), `limit ∈ {+inf, -inf, 0+, 0-}`, `scale: text` (the reference function), `exponent: number` |
| **evidence** | `windows: list` of `{index_min, index_max, exponent, n_points}`, `tolerance: measure` |
| **decision procedure** | at least 2 windows; each with `0 < index_min < index_max` and `n_points ≥ 3`; total span `max(index_max)/min(index_min) ≥ 4`; every per-window fitted exponent within `tolerance` of the claimed one |

**Holds:** λ_n grows like `(n/2)·log n` — exponent 1.0 on scale `n·log(n)/2`,
fitted separately on n ∈ [100, 500] and n ∈ [500, 2000], per-window exponents
0.99 and 1.01, tolerance 0.05.

**Rejects:** the same fit run once on n ∈ [100, 110] and once on [110, 120] —
span 1.2, refused. A rate fitted over a range that never doubles is a local
coincidence dressed as a limit, and this is the single most common way a
numerical search fools itself. Also rejects windows whose exponents disagree by
more than the tolerance: if the fit is not stable across the range, there is no
asymptotic claim, only a curve.

### 1.3 `relation` — a stated relation between two computed quantities

| | |
|---|---|
| **claim** | `lhs: text`, `rhs: text`, `relation ∈ {eq, le, lt, ge, gt, proportional, dist_match}`, optional `constant: number` |
| **evidence** | `defect: number ≥ 0`, `tolerance: measure > 0`, `defect_definition: text` |
| **decision procedure** | `lhs ≠ rhs`; relation from the closed vocabulary; `defect ≤ tolerance`; the defect must say what it measures |

**Holds:** λ₁ by the Cauchy-integral route versus λ₁ in closed form, relation
`eq`, defect 1e-25 against tolerance 1e-20, defect definition `abs(lhs - rhs)`.
Also holds the statistical case: empirical spacings versus the GUE law,
relation `dist_match`, defect = the Kolmogorov–Smirnov statistic.

**Rejects:** `lhs == rhs` — a quantity related to itself is a tautology, and an
unattended generator will produce those by the thousand. Also rejects a payload
whose defect *exceeds* its tolerance: that is a refutation of a relation, not a
candidate relation, and it must be recorded as a `refuted` verdict against the
claim it kills rather than smuggled in as a new observation.

### 1.4 `extremal` — a record over an explicitly bounded search

| | |
|---|---|
| **claim** | `subject` (the objective), `direction ∈ {max, min}`, `space: text`, `n_searched: count`, `argopt: atom`, `value: number` |
| **evidence** | `runner_up: number` |
| **decision procedure** | `n_searched ≥ 2`; `value` strictly beats `runner_up` in the stated direction |

**Holds:** the maximum of M(x)/√x over x ≤ 10⁶, at a named x, value 0.5709,
runner-up 0.5705.

**Rejects:** "the largest value seen so far", with no runner-up and no stated
search space — unfalsifiable where it stands. Also rejects a tie (`value ==
runner_up`): a tie is an extremal *set*, and the schema has no way to say which
element is the record. `n_searched` sits in the *claim*, not the evidence, so
extending the search to 10⁹ creates a **new** candidate — correctly, because a
record over a larger set is a different and stronger statement.

### 1.5 `structural` — a universal claim about an enumerated family

| | |
|---|---|
| **claim** | `family: text`, `predicate: text`, `scope: text` (the enumerated bounds) |
| **evidence** | `witnesses: list`, `n_checked: count`, `n_satisfied: count`, `controls: list` of `{id, satisfied}` |
| **decision procedure** | `len(witnesses) ≥ 3`; `n_checked == len(witnesses)`; `n_satisfied == n_checked`; **at least one control on which the predicate was evaluated and returned `False`** |

**Holds:** every Jensen polynomial J^{d,n} with d ≤ 12, n ≤ 10 is hyperbolic —
twelve witnesses, all satisfied, with a control (a polynomial with a complex
root pair) on which the same predicate returns `False`.

**Rejects:** the same claim with no failing control. This is the schema's
generalisation of the laboratory's standing counterexample battery: a property
that everything satisfies distinguishes nothing, so a structural claim with no
recorded near-miss has no content and is not a candidate. It also rejects
`n_satisfied < n_checked`: a universal claim with an exception already in hand
is a refutation of that claim, not a new one.

---

## 2. The six verdict states

`Verdict(status, decided_by, decided_by_version, decided_at, evidence, notes)`.
`verdict_reasons` enforces the entry criteria; `validate_verdict` raises. Every
decided verdict must name who decided it, at which version, and when.

| status | terminal | entry criteria (all enforced) |
|---|---|---|
| `open` | no | evidence **must be empty**. The initial state; you cannot smuggle a conclusion into an undecided record. |
| `known` | yes | non-empty `references` (identifiers — a DOI, an OEIS id, a document section, a laboratory symbol — never an opinion); `match_kind ∈ {value, statement, identity}`; if `value`, a `defect ≤ tolerance`. |
| `trivial` | yes | non-empty `derived_from` (the facts it follows from); an `argument` that is written out and **≤ 240 characters** — if it does not fit on a line it is not a one-line argument; `checked_by`, naming the procedure that verified the reduction reproduces the claim. |
| `refuted` | yes | a `witness` mapping (the parameters at which it fails); `defect > tolerance`; **and** `escalated_effort > effort` with `escalated_defect > tolerance` — the failure must persist at strictly higher precision, or it may be arithmetic noise. |
| `survives` | yes, re-openable | `checks_run` must contain all of `known`, `trivial`, `refutation` — you may not survive a check that never ran; `verified_effort > effort`, so verification cost strictly more than generation; and a non-empty `proof_gap` stating what is missing before this could be a theorem. |
| `inconclusive` | yes, re-openable | `reason ∈ {budget_exhausted, precision_insufficient, dependency_unavailable, nondeterministic, not_reproducible}`; a `detail` string; a `ceiling` mapping recording the resource limit that was hit. |

**Why these six.** `known` is expected to dominate, so it is a destination with
a detector (`match_known`), never a footnote on a near-miss. `trivial` catches
the second-largest class — true, but one line from something already recorded.
`refuted` is the honest outcome of most verification, with an anti-noise guard.
`inconclusive` is how *a whole line of work producing nothing* gets recorded:
the run happened, the ceiling is named, the conversion rate absorbs it.
`not_reproducible` lives here too — a candidate whose own provenance fails to
re-derive it is a defect in the lab, and the metrics must be able to count it.
`survives` is deliberately the most expensive state to enter.

Verdicts are **not** part of a candidate's identity. `Candidate.with_verdict`
returns the same candidate — same `id` — with a new verdict, and the JSONL log
is append-only: `latest_by_id` collapses it, last write wins. A `survives` that
later becomes `known` is one candidate with two records, not two candidates.

---

## 3. Provenance

`capture_provenance(...)` fills a `Provenance` that must let a stranger
re-derive the observation months later:

| field | why it is mandatory |
|---|---|
| `generator`, `generator_version` | conversion rates are *per generator*; bump the version whenever behaviour changes or the metrics silently mix two different procedures |
| `lab_object` | the dotted symbol path of the computed object (validated as a dotted path) |
| `parameters` | the call parameters; identifier keys, JSON-safe values |
| `precision` | `{kind ∈ dps|bits|float64|exact, value, backend}`, with `effort_digits()` so two precisions of different kinds are comparable — this is what makes the `refuted` and `survives` escalation checks enforceable |
| `seed` | required whenever `stochastic=True` |
| `code_revision`, `code_dirty`, `code_revision_source` | `git rev-parse HEAD` via `subprocess`, plus whether tracked files were modified. Outside a repository, or with no `git`, the source degrades to `"unavailable"` and the record says so rather than pretending |
| `captured_at`, `runtime`, `duration_s` | ISO-8601 UTC, interpreter/library versions, and the cost the funnel accounting needs |

`Provenance.is_reproducible()` is `True` only for a clean, identified revision
with a seed wherever randomness enters. It is a query the metrics layer is
expected to use: a generator producing irreproducible candidates is a defect,
not a style choice.

Two rules the validator enforces on every record: no non-finite float anywhere
(it cannot be valid JSON), and **no machine-local absolute path** (`/Users/…`,
`/home/…`, `C:\Users\…`) in any string. *Anywhere* means the claim, the
evidence, the provenance **and the verdict's evidence** — all four are written
to the same log, so all four are checked. The checkout `capture_provenance`
asks about is derived from `__file__`, never from a hard-coded location.

---

## 4. The deduplication contract

**Definition.** Two candidates are the same candidate **iff they have the same
`kind` and their canonicalised `claim` mappings are byte-identical at the same
resolution.** The `id` is

```
cand- + first 128 bits of SHA-256 over  {"v":<schema major>,"kind":<kind>,"claim":<canonical claim>}
```

Canonicalisation, precisely:

- mapping keys are sorted (insertion order is not meaning); sequences keep their
  order (order **is** meaning inside a claim);
- `int` is rendered exactly; `float`, `Decimal` and decimal-looking strings are
  rounded to `dedup_digits` significant digits and rendered in a fixed
  scientific form — so `1.0`, `"1.0"` and `1.000000000_1` collide, and a
  high-precision decimal string keeps its full value in the record while
  hashing at the shared resolution;
- an `int` and a `float` of the same numeric value canonicalise **differently**,
  on purpose: "exactly one million" and "one million, measured" are different
  claims. The per-kind field types (`count` vs `measure` vs `number`) exist to
  stop a generator flip-flopping between them;
- `bool` and `None` are their JSON spellings; unknown types are refused.

**What is deliberately excluded from identity:** provenance (generator, version,
parameters, precision, seed, revision, timestamp), verdict, label, `related_to`,
and *all* evidence. Two generators that find the same relation produce one
candidate with two provenance records — which is exactly the measurement the
metrics layer exists to make ("generator B has found nothing generator A had
not").

**Why nine significant digits.** `DEFAULT_DEDUP_DIGITS = 9` sits in the gap
between two failure modes. Too few digits and distinct quantities merge: a
catalogue lookup at 4 digits matches half the small integers and their obvious
combinations. Too many and a re-run splits from its own earlier discovery over
arithmetic noise — a `float64` pipeline carries ~15.95 digits and routinely
loses 3–6 to accumulated error. Nine leaves that headroom while remaining
selective, and it is far below the precision at which a high-precision re-run
quotes its result, so the re-run merges.

**The contract's guard rail.** For `constant` candidates the validator refuses
`dedup_digits` greater than the digits the error bound actually determines
(`floor(log10(|value|/uncertainty))`). You may not hash digits you did not
measure — that is precisely how a candidate splits from its own re-discovery.

**Known failure modes, stated rather than hidden:**

1. *Different resolutions do not merge.* Two records of the same number written
   with `dedup_digits` 9 and 6 have different ids. Mitigation: the default is
   fixed, generators only lower it when their error bound forces them to, and
   `same_claim(a, b)` re-compares at the coarser of the two — the metrics layer
   should use it whenever it needs to be careful. Hash equality implies
   `same_claim`; the converse is not guaranteed.
2. *Boundary straddling.* Two measurements either side of a rounding boundary
   in the 9th digit split. This is intrinsic to any hash-based deduplication
   and cannot be fixed by choosing a different digit count; it can only be
   traded against false merges. Deduplication is therefore a **lower bound** on
   duplicate detection, and the metrics layer must not report it as exact.
3. *Naming drift.* Identity strings (`subject`, `family`, `lhs`, …) are opaque
   to the schema. A domain module that names the same quantity two ways
   manufactures two candidates. That is an operator responsibility, and the
   registry is where it should be constrained.
4. *Truncation.* 128 bits collide by birthday at ~2⁶⁴ records; a laboratory log
   will not reach it. The test suite pins 20 000 near-identical claims to
   20 000 distinct ids.

`from_dict` recomputes the hash and **refuses a record whose stored `id`
disagrees with its claim**, so a hand-edited or corrupted line is rejected
rather than silently counted.

---

## 5. Schema version and migration policy

`SCHEMA_VERSION = "1.1"`, and `SCHEMA_MAJOR` is inside the hash preimage.

- **Minor bump** (`1.0 → 1.1`): may only *add optional fields*. Canonicalisation
  must not change, so every id stays stable. Old readers tolerate new records
  (unknown top-level keys are ignored); new readers fill defaults for old ones.
  Unknown *claim* keys are still refused — they would change identity.
- **Major bump** (`1.x → 2.0`): may change canonicalisation, therefore changes
  **every** id. It must ship a `migrate_record` path that rewrites the record
  and stores the old id under `supersedes`, so historical conversion rates
  survive the change.
- A record from an **unknown major is refused**, never guessed at.
- `SCHEMA_HISTORY` is the append-only log of revisions and is part of the
  module's public surface.

---

## 6. What was cut, and why

- **Free-text "conjecture" / "observation"** — no decision procedure exists;
  the category would accept everything, and a category that accepts everything
  is a defect. Anything worth keeping fits one of the five shapes, and if it
  does not fit, the honest record is that it was never a candidate.
- **"Anomaly" / "outlier"** — indistinguishable from `extremal` once you state
  the objective, and unfalsifiable until you do. If the objective can be named,
  it is `extremal`; if it cannot, there is nothing to verify.
- **"Counterexample"** — not a kind. A counterexample is a *verdict* (`refuted`)
  on an existing claim. Keeping it as a kind would let a refutation be logged
  as a discovery, which is the exact accounting error this package exists to
  prevent.
- **"Identity"** as distinct from `relation` — an identity is `relation` with
  `relation="eq"`. One decision procedure, not two.
- **"Statistical / distributional fit"** as its own kind — merged into
  `relation` as the `dist_match` operator: two computed objects, a named
  discrepancy, a tolerance. Its decision procedure would have been identical.
- **"Conjecture strength" / "interestingness" scores** — no procedure, and a
  free scalar would be re-derived by every reader as a ranking, which is
  enthusiasm with a decimal point. Ranking belongs to `metrics.py`, computed
  from recorded outcomes.

---

## 7. What this schema cannot express

Every ontology has a blind spot. These are ours.

1. **Zero-yield generator runs.** A candidate record needs a candidate. A
   generator that ran for an hour and emitted nothing leaves no trace here, yet
   that is a genuine funnel outcome and it belongs in the denominator of every
   conversion rate. `funnel.py` must record generator *invocations*
   independently of candidates; the schema neither provides nor enforces it.
   This is the largest single gap, and it is a requirement placed on the next
   layer rather than a limitation to shrug at.
2. **Claims with quantifier structure.** `structural` expresses "every member of
   this enumerated, finite family satisfies P". It cannot express "there exist
   infinitely many", "for all sufficiently large", or any alternation of
   quantifiers. Those are not decidable by enumeration, so by rule 1 the
   category was cut rather than faked. An "infinitely often" observation must
   be recorded as the finite evidence actually in hand.
3. **Relations among more than two quantities.** `relation` is binary. A
   three-way identity must be recorded as a derived quantity plus a binary
   relation, which loses the shape of the original statement.
4. **Graph consistency.** Version 1.1 can record `implies` and `equivalent_to`
   edges, but deliberately does not turn them into deductions. It does not
   require a target already to exist, require the reverse edge for an
   equivalence, detect cycles, or propagate verdicts. Those checks need a view
   of the whole ledger; a single candidate record cannot earn them.
5. **Anything about the *reason* a claim might be true.** The schema records
   what was asserted, what supported it and what killed it. It has no
   representation of a mechanism, a proof sketch or a heuristic — `proof_gap`
   is a sentence a human writes, not a structure a machine can check.
6. **Degrees of belief.** A verdict is one of six states. There is no
   probability, no confidence score, no partial credit. This is deliberate: a
   number nobody can calibrate becomes a number everybody quotes. The cost is
   that "refuted at 40 digits but the tail bound was hand-waved" and "refuted
   cleanly" look identical at the status level, and are distinguished only by
   reading the verdict evidence.
7. **Whether the subject-matter naming is honest.** The schema validates shape,
   not meaning. A generator that labels an arbitrary quantity `subject="the
   thing"` produces valid records forever. The seam that keeps this module
   domain-agnostic is exactly what makes that impossible to check here.

---

## 8. The pipeline layer: `registry`, `ledger`, `funnel`, `metrics`

Four more domain-agnostic modules, enforced by the same three seam tests
(`tests/test_discovery_funnel.py`), plus a fourth: the whole pipeline is run in
a subprocess with the laboratory package made *unimportable* by a meta-path
wall, and it must still generate, screen and report.

- **`registry.py`** — three plug-in roles (`Generator`, `Screen`,
  `KnownnessDetector`) and a `Domain` that bundles them. A screen declares its
  `cost` (`cheap`/`expensive`) and the `checks` it performs; a `ScreenResult`
  may pass, or stop a candidate with a verdict that already earns its status —
  there is no "flag", because a flag is an opinion with no decision procedure.
- **`ledger.py`** — append-only JSONL, `conjectures/ledger.jsonl` plus the run
  stream `conjectures/ledger.runs.jsonl`, locked appends, atomic compaction.
- **`funnel.py`** — `generate → deduplicate → knownness → cheap → expensive →
  terminal`, with the invariant that **count in equals count out for every run
  that completes**: every candidate leaves with one of seven dispositions (the
  five verdict statuses plus `duplicate` and `invalid`, which are funnel
  bookkeeping and not claims about the world). A run killed by a raising
  plug-in is the stated exception, and it is counted rather than hidden — see
  §8.1.
- **`metrics.py`** — the conversion tables. Every rate whose denominator is
  empty is `None`, never `0.0`. There is no *novelty* rate anywhere in it: the
  residue left by the checks that ran is `unsettled_rate`, and it is named that
  way because a catalogue that matched nothing has established nothing about
  the literature (`knownness.py`'s integrity rule, enforced here too — a test
  asserts no rendered table contains the word).

### 8.1 §7.1 (zero-yield runs) is closed in the run stream, not in the schema

`funnel.py` records **every generator invocation**, with its wall-clock cost,
whether or not it produced anything, and writes the run record twice
(`state="started"`, then `"finished"`) so a run that *died* is still in the
denominator. The schema is unchanged: a candidate record still needs a
candidate. The gap is filled beside it, exactly as §7.1 required.

Three run states, not two. A plug-in that raises ends the run with
`state="crashed"` and **the outcomes it had already decided**, plus
`aborted_by`, `entered` and `undecided`. The exception still propagates — a
screen that throws is a defect, not a verdict — but a run that screened four
hundred observations and died on the four hundred and first must not vanish
from the conversion rates, which is what happens if only the `started` record
survives. Only a run killed outright (no Python-level exception) leaves nothing
but `started`; it then counts as one incomplete run and contributes no
outcomes, because nothing knows what it did.

The candidates queued behind the failure never reach a disposition, so they are
no terminal conversion rate. They do remain in the emitted denominator:
`metrics.funnel_report`, `generator_scorecard` and `time_series` attribute them
as `undecided`, including per generator, so a crash cannot improve a source's
rates by shrinking its population. Re-running decides them: the one that was
mid-screen is `open` in the candidate log and is *resumed*, and the ones still
queued were never written, so a deterministic generator simply emits them
again. An operating-system kill cannot write the final crash record; the open
checkpoint and the earlier `started` record make that case visible and
resumable, and a subprocess SIGKILL test pins the behaviour.

Run records collapse by `run_id`, last write wins, so re-using a `run_id` would
delete an earlier run's outcomes from every denominator. An explicitly supplied
`run_id` that is already in the stream is therefore refused.

### 8.2 Friction found while building against this schema

Recorded rather than worked around, for whoever revises the ontology:

1. **`Precision("exact")` can never survive.** `survives` requires
   `verified_effort > effort`, and `effort_digits()` for exact arithmetic is
   `inf`, so no verification can exceed it. An exact result — the strongest
   kind available — is therefore unpromotable. The funnel writes
   `inconclusive/precision_insufficient` with `ceiling.effort = "exact"` rather
   than promoting anyway, and a test pins that behaviour. A future minor
   version might give `survives` an escalation predicate rather than a strict
   numeric comparison.
2. **`InconclusiveReason` has no value for "this domain has no such screen".**
   A candidate that passed everything but whose domain never ran the `trivial`
   check is recorded as `dependency_unavailable`, which is the closest fit; the
   missing dependency is a plug-in, not a library.
3. **`Verdict.evidence` is frozen on construction**, so a list written as
   evidence reads back as a tuple from a live object and as a list from JSON.
   Harmless, but consumers must not compare with `==` against a literal list.
4. **The funnel-level dispositions have no home in the schema.** `duplicate`
   and `invalid` are not verdicts — nothing about the world is being asserted —
   so they exist only in the run stream. That is the right split, but it means
   the candidate log alone cannot reproduce a conversion rate.
5. **Payloads a generator built and refused are not in the ledger.** §8.1
   closed the zero-yield gap for a whole *invocation*; the same gap remains one
   level down, for the individual payload a generator constructed and then
   declined to emit (a tie in an extremal search, a shape the schema would have
   refused, a coefficient bound the available digits could not support). The
   `zeta` domain records these on a `refused` list and `scripts/13` prints the
   count and the reasons for the pass it just ran, but the list is in-memory and
   cleared on every call: it reaches **no run record and no ledger**, so the
   cumulative dashboard (`--report`, `metrics.render_text`) cannot see it, and
   the same argument the console makes for showing it per-run applies to the
   cumulative view, where it is silently lost. `registry.Generator` has no
   `refused` role and `funnel.GeneratorReport` has no field for it. Closing this
   means adding an optional protocol member and an additive run-record field —
   a change to the run stream, so it is stated here rather than made.

### 8.2.1 Defects closed by the cross-cutting audit

The audit recomputed a scorecard directly from the raw run stream and found two
accounting defects. Both are now regression-tested:

1. `GeneratorStat.produced` used decided outcomes rather than the generator's
   report, so a crash silently improved that generator's rates. It now counts
   everything emitted and attributes the difference as `undecided` per source.
2. `unsettled_rate` included `refuted`, although a persistent counterexample is
   a terminal answer. Its numerator is now exactly `survives + inconclusive`;
   crash-interrupted candidates have their own rate and cannot improve ranking.

The same audit forced a screen exception, killed a subprocess inside a screen,
fed duplicates both within and across runs, grepped every code/document/output
path for novelty leakage, mutation-tested Mertens by forcing `survives`, and
mechanically checked every domain-agnostic module by AST, clean subprocess and
lexical scan. Completed runs conserve exactly; killed runs leave a visible,
resumable checkpoint. "Not recognised offline" remains no verdict and no claim
about novelty.

### 8.3 What the funnel refuses to do

It will not promote anything to `survives` on its own authority. That requires
all three of `known`/`trivial`/`refutation` to have actually run — the domain
declares which plug-in performs which — *and* a screen to report a verification
effort strictly above the effort the candidate was generated at. When either is
missing, the record is `inconclusive` with the ceiling that was hit. A survivor
carries a machine-written `proof_gap` saying that no proof is attached and that
it is a lead to be examined by hand. Nothing this pipeline produces is evidence
for anything.

---

## 9. Validation against history

A classification system that cannot correctly bin claims whose outcomes are
**already settled** is not ready to classify anything unsettled. Before this
funnel is pointed at an unexamined question, it has to reproduce history.

`discovery/historical_cases.py` is the harness and is domain-agnostic like its
four siblings: it defines what a settled case *is* (`HistoricalOutcome`,
`HistoricalCase`), replays one through any `Domain`, and adjudicates the result.
`discovery/domains/zeta_history.py` supplies this laboratory's cases. The seam
test globs `discovery/*.py`, so the split is not a stylistic choice — a harness
that named the subject would turn the existing suite red.

`IMPOSSIBLE_DISPOSITIONS` is the load-bearing part. It maps each historical
outcome to the dispositions the pipeline may never assign, and `case_reasons`
**refuses to register a case whose declared expectations overlap it**. Without
that, a failing case could always be repaired by editing its expectation, and a
suite that can be edited into agreement measures nothing.

Each case is replayed twice: `full` (the pipeline as it stands) and
`uncatalogued` (the catalogue replaced by an empty one that still runs). The
gate is *emptied*, not deleted, because deleting it makes `survives`
structurally unreachable — §8.3 — so every case would come back `inconclusive`
and the second replay would prove nothing.

### 9.1 What passed

All five cases classify correctly; 70 assertions in
`tests/test_discovery_historical_validation.py`.

| case | history | `full` | `uncatalogued` |
|---|---|---|---|
| Gauss 1792, π(x) ~ Li(x) | true, proved 1896 | `known` / `theorem` | `inconclusive`, *precision_insufficient* |
| Montgomery 1973, pair correlation | true so far as known, **open** | `known` / `conjecture` | `inconclusive`, *dependency_unavailable* |
| Mertens 1897, \|M(x)\| < √x | **false**, disproved 1985 | `known` / `disproved` | `inconclusive`, *dependency_unavailable* |
| Li 1997, λ_n ≥ 0 | equivalent to an open problem | `known` / `equivalent_to_open_problem` | `inconclusive`, *dependency_unavailable* |
| a PSLQ coincidence at 10 digits | never true (constructed) | `refuted` | `refuted` |

The Mertens case is the one that matters, and it is the reason the suite exists:
every computation feasible for a century supported that conjecture and it is
false. **The funnel does not endorse it in either mode.** The record it writes
says only "no violation was found for 2 ≤ x ≤ 10⁶", with three seeded ±1 random
walks as the controls the schema demands — every one of which violates the same
predicate inside the same range, which is why nobody should have believed it.

Two design consequences were forced by the exercise and are worth stating:

- **`known` could not say what kind of known.** `KnownFact` now carries a
  `status` from a closed vocabulary (`theorem`, `conjecture`,
  `equivalent_to_open_problem`, `disproved`, `established`), which
  `default_fact_matcher` puts into every match as `literature_status`. Without
  it, "already known" reads identically for the prime number theorem, for
  Montgomery's conjecture and for a disproved claim. The Montgomery case
  additionally asserts that no word anywhere in its record claims a proof.
- **A negative control needs a positive control.** "The spurious candidate was
  refuted" establishes nothing unless a candidate of the same shape can get
  through. `build_honest_twin` is the same subject, the same route and the same
  claimed error bar, measured instead of guessed; it reaches `survives` in both
  modes. A survivor is a lead, not a result.

### 9.2 What did not pass, and what it would have meant

Nothing was misclassified. Two things the exercise exposed are defects
nonetheless, both pinned as tests rather than written up as observations:

1. **Every historically correct answer was carried by the catalogue alone.**
   With the gate emptied, not one of the four claims is decided by anything that
   examined the mathematics; each stops for a different missing dependency
   (`test_each_case_was_stopped_for_a_distinct_and_named_reason` pins which).
   This is correct behaviour — the pipeline refuses to promote what it could not
   verify — but the screens contributed nothing to four of the five right
   answers. A laboratory that had not measured this would be crediting its
   screens for the catalogue's work, which is precisely the self-flattery this
   package exists to prevent. `gate_dependence` is the query that reports it.

2. **Deduplication merges a measurement with a coincidence.** The honest value
   of the probe quantity and the wrong closed form agree to twelve significant
   digits; identity is the canonical claim at `DEFAULT_DEDUP_DIGITS = 9`, so
   they are *the same candidate* — same id, `same_claim` true. Run in one pass,
   the second is recorded `duplicate` and never screened: whichever is logged
   first decides the fate of the other, and a refuted coincidence can shadow a
   correct measurement of the same quantity. They collide at every resolution up
   to and including twelve digits and separate at **thirteen** — the exact
   threshold, pinned from both sides by a test rather than quoted from a
   comfortable value above it.
   This is a **schema change**, not a domain fix — identity for a `constant`
   would have to include its error bound, which changes every id and requires a
   major version under §5 — so it is reported here and not made.

Had any case been misclassified, the meaning was written down in advance:
each `HistoricalCase` carries a mandatory `if_it_fails`, and the failure message
prints it. A `survives` on Mertens would have meant no output of this pipeline
could be trusted about anything unsettled; a `survives` on Gauss would have
meant the catalogue does not contain the prime number theorem; a `refuted` on
Li's criterion would have meant the laboratory believes it has settled an open
question, and the correct inference from that is a bug.

### 9.3 Limits of this validation

- **Five cases is a sample, not a suite.** They were chosen to span the outcome
  vocabulary, not at random, and every one of them is famous — which is exactly
  the population a catalogue is best at. Conversion rates measured on them do
  not transfer to unexamined observations.
- **Two of the four historical claims never reached the terminal stage in the
  counterfactual replay**, because the counterexample battery has no analogue of
  their predicates. The disposition is right; the argument is thinner than it
  looks.
- **"Mertens was not endorsed" is only a measurement if endorsement was
  reachable.** Two of the three reasons the pipeline does not promote it are
  bookkeeping rather than mathematics (see the next two bullets), so the
  headline result is on its own compatible with a suite that could never fail.
  `test_the_mertens_case_would_actually_fail_if_the_funnel_endorsed_it` closes
  that from the other end: it builds a pipeline that **does** endorse the
  observation — every screen a rubber stamp reporting a colossal verification
  effort, and the candidate's precision made finite so the effort comparison can
  be satisfied — confirms the funnel then writes `survives`, and asserts that
  the adjudicator reports a CRITICAL misclassification. Together with the rule
  that a case may not declare an expectation `IMPOSSIBLE_DISPOSITIONS` rules
  out, that is what makes the suite a measurement rather than a decoration.
- **The Mertens candidate is generated at `Precision("exact")`,** so §8.2 alone
  would have blocked promotion regardless of the mathematics. Removing the
  battery as well (a test does) shows the terminal stage recording
  `precision_insufficient` with `ceiling.effort = "exact"`. The conjecture is
  refused by three independent rules, none of which is that its mathematics was
  checked.
- **`structural` cannot record an exhaustive scan.** The Mertens scan covers
  999 999 integers and the record says `n_checked = 12`, because the schema ties
  `n_checked` to the number of witnesses written down. The real count sits in a
  free-form evidence key that nothing validates.
- **The relation case has no re-derivation route,** so the precision screen
  stops it at `dependency_unavailable` rather than passing it on. The domain has
  no route for a distributional statistic, and until it does, no `relation`
  candidate of that shape can clear the cheap screens.
