# The literature monitor: brief, and the incident that asked for it

**Written 2026-09-12.** This is a build brief, not a result. It specifies the
smallest standing literature watch that would have prevented a measured
failure, states what it must not grow into, and flags the one question about
it that is the operator's to settle rather than an agent's.

Nothing here is mathematics. It belongs in `meta/` because the quantity under
test in this directory is legitimate research output per unit of scarce human
judgment, and the incident below spent human judgment on something a cron job
does better.

## 1. The incident

Biao Wang posted arXiv:2609.07918, *Simple critical zeros and distinct zeros
of the Riemann zeta-function in short intervals*, at 2026-09-07T19:30:23Z. It
is the short-interval version of the exact theorem every Palomar entry this
laboratory holds is built on. Its global endpoint is `H = 0.6725007036794116`,
the constant `README.md` quotes as the floor the lab climbed off.

The laboratory learned of it on 2026-09-12, five days later, from an
unsolicited email sent through the contact form on `zeta.teal-sea.com` by a
member of the public who had been shown it by a commercial chatbot.

Nothing in this tree watches the literature. `ontology/scout_online.py` has a
working `ArxivBackend`, but it is a *pull*: it answers "has anyone seen this
candidate of mine", when handed a candidate. There is no path by which a new
paper reaches a session that has not already guessed its content.

The near-miss is measurable, and the comparison is the uncomfortable part:

| paper | posted | reached the lab | by what route |
|---|---|---|---|
| Lamzouri, arXiv:2609.02882 | 2026-09-02 | 2026-09-05, `hunts/cycle_moments` cites it | a session found it by hand |
| Wang, arXiv:2609.07918 | 2026-09-07 | 2026-09-12 | a stranger's email |

Three days by hand is the current unautomated baseline. Five days and an
outside favour is the current failure. A monitor that cannot beat three days
is not worth building.

This is an `meta/ledger.py` intervention in the precise sense that module
means: a human did what the machinery could not, and the missing capability
has a name. **Record it there as part of this build.** The named missing
capability is "standing literature watch on the lab's own subject".

## 2. Calibration measured before any code was written

These are live results from the arXiv API on 2026-09-12, and they are the
reason this brief exists instead of a one-line ticket. The obvious keyword
list does not work.

| query against `cat:math.NT` | returns Lamzouri | returns Wang |
|---|---|---|
| `all:"simple zeros"` | yes | **no** |
| `all:"simple critical zeros"` | no | yes |
| `all:"pair correlation"` | yes | yes |
| `abs:"critical line"` | yes | yes |

The phrase a person would reach for first, "simple zeros", misses the single
most relevant paper published this year, because Wang writes "simple critical
zeros". A monitor built on a plausible-sounding keyword list would have
reproduced the exact failure it was built to prevent, and would have reported
a clean run while doing it.

Two further facts from the same session, both load-bearing:

- **The API is reachable from this environment and from GitHub Actions.**
  `https://export.arxiv.org/api/query` returned HTTP 200. Courtesy limit is
  roughly one request every three seconds; space the queries.
- **The RSS endpoint returns an empty feed on weekends.**
  `https://rss.arxiv.org/rss/math.NT` returned HTTP 200 with zero `<item>`
  elements on Saturday 2026-09-12, because arXiv does not announce on
  weekends. An RSS-driven monitor therefore has a silent empty state that is
  indistinguishable from a broken feed. See §5.

Also observed: Lamzouri is now at **v2** while `hunts/cycle_moments` cites
v1. Version replacement of a paper the lab depends on is as interesting as a
new paper and is easy to forget.

## 3. What to build

One scheduled job. Keyword and author queries against the arXiv API, dedup
against what has already been reported, one GitHub issue per new hit.

That is the whole thing. The live consumer is a session doing frontier work
that needs to know a paper landed, and the delivery channel is the one this
repository already mandates: `CLAUDE.md` says an observation goes in the open
as a GitHub issue, and "this is true and unresolved" is exactly what a new
paper on the lab's target is.

Specifics that are decisions, not preferences:

- **Query set.** Union of several narrow queries rather than one broad one,
  because §2 shows single queries have blind spots. Start from
  `pair correlation`, `simple zeros`, `simple critical zeros`,
  `critical line`, `zeros of the Riemann zeta`, `de Bruijn-Newman`,
  `Davenport-Heilbronn`, `Li's criterion`, `mollifier`, `form factor`,
  `short intervals` combined with `zeta`. Add author watches for the people
  currently in the race: Lamzouri, Biao Wang, Baluyot, Goldston, Suriajaya,
  Turnage-Butterbaugh, Chirre, Goncalves, de Laat, Bui, Conrey, Pratt,
  Farmer, Gonek, Lee. Author-field syntax needs testing: `au:Wang_B` with a
  category filter returned nothing, so verify each author query returns that
  author's known papers before trusting it.
- **Categories.** `math.NT` primarily. Consider `math.CA`, `math.SP` and
  `cs.LO` at lower weight; the Lean and formalization side of the field does
  not always post to `math.NT`.
- **Dedup state.** Search the repository's existing issues for the bare arXiv
  identifier before opening a new one. Prefer that over a committed state
  file: it needs no write-back commit, it survives a re-run from a clean
  checkout, and the issue list is the record anyway.
- **Version updates.** Track the version suffix, not just the identifier, for
  any paper already cited anywhere in the tree. A v2 of a load-bearing source
  gets an issue.
- **Compute.** GitHub Actions on a cron, per the compute discipline in
  `CLAUDE.md`: this repository is public, so runners are free, and nothing
  heavy ever runs on the operator's machines. `full.yml` already carries a
  daily `0 7 * * *` schedule, so the precedent and the shape both exist.
  Run on weekdays; arXiv does not announce on weekends.
- **Issue body.** Identifier, title, authors, submission date, abstract,
  which query matched, and a link. No assessment of importance. The monitor
  reports that a paper exists; a session decides whether it matters.

## 4. The validation gate, which is not optional

This repository's habit is that a cross-check which cannot fail is not a
cross-check. `tests/test_pari_oracle.py` was validated by planting six faults
and confirming each turned it red. The monitor gets the same treatment, and
its test is already written for it by §2:

> **A cold run over the window 2026-09-01 to 2026-09-12 must return both
> arXiv:2609.02882 and arXiv:2609.07918.**

A monitor that misses Wang is not a monitor, it is a source of false
confidence about the thing it is failing at. Pin that as a test. Pin the
query-level facts in §2 as well, so that a future edit which drops the query
that catches Wang fails loudly rather than quietly narrowing coverage.

## 5. It must fail closed

`CLAUDE.md` records why, in a different context and at some cost: the first
version of `scripts/check_secrets.py` failed **open**, because its object
lister returned an empty list when git errored, so a malformed range reported
clean and the hook allowed the push. "A guard that fails open is worse than
none because it also supplies confidence."

The monitor has exactly that failure shape, and §2 found the trap before it
was built: an empty result set is the *normal* state on a weekend and on a
quiet day, and it is also what a broken query, a changed API schema, a
network failure and an expired token all look like. So:

- An HTTP error, a parse failure or a zero-entry response to a query that has
  never returned zero before must **fail the job**, visibly, not log "no new
  papers".
- Distinguish "queried successfully, nothing new" from "did not query" in
  whatever the job writes down. `ontology/scout_online.py` already models
  this distinction correctly with its `_did_not_reach` path; follow it.

## 6. Non-goals

Stated because each is an attractive way to turn a cron job into a project,
and `harness/VERDICT.md` is what that costs:

- **No relevance model, no scoring, no triage layer.** Keyword match, then a
  human or a session reads the issue. Revisit only if issue volume actually
  becomes a problem, with the volume measured rather than predicted.
- **No backlog file in this repository.** `CLAUDE.md` is explicit: an issue
  says "this is true and unresolved", the roster in fulcrum says "this one is
  next". The monitor produces issues and stops.
- **No new abstraction over `ontology/scout_online.py`.** Extend or reuse its
  arXiv fetching; do not build a source-plugin framework for the second
  source before there is a second source.
- **No adding this to `references/papers.md` automatically.** That file is a
  curated annotated shelf of sources actually read and engaged. A machine
  appending unread titles to it would destroy exactly the property that makes
  it worth having.

## 7. The boundary question, for the operator

`CLAUDE.md` draws the line as: needed to evaluate or reproduce a public
claim, it belongs here; teaches the lab how to allocate, route, prompt or
operate itself, it belongs in fulcrum unless reproducibility needs it.

A literature monitor sits on the line, so the argument for each side, and
then the flag rather than a framework to adjudicate it:

**For here.** The novelty rule in `CLAUDE.md` requires that where a search
has been run the lab must say what was searched and what it found, and
`ontology/knownness.py` deliberately defaults to "the literature was not
consulted" so an unrun check never reads as absence of prior art. A standing
monitor is the machinery that lets this tree stop defaulting to unsearched.
That is reproducibility, and it is public.

**For fulcrum.** The watch list encodes who the lab considers competition and
which directions it is tracking, which is closer to allocation than to
evidence.

The split this brief recommends, which the operator should confirm or
overturn: the **scanner and its queries are public and live here**, because
they are the search record; **what to chase in response stays in the roster
in fulcrum**. Do not build anything that adjudicates this automatically.

## 8. Beyond arXiv

In rough order of value per unit of effort. None is required for a first
version, and none should be built before arXiv is working and validated:

- **GitHub watches on the tracked competitor repositories.** The race is
  partly conducted in code, and `hunts/amtopa_ceiling` exists because of one
  such artifact. A new tag or release on a tracked repository is a signal.
- **The Palomar Registry.** New entries in the lab's own verification venue
  are directly relevant and the registry is small enough to poll cheaply.
- **alphaXiv**, which carries the same papers with a comment layer, and
  sometimes carries the first outside reading of a paper.
- **zbMATH and MathSciNet.** Backends already exist in
  `ontology/knownness.py`; they are slow-moving and better for prior-art
  checks than for news.
- **Mathlib pull requests touching number theory.** Relevant to the Lean arm
  specifically: a lemma the lab needs may arrive upstream.

## 9. Immediate backlog, found while calibrating

The queries in §2 surfaced recent `math.NT` papers this tree has never
looked at. They are listed as leads, not as assessments, and the fact that a
ten-minute calibration produced a nonzero backlog is itself the argument for
§3:

- **arXiv:2609.07918**, Wang. The subject of the companion brief in
  `hunts/short_interval/MISSION.md`. Read that first.
- **arXiv:2609.11619**, Hagen, *Sharp unconditional moment bounds for
  products of L-functions*, 2026-09-10. Flagged because
  `hunts/cycle_moments` is blocked on an unproved normalized fourth-moment
  bound, and this is an unconditional moment bound. Whether it is the right
  shape is unchecked.
- **arXiv:2609.01101**, Durkan, Karak and Mahatab, *Sharp lower bounds for
  shifted moments of Dedekind zeta functions*, 2026-09-01. Same reason, one
  step further from the target.
- **arXiv:2609.02882v2**, Lamzouri. The tree cites v1. Check what changed.

## 10. Built

**2026-09-12.** Built in the same session as this brief, uncommitted, for review: `scripts/literature_monitor.py` (standard library only; a union of eleven narrow keyword queries from §3 against `math.NT`, `math.CA`, `math.SP` and `cs.LO`, spaced three seconds apart, paged newest-first until the window is covered; dedup by scanning every existing issue for the bare identifier, with `GITHUB_TOKEN` read at call time and never printed; version tracking for every `arXiv:NNNN.NNNNN[vN]` cited anywhere in the tree, so a replaced version of a load-bearing source gets its own issue; issue bodies carry identifier, title, authors, submission date, abstract, matching queries and link, and no assessment), `.github/workflows/literature-monitor.yml` (06:00 UTC, Monday to Friday, plus `workflow_dispatch`, never on push, `issues: write` and `contents: read`, fifteen-minute timeout), `tests/test_literature_monitor.py`, and an entry in `meta/interventions.jsonl` naming the missing capability as "standing literature watch on the lab's own subject", recorded as `designed` rather than `automated` until the job opens an issue unaided. The tests pin the §4 gate (a cold run over 2026-09-01 to 2026-09-12 returns both arXiv:2609.02882 and arXiv:2609.07918), the four query-level facts of §2 by name and by search string so that dropping or rewording the query that catches Wang fails, fail-closed behaviour (an HTTP 503, malformed XML, an unexpectedly empty response and an unrecorded request each exit non-zero with the query named, and "queried, nothing new" is a distinct, exit-zero state), dedup against a fake issue list, version-suffix detection, the workflow's schedule and permissions, and that no author query is live: `au:Wang_B` returned nothing per §3 and the API was unreachable, so the fifteen author watches sit in `AUTHOR_WATCH_UNVERIFIED` behind a `--verify-authors` probe and none is enabled. **The fixtures in `tests/fixtures/literature_monitor/` are placeholders, not recordings.** The arXiv API answered HTTP 429 to every request for the whole session; a recording attempt with backoff ran eighteen minutes and landed nothing. The placeholder files carry the exact Atom shape and the identifiers, dates and authorship this brief records, a `PLACEHOLDER` marker file, and a README with the recording command; the gate tests therefore pass against the fixture *shape* and do not yet demonstrate that the live queries return those papers. That is the one thing still owed, and `test_fixtures_are_real_recordings_not_placeholders` skips loudly until it is paid. Dry run, no network: `python scripts/literature_monitor.py --dry-run --fixture tests/fixtures/literature_monitor --since 2026-09-01 --until 2026-09-12 --no-version-check`. Dry run against the live API: `python scripts/literature_monitor.py --dry-run`.
