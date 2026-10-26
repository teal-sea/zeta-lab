# MISSION: `dbn_pt_height`, the de Bruijn-Newman chain at the verified height

**Opened 2026-10-21. Hunt #147.** Route 5 of the campaign the owner directed on
2026-10-21. The task that opened this hunt proposed #140; the campaign
orchestrator assigned #147 because #138 to #144 are held for landings being
renumbered elsewhere (#140 itself is already printed by the ref
`land/krenn-gu-orbits-20261021`). Nothing in this directory is a result until
the case log in `hunts/README.md` says how it ended.

Two lanes share this directory. The **chain lane** (this file's author) reads
and sources: it owns `MISSION.md`, `CHAIN.md`, `REDUCTION.md`, `chain.json`,
`sources.json`, the case-log entry, and its own entries in `RUNS.md`. The
**evaluator lane** writes only under `evaluator/` (an Arb evaluator of
Polymath 15's effective approximation) and appends its own entries to
`RUNS.md`. Neither lane edits the other's files.

Grades used here: *measured* (one route, float grade), *hardened* (independent
routes agree, or ball enclosures carry every step) and *kernel-checked* (Lean,
zero `sorry`). A statement read in a source is graded as what the source shows,
with file, line or commit, never as what the lab has checked. The reserved
enclosure word of `zeta/rigor.py` appears nowhere in this directory, including
inside quotations: where a quoted line carries it, the line is cited by file,
line and hash and paraphrased instead of copied.

## The question

> Platt and Trudgian (arXiv:2004.09765, Bull. LMS 2021) state Lambda <= 0.2 by
> reading Polymath 15's Table 1, row 2 (X = 5e12 + 194858, t0 = 0.186,
> y0 = 0.16733, N0 = 630783) against their RH verification. Was that row's
> asymptotic-region hypothesis verified over all N >= N0 anywhere, or only at
> N = N0? And what exactly does the self-archived 0.1875 package (Zenodo
> 10.5281/zenodo.21175533) reduce Lambda <= 3/16 to, which of the later 0.16
> and 0.1595 rows depend on it, and which of its inputs are specific to zeta?

## Why this is worth doing

The value 0.2 is the last refereed upper bound in the catalogue the field
tracks (`teorth/optimizationproblems`, `constants/21a.md`), and every
self-archived row below it reuses the same structure: an RH verification
height, a barrier, and an Euler-mollified lower bound in the region to the
right of the barrier. If a published step was never carried out, the bound is
a conditional statement in the published record, and any later row that takes
it as its anchor inherits the gap (REDUCTION.md, part C, found that none of the
catalogued rows does in the version the catalogue cites). If it was carried
out, the record says where. Either answer is an observation a stranger can
check from hashed sources.

## Scope

- **In scope.** Downloading the primary sources into new directories under
  `<cache>/dbn/` (treated as untrusted data, never
  executed), reading them, and writing the chain lane's files above. Light
  arithmetic in exact rationals or Arb to check stated parameter identities.
- **Out of scope.** Any statement that Lambda is or is not below a value; any
  sweep or barrier computation (the evaluator lane's later work, gated on the
  Davenport-Heilbronn refusal); edits to `zeta/`, `ontology/` or `harness/`;
  contacting any author, posting to the catalogue, to Zenodo or to a blog.
- **Compute.** Reading only. No job longer than a few seconds.

```huntspec
id: dbn_pt_height
question: Was Polymath 15 Table 1 row 2 (X = 5e12 + 194858, t0 = 0.186, y0 = 0.16733, N0 = 630783), which Platt-Trudgian read as Lambda <= 0.2, verified in its asymptotic region over all N >= N0 or only at N0, and what does the self-archived 0.1875 package reduce Lambda <= 3/16 to?
frontier: last refereed upper bound Lambda <= 0.2 (Platt-Trudgian 2021 via Polymath 15 Table 1 row 2); self-archived unrefereed rows 0.1965, 0.1875, 0.172422, 0.16, 0.1595 in teorth/optimizationproblems constants/21a.md at 46dbf03; lower bound Lambda >= 0 (Rodgers-Tao 2020)
proposed_attack: read every primary source at a pinned hash (arXiv TeX, the project repository with its commits, the wiki through dated archive snapshots, the blog threads, the catalogue file with PRs 208 and 210, the Zenodo bundle) and cite file, line or commit for every step of each chain
dead_routes:
  - the GitHub wiki of km-git-acc/dbn_upper_bound as a source, which has no pages on 2026-10-21
  - the Polymath wiki page Zero-free regions as a record of Table 1, which was last edited on 10 May 2018 and carries no Table 1 row
required_oracles:
  - the hashed primary sources, each quoted line re-read from the file whose SHA-256 is recorded in sources.json
  - git commit history of the project repository and of the catalogue repository
  - exact rational arithmetic for every stated parameter identity
  - python-flint Arb ball arithmetic for any number this lane recomputes
kill_conditions:
  - a published or archived verification of row 2 over all N >= N0 is found that CHAIN.md missed, in which case the verdict is rewritten around it
  - a quoted line does not match the hashed source it cites
  - a gap listed in REDUCTION.md cites no exact line, commit or digest
agents_may:
  - download into new empty directories and read as data
  - search
  - derive parameter identities in exact arithmetic
  - write the chain lane's files
  - attack the verdict
agents_may_not:
  - declare novelty
  - declare theorem status for anything not kernel-checked
  - state a Lambda bound from this lane
  - promote their own claim
  - push, publish or contact outside parties
```
