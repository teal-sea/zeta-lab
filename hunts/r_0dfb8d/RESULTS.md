# RESULTS: Hunt R-0DFB8D (#108): the recount reproduces; the evidence is not always there to recount

Read 2026-08-24. `SWE-bench/experiments` pinned at commit
`1faa91cade0562ba62b66c1c99e71f7b72d96f13`; split ids from
`princeton-nlp/SWE-bench_Verified` at dataset sha
`c104f840cc67f8b6eec6f759ebc8b2693d585d4a` (sha256 of the sorted 500 ids:
`fad0fdea4fc2315e…`); logs from `s3://swe-bench-submissions` by anonymous
HTTPS GET, ETag and byte count recorded per file in `data/fetch_manifest.json`.

Labels are Hunt #80's: **VERIFIED** = re-derived here from the pinned
artifacts; **REPORTED** = stated by the archive and taken as given;
**INFERRED** = our reading of what a measurement means.

Every statement below is scoped to **the entry as archived**. Nothing here is a
statement about a team, an agent or a model, and nothing here bears on RH
(`docs/08`).

## The headline

**The published resolved counts recount exactly, wherever the logs exist.** Five
of the six preregistered units reproduce to the integer, and each also
reproduces across all twelve per-repository sub-counts. Across 2,484
re-derived per-instance reports, **zero** disagreed with the verdict recorded in
the same file. The interesting result is the other class, as the prior
expected: **the evidence is not uniformly retrievable**. One preregistered unit
and, on a three-key probe, fifteen of the archive's 134 entries answer no
per-instance report at the documented location at all.

## The table

| unit | `tags.checked` | published `resolved` | A: recount | A verdict | B: reports re-derived | B verdict | per-repo cross-check |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `20240402_sweagent_gpt4` | true | 112 | n/a | **logs-unavailable** | 0 | not-run | 0/12 (no logs) |
| `20241029_OpenHands-CodeAct-2.1-sonnet-20241022` | true | 265 | 265 | **match** | 493 | consistent | 12/12 |
| `20250807_openhands_gpt5` | true | 359 | 359 | **match** | 498 | consistent | 12/12 |
| `20250902_atlassian-rovo-dev` | false | 384 | 384 | **match** | 500 | consistent | 12/12 |
| `20251127_openhands_claude-opus-4-5` | key absent | 388 | 388 | **match** | 498 | consistent | 12/12 |
| `20251215_livesweagent_claude-opus-4-5` | false | 396 | 396 | **match** | 495 | consistent | 12/12 |
| `20250805_openhands-Qwen3-Coder-480B-A35B-Instruct` *(supplementary)* | false | 348 | n/a | **logs-unavailable** | 0 | not-run | 0/12 (no logs) |

VERIFIED throughout. The supplementary unit was added after the preregistered
six, once the archive-wide probe showed a 2025 entry answering none of three
probe keys; it was swept over all 500 documented keys so that the
`logs-unavailable` verdict rests on 500 requests rather than 3.

## What each column means, and what it does not

**A = match** means: for every one of the 500 split instance ids, the archived
`report.json` was fetched where it existed, `resolved == true` was counted, and
the total equalled the published integer. It does **not** mean the evaluation
was correct, that the patch was correct, or that re-running the harness would
reproduce it. It means the published number is the number its own archived
evidence contains.

The per-repo column is a second, finer published artifact
(`results/resolved_by_repo.json`) carrying the same claim at 12-way grain. One
aggregate agreement can come from two errors cancelling; twelve simultaneous
per-repo agreements are much harder to get by cancellation. All five recountable
units agree on all twelve, and on all twelve repository totals against the split
(VERIFIED).

**B = consistent** means: for each instance, `resolved` was compared against the
rule the benchmark states: every required `FAIL_TO_PASS` and `PASS_TO_PASS`
test of that instance present in `success`, both `failure` lists empty, with the
required test lists taken from the split rather than from the entry. 2,484
reports, 0 disagreements (VERIFIED). No entry examined records a verdict its own
recorded tests do not support. Not one instance had a required `FAIL_TO_PASS`
test missing from both the success and failure lists.

## The check can fail: four planted faults, four reds

A check that cannot fail is not a check, so the two verdicts were run against a
lesioned copy of one unit's archive (`probe.py control`, results in
`data/control.json`). Baseline `20250902_atlassian-rovo-dev`: A match, B
consistent.

| planted fault | expected | observed |
| --- | --- | --- |
| flip one `resolved` false → true | A mismatch (+1), B inconsistent | A **mismatch**, B **inconsistent (1)** |
| add a `PASS_TO_PASS` failure under `resolved: true` | B inconsistent, A unchanged | A match, B **inconsistent (1)** |
| drop the required `FAIL_TO_PASS` successes | B inconsistent, A unchanged | A match, B **inconsistent (1)** |
| remove one archived report file | A recount −1 → mismatch | A **mismatch** |

All four detected (VERIFIED). The two classes also stayed separated under
lesion, which is the property the mission asked for: two of the four faults move
B and leave A alone.

## The findings that are not "match"

### 1. The logs are not uniformly there (VERIFIED)

A three-key probe (`probe.py availability`, one early / one middle / one late
instance id) across all 134 entries: **119 answer at least one probe key, 15
answer none.** Thirteen of those fifteen are dated 2024-07 or earlier; two are
dated 2025-08-05.

Two of the fifteen were swept exhaustively rather than probed:

* `20240402_sweagent_gpt4` (`tags.checked: true`, published `resolved: 112`,
  published `with_logs: 472`): **0 of 500** documented report keys return 200;
  all 500 return 404. Its `all_preds.jsonl` and its `trajs/` objects *are*
  retrievable, so the entry is archived, but not with the per-instance
  evaluation evidence at the documented location.
* `20250805_openhands-Qwen3-Coder-480B-A35B-Instruct` (published `resolved: 348`,
  `no_generation: 0`, `no_logs: 1`): **0 of 500** report keys, and
  `all_preds.jsonl` returns 404 as well.

INFERRED, and worth stating as inference rather than fact: for the 2024 cohort
the natural reading is a format or migration gap (the current per-instance
`report.json` shape postdates those submissions), not a claim that evidence was
withheld. That reading does not extend to the 2025-08 pair, which are contemporary
with entries whose logs are fully present. This hunt does not adjudicate why.

Nothing here can distinguish "no object exists" from "the object exists under a
key we did not guess", because **anonymous `ListBucket` on that bucket returns
403** (see §3). Six alternative key shapes were probed by hand for the 2024 unit
(`logs/<id>.json`, `logs/<id>.log`, `logs/<id>.eval.log`, `logs.zip`,
`results/report.json`, the `evaluation/`-prefixed path) and all missed.

### 2. `no_logs: 0` is published where an instance has a prediction and no log (VERIFIED)

The published record accounts for absent evidence with two fields. Because
`all_preds.jsonl` is archived beside the logs, which field a missing report
belongs to is checkable (`probe.py preds`, `data/preds.json`).

| unit | missing reports | of those: no prediction | empty patch | **non-empty prediction, no log** | published `no_generation` / `no_logs` |
| --- | --- | --- | --- | --- | --- |
| `20241029_OpenHands-CodeAct-2.1…` | 7 | 1 | 5 | 1 | 6 / 1, reconciles |
| `20250807_openhands_gpt5` | 2 | 1 | 0 | **1** | 1 / **0** |
| `20250902_atlassian-rovo-dev` | 0 | 0 | 0 | 0 | 0 / 0, reconciles |
| `20251127_openhands_claude-opus-4-5` | 2 | 0 | 1 | **1** | **2** / 0 |
| `20251215_livesweagent_claude-opus-4-5` | 5 | n/a | n/a | n/a | 4 / 1, `all_preds.jsonl` is 404 |

For `20250807_openhands_gpt5`, the most recent entry the maintainers mark
`checked: true`, instance `sphinx-doc__sphinx-8475` has a non-empty archived
prediction and no archived report, while the entry publishes `no_logs: 0`. For
`20251127_openhands_claude-opus-4-5` the two missing instances are one empty
patch and one non-empty prediction without a log, published as
`no_generation: 2, no_logs: 0`.

The interpretation of the two fields is ours (INFERRED); the counts are not
(VERIFIED). **Neither discrepancy changes a resolved count**, since an instance
with no report is counted resolved by nobody. It is an accounting field that does
not reconcile, not a count that does not.

### 3. The archive's own README overstates what access requires (VERIFIED)

`SWE-bench/experiments`' README says *"You need an AWS account to download the
logs and trajectories"*. Measured today: `GetObject` under the `verified/`
prefix succeeds anonymously (this hunt fetched 4,000-odd objects, 31 MB of
reports, with no credentials, and `analysis/download_logs.py` itself configures
`signature_version=UNSIGNED`), while `ListObjectsV2` on the bucket returns **403
Access Denied**, and a GET outside the served prefixes returns 403 rather than
404.

That asymmetry is the operationally important part and it cuts against
reproduction: **an outside reader can retrieve any key they can name and cannot
discover which keys exist.** Every recount here therefore had to name its own
500 keys from the split, and every absence is "absent at the documented key",
never "absent from the bucket".

### 4. `tags.checked` is not a boolean in six entries (VERIFIED)

Across 134 entries: **30 `true`, 96 boolean `false`, 6 carrying the string
`"false (See README.md for info on how to get your results verified)"`, and 2
with no such key.** The most recent entry marked `true` is
`20250807_openhands_gpt5`; every one of the 21 entries dated after it is `false`,
the string, or absent.

The six string-valued flags matter for a mechanical reason rather than a
rhetorical one: `"false (…)"` is a **truthy** string in Python, JavaScript and
Ruby alike, so any consumer writing `if tags["checked"]` reads six unchecked
entries as checked. This hunt's counts key off `is True` / `is False`, which is
why its 96/30/6/2 differs from a naive 95/30/9 reading of the same files.

### 5. No entry states the harness version that produced its number (VERIFIED)

None of the 134 entries' `metadata.yaml` / `metadata.yml` / `README.md` matches
`/swebench[=< ]*\d|harness version|sweb\.eval|swebench_?version|harness[: ]+\d/i`.
`swebench` on PyPI is at 5.0.2. So the archive records *which* number an entry
published and does not record *which evaluator produced it*; two entries a year
apart are not, from the record alone, known to have been graded by the same
code. This is a scope caveat on every "match" above: the recount shows the number
agrees with its own logs, not that the logs came from a stated version of the
grader.

### 6. One retrieval bug was ours, not the archive's (VERIFIED)

The first availability pass reported 16 unreachable entries. One,
`20250616_Skywork-SWE-32B+TTS_Bo8`, was an artifact of not percent-encoding the
`+` in the entry name: a bare URL reads it as a space. Fixed in `probe.py`
(`s3()`), rerun, 15. Recorded because a reproduction procedure that reports the
target's absence when the fault is in its own fetcher is the exact failure mode
this class of hunt exists to catch, and it caught it here on itself.

## The transfer measure

The mission's transfer measure is **hand interventions per unit**, with the
procedure judged not to have crossed the domain above about two. Interventions
that required a human-equivalent judgment call rather than mechanical work:

1. the archive README's stated AWS-account requirement is wrong in one direction
   and incomplete in the other, so the access model had to be established by
   probe (§3), and the bucket name read out of `analysis/download_logs.py`;
2. anonymous listing being denied forced key enumeration from the split, which
   changed the shape of every absence claim in this document;
3. the 2024 cohort's missing logs needed six by-hand alternative key shapes
   before "absent at the documented key" was a fair statement;
4. `tags.checked` needed a type check rather than a truth check (§4).

Four interventions across seven units, **0.57 per unit**, and none of the four
was unit-specific: each was paid once and then held for every unit. Under the
mission's threshold. The `fetch_upstream.sh` / `compare_expected.py` shape from
`main` carried over with no abstraction added, as the roadmap non-goal requires:
`probe.py` is one file with six stages and no framework, and nothing was written
outside this hunt directory except the case-log line and the ledger append the
brief mandates.

## What could not be settled at this cost

* **Whether the archived logs are themselves faithful.** Everything here reads
  the archive against itself. A `report.json` that misrecorded its own test run
  would be self-consistent and would recount perfectly. Closing that needs the
  Docker harness re-run, explicitly out of scope.
* **Whether the missing objects exist under keys we did not guess.** Blocked by
  the 403 on listing (§3), not by budget.
* **Whether the string-valued `checked` flags are read as truthy by any live
  consumer** (the leaderboard site, downstream tooling). Establishing that would
  mean reading code this hunt did not fetch.
* **The 2024 cohort's intent.** §1 gives the format-migration reading as
  inference and does not test it.

## Disclosure

Two things in this document are reportable to the archive's maintainers as
plain fact with a reproducer: the six non-boolean `checked` values (§4) and the
`no_logs` accounting cases (§2), plus, as a documentation correction, the AWS
account claim (§3). Per the mission, **no agent sends any of it anywhere.** The
reproducer is `probe.py`; the decision to file is the operator's.

## Closing the loop: nothing in the ledgers asked for this

The brief's standing instruction is to record this run's outcome in the
`harness/departments/` ledger the task came from. This task came from issue
\#141, not from a ledger-returned item, and no ledger item corresponds to it:
`harness.review.standing_reasons` currently asks for blind attacks on
`rf-c003-window` and `k2-far-constant-depth1`, `harness.guards.undemonstrated`
asks for a mutant against `tests/test_doors.py`, and
`harness.graveyard.unguarded` is empty. None is this hunt's subject. **No entry
was appended**, because recording an attack outcome against a claim this hunt
did not attack would put a false record in the ledger, and the ledger is only
worth what its entries are true about. The three open items above are named here
so the omission is checkable rather than silent.

## Loose threads

* **The 2025-08 pair with no retrievable evidence.** Two entries dated
  2025-08-05 publish resolved counts of 258 and 348 and answer neither
  `logs/<id>/report.json` nor `all_preds.jsonl` at the documented keys, unlike
  their contemporaries. *Why it might matter:* the recount procedure is only as
  good as the archive's retention, and these are recent enough that a format
  migration does not explain them. *First step:* sweep all 500 keys for the
  30B entry as was done for the 480B one, and probe `trajs/` and
  `results/results.json` keys for both, to distinguish "not uploaded" from
  "uploaded elsewhere".
* **`20251215_livesweagent_claude-opus-4-5` archives 495 reports and no
  `all_preds.jsonl`.** *Why it might matter:* without predictions the
  `no_generation` / `no_logs` split cannot be reconciled from outside for the
  archive's newest entry, which is the one most likely to be cited. *First
  step:* probe the alternate prediction key shapes (`preds.json`,
  `all_preds.json`) and check whether recent entries as a class stopped
  archiving predictions.
* **`20241002_lingma-agent_lingma-swe-gpt-7b` and `20250616_Skywork-SWE-32B`
  answer some probe keys and not others.** *Why it might matter:* partial
  archives are the case where a three-key probe is least informative, and
  `lingma-swe-gpt-7b` publishes `no_generation: 86`, so partial absence may be
  entirely expected. *First step:* full 500-key sweep on both, then the §2
  prediction reconciliation.
* **The `validation/` folder.** The archive also publishes validation logs for
  the dev and test splits, never read here. *Why it might matter:* it is the
  provenance of the split's required-test lists, which this hunt used as an
  oracle without checking. *First step:* recount the split's `FAIL_TO_PASS`
  lists against those validation logs.
* **The Docker re-run.** Out of scope by design and named in the mission as a
  possible third hunt; `swebench/sweb.eval.*` images are public and the cost is
  an environment reproduction, not an arithmetic one.

## The doors

Not applicable in the sense the repo-wide rule intends: this hunt measures no
ceiling and optimises nothing, so it has no active constraints, no frozen
constants and no configuration-vs-information ceiling to report. The nearest
honest analogue is §3: the binding constraint on *any* outside reproduction of
this archive is that keys can be fetched but not enumerated, and unfreezing it
is a bucket-policy decision belonging to its maintainers, not a parameter here.
