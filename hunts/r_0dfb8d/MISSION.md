# MISSION: Hunt R-0DFB8D (#108): do SWE-bench leaderboard entries recount from their own archived logs?

Second instance of the reproduction procedure outside mathematics, paired with
issue #140 (soundcalc / zkVM). Same anatomy, different field: a public checker,
publicly archived accepted objects, a published number. Filed as a transfer
test.

## What this hunt is

`SWE-bench/experiments` is the archive of record for the SWE-bench leaderboard.
Each entry under `evaluation/verified/` publishes a resolved count in
`results/results.json`, and archives its per-instance evidence in a public S3
bucket, one directory per instance holding `eval.sh`, `patch.diff`,
`report.json` and `test_output.txt`. `report.json` carries both the verdict
(`resolved`) and the test results the verdict should follow from
(`tests_status.FAIL_TO_PASS` / `PASS_TO_PASS`, each split into `success` and
`failure`).

So two questions are answerable from the archive alone, and this hunt keeps
them apart:

* **RECOUNT (class A).** Count `resolved == true` across the archived
  per-instance reports; compare to the published `results.json`; reconcile the
  instance-id set against the 500-instance Verified split and account for the
  published `no_generation` and `no_logs` explicitly.
  Verdict: `match` / `mismatch` / `logs-unavailable`.
* **SELF-CONSISTENCY (class B).** For each instance, re-derive the verdict from
  the evidence in the same file: `resolved` should hold exactly when every
  required `FAIL_TO_PASS` and `PASS_TO_PASS` test is in `success` and both
  `failure` lists are empty. Verdict: `consistent` / `inconsistent`, with the
  disagreeing instance ids listed.

The two verdicts are never merged. A `match` says the arithmetic reproduces; it
says nothing about whether each verdict followed from its own evidence, and the
converse likewise.

## What this hunt is not

Out of scope by design, not by accident:

* **Re-running the Docker evaluation harness.** A different and far more
  expensive question (an environment reproduction rather than an arithmetic
  one); mixing them would confound both. It becomes a third hunt if phase one
  earns it.
* Any statement about a model's capability, any comparison between entries, and
  anything about contamination.
* Any characterisation of a team, an agent or a model, in any artifact
  including commit messages. Every statement is scoped to **the entry as
  archived**: "entry X's published resolved count does not recount from its own
  archived logs" is the sentence available; "team X overstated" is not, in any
  form.

The archive is fetched read-only. Nothing is submitted to any leaderboard, and
no agent sends anything anywhere.

## Prior art, and what it does not cover

OpenAI stopped reporting SWE-bench Verified on 2026-02-23, reporting that 59.4%
of 138 audited hard tasks had material test flaws. SWE-ABS (ICML 2026,
`OpenAgentEval/SWE-ABS`) strengthened 312 of 500 instances, killed 847
previously-passing patches, and moved the top entry from 78.80% to 62.20%.
Both attack the *benchmark*. Neither re-derives the *published per-entry
numbers from the archived logs*, which is what this hunt does.

```huntspec
id: swebench_recount
question: Do the resolved counts published in SWE-bench/experiments for six Verified leaderboard entries recount from the per-instance logs those entries archived, and does each per-instance verdict follow from the test results recorded in the same file?
frontier: 134 Verified entries at 2026-08-24; tags.checked is false for 96, true for 30, a non-boolean string for 6 and absent for 2; no entry carries checked true after 20250807_openhands_gpt5; per-instance report.json carries both the verdict and the test results it should follow from
proposed_attack: fetch every per-instance report.json for each unit from the public bucket, recount resolved and reconcile the instance set against the 500-instance split, then re-derive each verdict from its own tests_status and list every instance where the two disagree
dead_routes:
  - re-running the Docker evaluation harness, a different and much more expensive question, deliberately deferred
  - any comparison between entries, any statement about model capability, any contamination claim
  - anonymous ListBucket on the archive bucket, which returns 403 and cannot enumerate an entry's keys
required_oracles:
  - the archived per-instance report.json files at the public bucket, fetched unmodified, with their ETags and byte counts recorded
  - the entry's own results/results.json and results/resolved_by_repo.json as published in the repository at a pinned commit
  - the 500 instance ids and required test lists of the SWE-bench Verified split from the published parquet at a pinned dataset sha
  - exact integer arithmetic and set comparison
kill_conditions:
  - the per-instance logs for a unit are not retrievable, that unit is recorded logs-unavailable and no count is inferred for it
  - the instance-id set recovered for a unit does not reconcile with the published split and the difference cannot be accounted for by no_generation and no_logs
  - any step would require judging whether a patch is correct, which this hunt does not do
  - a planted fault fails to turn a verdict red, in which case the verdict is not evidence and is withdrawn
agents_may:
  - fetch and archive the public logs, recording URL, ETag and byte count per file
  - recount, reconcile and re-derive, and report per-instance disagreements by id
  - record the checked flag and the absence or presence of a stated harness version
agents_may_not:
  - post to SWE-bench maintainers, to any submitting team, or to any leaderboard
  - characterise a team, an agent or a model in any artifact, including commit messages
  - submit anything to any benchmark
  - merge the recount verdict and the self-consistency verdict into one
```

## How to re-run

```bash
python3 -m venv .venv && .venv/bin/pip install pyyaml pyarrow
.venv/bin/python hunts/r_0dfb8d/probe.py all
```

Roughly 4,000 HTTPS GETs, about 550 MB into `hunts/r_0dfb8d/data/cache/`
(gitignored), under ten minutes cold and instant afterwards. No Docker, no GPU,
no credentials.
