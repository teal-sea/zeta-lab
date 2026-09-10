# claim_halflife: run manifests

```runmanifest
id: claim_halflife-2026-09-09-corpus
hunt: claim_halflife
started: 2026-09-09T23:20-05:00
finished: 2026-09-09T23:40-05:00
ran:
  - git rev-parse --is-shallow-repository
  - git fetch --unshallow origin
  - .venv/bin/python hunts/claim_halflife/corpus.py
  - .venv/bin/python hunts/claim_halflife/classify.py
  - .venv/bin/python hunts/claim_halflife/controls.py
  - .venv/bin/python hunts/claim_halflife/depth.py 100 262 500 800
outcome: the container's checkout was shallow at 262 commits against 1084 and nothing announced it; on the full history 22 of 95 case-log entries were never touched again, against 29 at the container's own depth and 91 at depth 100
artifacts:
  - hunts/claim_halflife/artifacts/corpus.json
  - hunts/claim_halflife/artifacts/classified.json
  - hunts/claim_halflife/artifacts/controls.json
  - hunts/claim_halflife/artifacts/depth.json
```

```runmanifest
id: claim_halflife-2026-09-10-ladders
hunt: claim_halflife
started: 2026-09-09T23:45-05:00
finished: 2026-09-10T00:30-05:00
ran:
  - .venv/bin/python hunts/claim_halflife/lesion.py
  - .venv/bin/python hunts/claim_halflife/lesion2.py
  - .venv/bin/python hunts/claim_halflife/lesion3.py
outcome: of 25 (hunt, test) pairs that can be scored, 19 defend at least one number against a 10 percent mutation and 8 are byte-pinned; 6 read none; the first two ladders are kept because each measured the instrument rather than the tree, the first by mutating one leaf and the second by mutating only the first of up to thirty-seven artifacts a test names
artifacts:
  - hunts/claim_halflife/artifacts/lesion.json
  - hunts/claim_halflife/artifacts/lesion2.json
  - hunts/claim_halflife/artifacts/lesion3.json
```

```runmanifest
id: claim_halflife-2026-09-10-blind-audit
hunt: claim_halflife
started: 2026-09-10T00:10-05:00
finished: 2026-09-10T00:40-05:00
ran:
  - .venv/bin/python hunts/claim_halflife/make_audit_sample.py
  - a blind classification by a separate agent, with the key moved out of the repository before it ran
  - .venv/bin/python hunts/claim_halflife/score_audit.py <key> <audit>
  - .venv/bin/python hunts/claim_halflife/classify2.py
  - .venv/bin/python hunts/claim_halflife/make_audit_sample2.py <key2>
outcome: the audit agreed with the classifier on 16 of 30, precision 0.40 and recall 0.55 on a balanced sample, so the correction rate is withdrawn; two structural defects named and repaired; re-scoring against the same rows reaches 21 of 30, which is fitted rather than measured, and a disjoint sample of thirty went to a second blind audit
artifacts:
  - hunts/claim_halflife/artifacts/audit_sample.json
  - hunts/claim_halflife/artifacts/audit_score.json
  - hunts/claim_halflife/artifacts/classified2.json
  - hunts/claim_halflife/artifacts/audit_sample2.json
```

## Notes

- **The ladder broke the tree while measuring it.** Its first version restored
  mutated artifacts with `git checkout --`; a concurrent `git` in the same
  working tree made one restore fail with exit 128 and left a mutated artifact
  behind. The rule was already in the operating playbook. It is now obeyed:
  original bytes in memory, and the restore is asserted to round-trip.
- **The key was moved out of the repository before the blind audit ran**, not
  merely withheld in the prompt, because an agent with a shell can read a file
  it is told not to read.
- `classify.py` is kept exactly as it was. A classifier that scored near chance
  is evidence about how this kind of measurement fails, and deleting it would
  remove the only record of that.
