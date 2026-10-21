# RUNS: `dbn_pt_height`

Each lane appends its own entries; neither edits the other's. Timings are wall
clock on the shared swarm box (32 vCPU), single process, under whatever load
the other workflows were putting on it; the 1-minute load average at launch is
recorded with each entry because it inflates every number here.

## Chain lane (`MISSION.md`, `CHAIN.md`, `REDUCTION.md`, `chain.json`, `sources.json`)

### C1. Sourcing and reading (2026-10-21 16:23 to 17:23 UTC)

- Estimate before starting: reading and downloads only, no numerics; under one
  CPU-minute in total and well under 1 GB of memory. The largest single object
  was the 196150822-byte Zenodo archive (about two minutes to fetch; extracted
  to about 208 MB). No job was detached and nothing ran longer than a few
  seconds, so no checkpointing was needed.
- Every download went into a new, empty directory under
  `/home/thomas/.cache/zeta-lab/dbn/` whose name starts `chain-`; nothing there
  was executed. Archives were listed for symlinks and parent paths before
  extraction. Each file's URL, SHA-256, size and retrieval time is in
  `sources.json`.
- `test_chain.py` re-reads all 129 quotations from those hashed bytes and runs in
  about 7 s on one core.

```runmanifest
id: dbn_pt_height-2026-10-21-chain
hunt: dbn_pt_height
started: 2026-10-21T16:23Z
finished: 2026-10-21T17:23Z
ran:
  - curl downloads of the arXiv sources, the Polymath wiki snapshots, the blog threads, the GitHub API records and the Zenodo files into new directories under /home/thomas/.cache/zeta-lab/dbn
  - git clone of km-git-acc/dbn_upper_bound and teorth/optimizationproblems, and a no-checkout clone of the 463464q435q43 fork exported at its two pinned commits
  - a quotation builder run with the venv python in isolated mode from the scratchpad, writing chain.json and sources.json
  - .venv/bin/python -m pytest -q -n0 hunts/dbn_pt_height/test_chain.py
artifacts:
  - hunts/dbn_pt_height/MISSION.md
  - hunts/dbn_pt_height/CHAIN.md
  - hunts/dbn_pt_height/REDUCTION.md
  - hunts/dbn_pt_height/chain.json
  - hunts/dbn_pt_height/sources.json
  - hunts/dbn_pt_height/test_chain.py
outcome: row 2's asymptotic-region hypothesis was found verified only at N = N0 in the Polymath record, and the 0.16 and 0.1595 rows were found to depend on the 0.1875 reduction, whose zeta-specific inputs are the verification height and the Euler-mollified lower bound
```
