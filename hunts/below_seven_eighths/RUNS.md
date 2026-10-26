# RUNS.md: hunt #136 `below_seven_eighths`

Created 2026-10-26, when the lane was resumed in place by the owner's decision of that day.
The first wave (2026-10-21) kept no RUNS.md. Its manifests are reconstructed here from what
the lane files record. A block copied from a lane file is marked as copied. A block written
on 2026-10-26 for a lane that embedded no manifest is marked *reconstructed*: its times come
from the lane page, a commit time or a file modification time (named in each block), its
`ran` list from the commands the page itself gives, and anything not recorded is said to be
unrecorded. No first-wave run was repeated to write this file.

Compute: every first-wave run was on the campaign box (`<box>`, 32 vCPU, 115 GiB). Apart from
the Lean lane (one build, 3:09:51 wall, 10.4 CPU-hours; LEAN.md section 1) each lane ran exact
arithmetic and tests on one core for well under a core-hour (inferred from the pages; no
lane timed itself). The caches the runs read (`<cache>/openai-math-adc7f124/paper.tex`,
`<cache>/followups/run-2026-10-21T1440Z/`) are outside the tree; `<cache>/qrh-build/` no longer
exists (LEAN.md, 2026-10-26 note).

## Files left uncommitted

None. The 2026-10-26 checkpoint commit found no file in the hunt directory over 10 MB
(the directory is 4.2 MB); no SHA-256 list is needed.

## First wave, 2026-10-21

Copied verbatim from `PROBE.md`:

```runmanifest
id: below_seven_eighths-2026-10-21-probe
hunt: below_seven_eighths
started: 2026-10-21T14:36Z
finished: 2026-10-21T15:28Z
ran:
  - .venv/bin/python hunts/below_seven_eighths/probe_table.py --paper --quick
  - .venv/bin/python hunts/below_seven_eighths/probe_table.py --paper
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_probe_table.py
  - planted-fault run of a scratch copy of probe_table.py with the Gram coefficient 1/k
outcome: priced the order-k template; k = 6 reproduces the paper and Liu; every order below 6 is cheaper in principle and none is available
artifacts:
  - hunts/below_seven_eighths/PROBE.md
  - hunts/below_seven_eighths/probe_table.py
  - hunts/below_seven_eighths/test_probe_table.py
```

Copied verbatim from `PROBE.md`:

```runmanifest
id: below_seven_eighths-2026-10-21-probe-repair-r1
hunt: below_seven_eighths
started: 2026-10-21T16:44Z
finished: 2026-10-21T17:41Z
ran:
  - .venv/bin/python hunts/below_seven_eighths/probe_table.py --paper
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_probe_table.py
  - planted-fault runs of the test file against scratch copies of PROBE.md and probe_table.py
  - curl of the arXiv HTML of 2306.11875v5 and the abstract of 1312.0568 into scratch, read as data
  - .venv/bin/python -m pytest -q -n0 -m "not slow" tests/test_huntspec.py tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py tests/test_doors.py
  - .venv/bin/python scripts/make_context.py --check
outcome: repaired the probe lane after verification; floor-bin convention made explicit with both walls, two-sided exact brackets added, two float-route defects fixed, grades and citations corrected
artifacts:
  - hunts/below_seven_eighths/PROBE.md
  - hunts/below_seven_eighths/probe_table.py
  - hunts/below_seven_eighths/test_probe_table.py
```

Copied verbatim from `PROBE.md`:

```runmanifest
id: below_seven_eighths-2026-10-21-probe-repair-r2
hunt: below_seven_eighths
started: 2026-10-21T22:00Z
finished: 2026-10-21T22:46Z
ran:
  - OMP_NUM_THREADS=1 .venv/bin/python -m pytest -q -p no:cacheprovider -n0 hunts/below_seven_eighths/test_probe_table.py
  - .venv/bin/python hunts/below_seven_eighths/probe_table.py --paper
  - scratch scripts for the relaxed ties, hunt 134's witness points, Liu's count equation and the cutting-plane brackets
  - WebFetch of the arXiv abstract and PDF of 1112.1650, decompressed with qpdf and its text extracted in scratch, read as data
  - planted-fault runs: page typos, a table line, a fraction swap and source mutants of the exact checker, all inside the test file
  - three scratch copies of the lane, each with one planted fault (a page fraction, a relaxed-tie hypothesis bound, the sign of a large-delta corner term), each run against the full test file
  - .venv/bin/python -m pytest -q -n0 -m "not slow" tests/test_huntspec.py tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py tests/test_doors.py
  - .venv/bin/python scripts/make_context.py --check
outcome: repaired the probe lane after the second verification; the k = 2 and 3 tie verdicts corrected with relaxed-tie points, the page's fractions, line numbers and tables tied to the computation, the exact checker fault-tested, wording and grades corrected
artifacts:
  - hunts/below_seven_eighths/PROBE.md
  - hunts/below_seven_eighths/probe_table.py
  - hunts/below_seven_eighths/test_probe_table.py
```

Copied verbatim from `LEAN.md`:

```runmanifest
id: below_seven_eighths-2026-10-21-lean-session1
hunt: below_seven_eighths
started: 2026-10-21T14:39Z
finished: 2026-10-21T18:06Z
ran:
  - scratch/setup.sh (clone of openai/math at adc7f124, elan toolchain v4.34.1, lake update, lake exe cache get), under the memory watchdog
  - scratch/build.sh (lake build OAI.NumberTheory.DirichletL.Nonvanishing, LEAN_NUM_THREADS=16)
  - scratch/post.sh (axioms, gate with three planted faults and a control, environment dump)
  - lean on scratch/BridgeEndpoint.lean, BridgeCentral.lean and their planted-fault copies
outcome: recorded by the second session from this run's evidence directory; the closure built with exit 0 in 11393 s, both 7/8 statements report only the three standard axioms, and the run was stopped by the campaign pause before it wrote its page
artifacts:
  - <cache>/qrh-build/evidence/20261021T143950Z/
  - <cache>/qrh-build/analysis/
  - hunts/below_seven_eighths/LEAN.md (sections 1 and 2)
```

Copied verbatim from `LEAN.md`:

```runmanifest
id: below_seven_eighths-2026-10-21-lean-session2
hunt: below_seven_eighths
started: 2026-10-21T21:22Z
finished: 2026-10-21T22:05Z
ran:
  - scratch/session2.sh evidence/20261021T2130Z-session2 (no-op lake build, axioms, gate, planted faults, bridges, environment dump), under the memory watchdog
  - scratch/closure_s2.py, levels.py, depth.py and rebuild.py on the import graph and the first session's build log
  - scratch/postprocess.py, census_downstream.py, targets_table.py and s2_tables.py on the session-two dump
  - scratch/textcensus.py on the census and on a census with one planted fake row
  - evalcheck.py comparing the four Lean evaluations with hunt 134's probe.py
  - grep over OpenAI's checkout for compensated_geometry, the other Parameters theorems and balancedExponent
outcome: every check of the first session reproduced with fresh logs, the dependency census located the geometry and row-count literals with their downstream reach, and the page was completed
artifacts:
  - hunts/below_seven_eighths/LEAN.md
  - <cache>/qrh-build/evidence/20261021T2130Z-session2/
  - <cache>/qrh-build/analysis-session2/
  - <cache>/qrh-build/analysis-session2-text/closure.txt
```

Reconstructed (lane page `FOLLOWUPS.md` lines 4 to 11 and `followups.json` `compiled_utc`, `repaired_utc`):

```runmanifest
id: below_seven_eighths-2026-10-21-followups
hunt: below_seven_eighths
started: 2026-10-21T14:36Z
finished: 2026-10-21T22:07Z
ran:
  - downloads of the public follow-ups (arXiv sources, GitHub READMEs and commits, the tracker catalogue and pull list) to <cache>/followups/run-2026-10-21T1440Z/, each hashed in followups.json
  - compilation of FOLLOWUPS.md and followups.json between 14:36Z and 15:10Z
  - repair passes r2 (15:52Z), r3 (16:41Z) and r4 (from 21:22Z, with a tracker re-check between 21:28Z and 21:38Z)
  - scratch checkers for identities X1 to X18, hashes and quotations (session scratch, swept; not in the tree)
outcome: reconstructed; the public frontier map and the tracker records below B_flat were recorded, the identities were checked in scratch only, and the open issues of section 13 were listed
artifacts:
  - hunts/below_seven_eighths/FOLLOWUPS.md
  - hunts/below_seven_eighths/followups.json
```

Reconstructed (`ASSEMBLY.md` line 107 for the start; `test_assembly.py` modification time for the finish, an upper bound):

```runmanifest
id: below_seven_eighths-2026-10-21-assembly
hunt: below_seven_eighths
started: 2026-10-21T14:36Z
finished: 2026-10-21T22:12Z
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_assembly.py
  - assembly.py solvers and citation check against the pinned paper.tex (exact commands not recorded)
  - the verifier round 1 repair, including planted code faults (ASSEMBLY.md section on repairs)
outcome: reconstructed; the exact model of the Part II assembly reproduces 7/8 and the stated margins under readings R1 and R2, and no improvement of the half-plane is claimed
artifacts:
  - hunts/below_seven_eighths/ASSEMBLY.md
  - hunts/below_seven_eighths/assembly.py
  - hunts/below_seven_eighths/test_assembly.py
```

Reconstructed (start not recorded; `ROWCOUNTS.md` and `test_rowcounts.py` modification times for the finish):

```runmanifest
id: below_seven_eighths-2026-10-21-rowcounts
hunt: below_seven_eighths
started: 2026-10-21 (time not recorded)
finished: 2026-10-21T17:44Z
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_rowcounts.py
  - rowcounts.py exact enumerations and the 98-snippet citation check (exact commands not recorded)
  - the repair after the independent verifier's review (ROWCOUNTS.md section 10)
outcome: reconstructed; none of nine recounts recovers anything at the paper's inputs, the floor rows were not recounted
artifacts:
  - hunts/below_seven_eighths/ROWCOUNTS.md
  - hunts/below_seven_eighths/rowcounts.py
  - hunts/below_seven_eighths/test_rowcounts.py
```

Reconstructed (start not recorded; `test_euler_step.py` modification time for the finish):

```runmanifest
id: below_seven_eighths-2026-10-21-eulerstep
hunt: below_seven_eighths
started: 2026-10-21 (time not recorded)
finished: 2026-10-21T22:45Z
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_euler_step.py (fast tier and the slow full ranges)
  - euler_step.py exact local computation and the 202-line citation check against paper.tex
  - two adversarial verifier rounds and their repairs (EULER_STEP.md, repair rounds)
outcome: reconstructed; Lemma 7.1 and its Gauss-sum inputs checked exactly on the stated ranges, with the rival table
artifacts:
  - hunts/below_seven_eighths/EULER_STEP.md
  - hunts/below_seven_eighths/euler_step.py
  - hunts/below_seven_eighths/test_euler_step.py
```

Reconstructed (commit times of `b6c4972a8` and `129c5fb7e`):

```runmanifest
id: below_seven_eighths-2026-10-21-referee
hunt: below_seven_eighths
started: 2026-10-21 (time not recorded)
finished: 2026-10-21T22:46Z
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/referee -m "not slow"
  - local_identity_pari.py, PARI/GP cyclotomic checks of Lemma 7.1, Lemma 4.2 and Equation (4.7)
  - the repair after the adversarial review (REFEREE_W1.md section 7)
outcome: reconstructed; code-disjoint exact check of the scalar Euler identity at the stated primes and boxes, committed in b6c4972a8 and repaired in 129c5fb7e
artifacts:
  - hunts/below_seven_eighths/referee/REFEREE_W1.md
  - hunts/below_seven_eighths/referee/local_identity_pari.py
  - hunts/below_seven_eighths/referee/test_local_identity_pari.py
  - hunts/below_seven_eighths/referee/disagreements.json
```

Reconstructed (commit time of `baa41597e`; `price.py` was modified again after that commit and the change was committed in the 2026-10-26 checkpoint):

```runmanifest
id: below_seven_eighths-2026-10-21-amplification
hunt: below_seven_eighths
started: 2026-10-21 (time not recorded)
finished: 2026-10-21T17:47Z
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/amplification/test_price.py
  - price.py exact LP and decision procedure on the bin rectangle, citation hashes
outcome: reconstructed; Lemma 17.6's sixth-power amplification priced as a door outside the assembly, with Guo's Hypothesis 11.1 written up; no improvement claimed
artifacts:
  - hunts/below_seven_eighths/amplification/LOSS_MAP.md
  - hunts/below_seven_eighths/amplification/guo_h11.md
  - hunts/below_seven_eighths/amplification/price.py
  - hunts/below_seven_eighths/amplification/test_price.py
```

## Resumed in place, 2026-10-26

```runmanifest
id: below_seven_eighths-2026-10-26-resume
hunt: below_seven_eighths
started: 2026-10-26T12:44Z
finished: 2026-10-26T13:16Z
ran:
  - git commit of the stalled lane files after the operator-detail scrub; git merge origin/main (hunts/README.md conflict resolved, both entries kept)
  - .venv/bin/python -m pytest -q -n0 tests/test_hunt_probe_discipline.py tests/test_hunt_numbering.py tests/test_docs_numbering.py tests/test_doors.py tests/test_hunt_doors.py tests/test_huntspec.py
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths (killed by its 1100 s timeout under a box load near 56, no result)
  - .venv/bin/python -m pytest -q -n0 -m "not slow" on each of the seven lane test files, one at a time (two failures inherited from the stalled state, then green after the repair below)
  - gh api reads of github.com/GTimG/QuasiRiemannTracker (pull list, PR files, main at 01c21abe) and a blobless clone with pull/63 to pull/79 heads, sources extracted to session scratch and deleted after reading
  - an import-closure script over each PR's Candidate.Main and pattern searches of its closure (session scratch, not kept)
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_followups_identities.py, and one planted-fault run against a mutated copy of followups.json
outcome: checkpoint committed and merged with main; two failures inherited from the stalled 2026-10-21 state were repaired for consistency (test_price.py and guo_h11.md still had the old D^(2a)/log D normalization that the uncommitted price.py had dropped; EULER_STEP.md's "all 32 inert ell" collided with the doc-sync pattern for the 616 count); the lane's slow tier was not run; X1 to X18 pinned by a test except X3, which the tree cannot pin; tracker PRs 63 to 79 read against the 13/15 floor model (all inside, inferred); live bar 0.8746075; disposition drafted in MISSION.md
artifacts:
  - hunts/below_seven_eighths/test_followups_identities.py
  - hunts/below_seven_eighths/FOLLOWUPS.md (section 14)
  - hunts/below_seven_eighths/MISSION.md (dated disposition section)
  - hunts/below_seven_eighths/LEAN.md (2026-10-26 note)
  - hunts/below_seven_eighths/RUNS.md
```

Tracker heads read on 2026-10-26 (PR, head commit, tree of the submission directory, head commit time):

```
63 52419a826d4a8465cdeb56aaa2d471c489221d1d d4d4860d11683915a3c357f63863e7d7bf6d19a2 2026-10-16T23:01:55-04:00
64 edbb22b1a080c961b19e438e9e8ce6d6b3842739 b0d9f04b4df4760128765a4d97f3b51bad830bd0 2026-10-17T10:15:08Z
66 c68a3b2ba5b28b9c9b4bf26966ed6ee04ffa29b9 bc0d103646a16771127b776112950f57a37654bb 2026-10-19T14:48:41+02:00
67 0db497edc397d7076b1652b060e49c76b683e901 4eeb21a6734b27741debdb7afcd0ac08af989391 2026-10-20T00:13:21Z
68 f07bb2418990a9976c0da5f65bb6a7a77da94c9a 18383359655ea9c6f1942658c0db4da5dcb156b8 2026-10-20T12:38:09-04:00
69 ac76d5ef6008d976a7b8f3c1d921af2317e79ce9 56039549fff3a07c3e0ab83e3264ad5ae498c35d 2026-10-21T10:04:51-06:00
70 8ee28f244ec11b180d09c9d3f92e34ee078c746a 0a07c961b4ed9bb9dd2a83bf4d642a2a452a3597 2026-10-23T09:36:09+02:00
71 17d05f9a81bbea54ae55597eb0a449b27e33a06d 67b0c380e185051078dd52736787c5656ee422b2 2026-10-24T19:36:49+05:30
72 2a4bdc15726d5724e86381e5d452e615e5b4cf5d a9f75bea43507ecb11193ef396309aaa191d3bff 2026-10-25T00:39:31Z
73 41ddc0ddea6b4de6829d8cc1f94afa4e22c748f3 d09eee018f93d7901b98aadba24af1067ed6b468 2026-10-25T07:14:06Z
74 bf20f0d362f941a544aca2e886ec41f77b191ea5 133f2a1904d9b99f1a2b8ab3c8642a306dffc1b9 2026-10-25T16:43:23+01:00
75 3b5057861b92296e62ea3fa28237d3d8f196b441 596d991ee516d77ef32a84aa55e1784e3fba7500 2026-10-26T00:39:51Z
76 2fd55e03fd33d0f181cdd74ab1bd0a87b949f53a f75ddc12b7174ef8856b7743cb9e603415e0ee9e 2026-10-26T01:20:52+01:00
77 3b5057861b92296e62ea3fa28237d3d8f196b441 596d991ee516d77ef32a84aa55e1784e3fba7500 2026-10-26T00:39:51Z
78 772f35e52abe164ccc127b6e3cd9c835128247df fa65f09c313b37aa5c0d235ed83e6eb432b7a55e 2026-10-26T09:01:37Z
79 3dcd2742e2a605f2f480e46b824cb695d3fc4863 4e751858ec91f3abac526f8fc836fdbd2ecbf413 2026-10-26T11:49:11Z
```

Tracker `main` at `01c21abe8547304d033798ae7e4752dba4038209` (committed 2026-10-26T01:30:16Z).
