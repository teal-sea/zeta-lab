# Run record

## Baseline

Checkout `/home/user/zeta-lab-qrh-nonresidue`, branch `hunt/qrh-nonresidue`
from origin/main `ef4e0564`. `zeta.rigor.BACKEND` reported `python-flint`
with both backends available; python-flint 0.9.0.

## Budget, before execution

Unit timings from the pilot (run 1 below): exhaustive tables to 10^6 took
1.3 s, small-modulus generation to q = 2000 took 1.4 s, all Arb sections
under 2 s. Tables scale roughly linearly (10^7: about 15 to 20 s) and the
generation table roughly quadratically in q (10^4: about 35 s). Estimate for
the full run: about 1 CPU-minute, under 1 GB, one process. Well inside the
60 CPU-minute allocation, so no checkpointing.

## Runs

```runmanifest
id: qrh_nonresidue-2026-10-08-pilot
hunt: qrh_nonresidue
started: 2026-10-08T11:18Z
finished: 2026-10-08T11:21Z
ran:
  - PYTHONPATH=. .venv/bin/python hunts/qrh_nonresidue/verify.py --table-limit 1000000 --qmax 2000 --out <scratchpad>/v_small.json
outcome: first attempt stopped on an assertion because OEIS A002230 lists p = 2 with g = 1; after skipping p = 2 every section passed and fixed the unit timings above
artifacts:
  - none in the repository (scratchpad output only)
```

```runmanifest
id: qrh_nonresidue-2026-10-08-full-attempt
hunt: qrh_nonresidue
started: 2026-10-08T11:31Z
finished: 2026-10-08T11:31Z
ran:
  - /usr/bin/time -v .venv/bin/python hunts/qrh_nonresidue/verify.py --table-limit 10000000 --qmax 10000
outcome: did not start, /usr/bin/time is absent in this container (exit 127); no numbers were produced or used
artifacts:
  - none
```

```runmanifest
id: qrh_nonresidue-2026-10-08-full
hunt: qrh_nonresidue
started: 2026-10-08T11:32:32Z
finished: 2026-10-08T11:33:24Z
ran:
  - PYTHONPATH=. .venv/bin/python hunts/qrh_nonresidue/verify.py --table-limit 10000000 --qmax 10000
outcome: all assertions passed; 52.5 s wall, 52.2 CPU-seconds, peak resident memory 667 MB; closed-form margins positive, tables to 10^7 within every bound, ablation slopes 7.9995, 11.9996, 15.9997
artifacts:
  - hunts/qrh_nonresidue/verification.json
```

```runmanifest
id: qrh_nonresidue-2026-10-08-full-final
hunt: qrh_nonresidue
started: 2026-10-08T11:51:01Z
finished: 2026-10-08T11:51:52Z
ran:
  - PYTHONPATH=. .venv/bin/python hunts/qrh_nonresidue/verify.py --table-limit 10000000 --qmax 10000
outcome: rerun after adding the quartic-kernel constant section; all assertions passed, 50.8 s wall, 50.5 CPU-seconds, 667 MB; every earlier number reproduced
artifacts:
  - hunts/qrh_nonresidue/verification.json
```

```runmanifest
id: qrh_nonresidue-2026-10-08-tests
hunt: qrh_nonresidue
started: 2026-10-08T11:40Z
finished: 2026-10-08T11:41Z
ran:
  - PYTHONPATH=. .venv/bin/python -m pytest -q -n0 hunts/qrh_nonresidue/
outcome: 15 passed in 2.4 s (later grown to 19 tests: explicit-formula normalisation, residue formula for two characters, quartic constant)
artifacts:
  - hunts/qrh_nonresidue/test_qrh_nonresidue.py
```

```runmanifest
id: qrh_nonresidue-2026-10-08-governance
hunt: qrh_nonresidue
started: 2026-10-08T11:45Z
finished: 2026-10-08T11:50:47Z
ran:
  - pytest -q -n0 tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py tests/test_huntspec.py tests/test_hunt_numbering.py tests/test_contribution_check.py hunts/qrh_nonresidue/
outcome: 55 passed, 1 failed; MISSION.md cited the unmerged docs page by its bare number, which the numbering guard rejects; the citation was reworded and the set rerun
artifacts:
  - none
```

```runmanifest
id: qrh_nonresidue-2026-10-08-governance-rerun
hunt: qrh_nonresidue
started: 2026-10-08T11:52Z
finished: 2026-10-08T11:54:11Z
ran:
  - pytest -q -n0 tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py tests/test_huntspec.py tests/test_hunt_numbering.py tests/test_contribution_check.py hunts/qrh_nonresidue/
  - .venv/bin/python scripts/make_context.py --check
outcome: 60 passed in 131 s; CONTEXT.md up to date
artifacts:
  - none
```

```runmanifest
id: qrh_nonresidue-2026-10-08-full-eleven-twelfths
hunt: qrh_nonresidue
started: 2026-10-08T12:03Z
finished: 2026-10-08T12:04:05Z
ran:
  - PYTHONPATH=. .venv/bin/python hunts/qrh_nonresidue/verify.py --table-limit 10000000 --qmax 10000
outcome: rerun after the lead's citation correction added Theorem 1(d) for the Oct 5 paper's 11/12 half-plane; margin 0.169438807002 at L = 2, all other numbers unchanged; 53.9 s, 667 MB
artifacts:
  - hunts/qrh_nonresidue/verification.json
```

## Inputs fetched from outside

OEIS b-files A000229, A002229, A002230 and A014233, downloaded from oeis.org
on 2026-10-08 into `oeis/` (blank lines removed). Every value used is
recomputed by `verify.py` before it is compared with a bound, so the files
are inputs to a check, not trusted data.
