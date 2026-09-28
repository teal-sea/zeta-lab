# Runs

**Current status (2026-09-28): the Lean kernel build of the c = 2330/10^6 candidate
has been run and passed, locally by this laboratory, on Modal.** Build receipts,
the complete final log, the six raw axiom lines and provenance are in
`evidence/` (start at `evidence/README.md`). It is not external review and not a
Palomar registration. The 2026-09-05 entry below is kept as written and says
"Lean build pending" because that was true on that date; see the 2026-09-28
addendum at the end.

## 2026-09-05: a stronger four-point proof candidate

The selected exact parameters are `c = 2330/1000000`, `p = 2500`, `m = 432`.
The candidate formula is

    (14400000 * H - 17240) / 14366681

where `H = 3/2 - cot(1/sqrt(2))/sqrt(2)`. At 70 decimal digits:

    registered: 0.6728470197666888276075893668514985159475049461800387554234098564564666
    candidate:  0.6728603588388666595002053005539310516983709467912736933872256038932257
    difference: 0.0000133390721778318926159337024325357508660006112349379638157474367591

The exact rational search closes. The separate preflight reads the generated
Lean, not the search tree: 1516 cell lemmas, 11863 leaves, 220 chunks,
13 boxes, 64 dispatch cases, zero reported problems. This is not a completed
Lean verification. The former `FOUR-POINT.md` already tabulated this floor;
the new work here is taking the stronger floor toward a full kernel build.

Other exact trees closed at `(c*10^6,p) = (2170,2750)` and `(2180,2750)`.
They imply candidate constants `0.67286280227386038750` and
`0.67286947073481791424`. They require respectively 3741/5825 and 5845/11318
cells/leaves. We select the lower candidate because its projected build is
shorter, so the first full verification starts sooner.

Compute estimate before launch: the old measured rates from
`ainta_seven_point/FOUR-POINT.md` are 6.51 seconds per cell and 1.34 seconds
per leaf. This candidate projects 26665.58 seconds serial including a
15-minute prelude. Two explicit build processes project 13782.79 seconds,
about 3h50m, if scaling is ideal. This is an estimate, not a promised runtime.
The existing public-repository GitHub Actions standard runner is the compute
provider. No paid Modal run is launched. The job timeout remains 350 minutes.

Local setup installed the declared Python requirements with both Arb and
mpmath interval backends available. The broad fast tier was stopped after
28 failures, 610 passes and 1 expected failure in 80.62 seconds: every failure
reported the missing LLVM compiler backend (`clang` absent from PATH).
The numerical proof work does not consume that backend. Relevant hunt and
document checks pass: 27 tests. No green full-suite claim is made.

```runmanifest
id: four_point_pressure-2026-09-05-c2330
hunt: four_point_pressure
started: 2026-09-05T19:26:00Z
finished: arithmetic complete; Lean build pending
ran:
  - .venv/bin/python hunts/ainta_seven_point/four_point_gen.py 2330 2500
  - .venv/bin/python hunts/ainta_seven_point/four_point_preflight.py
  - .venv/bin/python -m pytest -q -n0 tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_huntspec.py
outcome: exact arithmetic and emitted-source preflight pass; complete kernel verification remains pending
artifacts:
  - hunts/ainta_seven_point/lean-four-point/FourPoint/Main.lean
  - hunts/ainta_seven_point/lean-four-point/FourPoint/Cells.lean
  - hunts/four_point_pressure/RUNS.md
```

## 2026-09-28: postbuild addendum, Lean kernel build passed

The candidate was built layer by layer at source commit
`5522b96314f7f63198ae3ec4e71d954255f93d1a`, pinned toolchain
`leanprover/lean4:v4.33.0-rc2`, on Modal (final app
`ap-7zxzQj0YqTwlQUP6P06ecn`, profile `teal-sea`, one `lake build` at a time),
not on GitHub Actions as the 2026-09-05 estimate planned. The build was resumed
across several launches; `evidence/README.md` lists them and states two
provenance gaps.

Result: 49 receipts, all ok, zero sorry warnings, verifier `FPVERIFY ok: True`
with no problems. Each of `F4_eq`, `cover1`, `four_point_cert`, `Phi_four`,
`four_point_bound`, `four_point_bound_ratio` depends only on
`[propext, Classical.choice, Quot.sound]`. The sources on this branch hash to
the values the run recorded (51-file `FourPointCand` tree
`a72e89fc...8962c82`, 84-file `lean/bridge` tree `a4931d83...f8d2ff`). No proof
source or numerical constant was changed after the run.

Cost: the report's metered lower bound is about $0.92 across receipts, excluding
image prep and container start; the earlier serial 26665.58 s estimate above was
for GitHub Actions and was not the provider used. Wall time of the final launch
was 920.9 s because it resumed from a saved checkpoint.

Scope: a local compile record, pending external verification. The GitHub
`checks` workflow does not compile Lean, so it neither confirms nor contradicts
this build. Earlier statements in this file that no Lean verification had been
completed described the state on 2026-09-05.

```runmanifest
id: four_point_pressure-2026-09-28-c2330-modal-kernel-build
hunt: four_point_pressure
started: 2026-09-28
finished: 2026-09-28
ran:
  - serial layer-by-layer lake build of FourPointCand on Modal, final launch 20260928t220203, app ap-7zxzQj0YqTwlQUP6P06ecn, source 5522b96314f7f63198ae3ec4e71d954255f93d1a
outcome: 49 receipts ok, zero sorry warnings, FPVERIFY ok True, six advertised theorems depend on propext Classical.choice Quot.sound only; local kernel build at pinned Lean v4.33.0-rc2, pending external verification
artifacts:
  - hunts/four_point_pressure/evidence/README.md
  - hunts/four_point_pressure/evidence/zeta-fourpoint-serial-result-final3.md
  - hunts/four_point_pressure/evidence/modal-ap-7zxzQj0YqTwlQUP6P06ecn-client-stdout-stderr-launch-20260928t220203.log
  - hunts/four_point_pressure/evidence/main-axioms-print-output.txt
  - hunts/four_point_pressure/evidence/SHA256SUMS
```

Note on the 2026-09-05 manifest above: its artifact paths `FourPoint/Main.lean`
and `FourPoint/Cells.lean` are historical. The module root was renamed to
`FourPointCand` on 2026-09-05 (see `REPAIR-RESULT.md`); the current paths are
`hunts/ainta_seven_point/lean-four-point/FourPointCand/Main.lean` and
`.../Cells.lean`. The old manifest is left as recorded.
