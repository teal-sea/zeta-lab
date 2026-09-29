# Runs

**Current status (2026-09-28): the Lean kernel build of the c = 2330/10^6 candidate
has been run and passed, locally by this laboratory, on Modal.** Build receipts,
the complete final log, the six raw axiom lines and provenance are in
`evidence/` (start at `evidence/README.md`). It is not external review and not a
Palomar registration. The September 5 canceled-run record below is historical;
see the September 28 addendum and subsequent integration audit.

## 2026-09-05: candidate emitted, complete Lean check canceled

**Terminal status: canceled, not kernel-checked.** The existing registered
four-point bound remains unchanged. This experiment produced no new proved
constant, and no 68% or 69% result.

The selected parameters were `n=4`, `c=2330/1000000`, `p=2500`, `m=432`.
Substitution into the existing bridge gives the candidate expression

    (14400000 * H - 17240) / 14366681

where `H = 3/2 - cot(1/sqrt(2))/sqrt(2)`. Numerical evaluation at 80-digit
working precision, rounded here:

    registered: 0.672847019766688827607589366851
    candidate:  0.672860358838866659500205300554
    difference: 0.0000133390721778318926159337024

The subtraction compares expressions, not two established lower bounds.
The candidate's uniform finite-certificate obligation was not discharged by
a complete Lean build. The earlier
[FOUR-POINT.md](../ainta_seven_point/FOUR-POINT.md) already tabulated this
floor, so this is not a claim to have discovered the numerical parameter.

### Exactly what ran

The original local run reported exact search-tree closure. The separate
emitted-source preflight was rerun before this publication on the preserved
candidate checkout. It reports 1516 cell lemmas, 11863 leaves, 220 chunks,
13 boxes, and 64 dispatch cases, with zero problems. This is an arithmetic
and coverage check of the emitted source, not a Lean kernel check.

The complete check was attempted only in
[GitHub Actions run 33987435968](https://github.com/teal-sea/zeta-lab/actions/runs/33987435968),
against commit `d28df5f992479cd32751cb90c8c88551550582a3`.
The run was created at `2026-09-05T19:32:53Z` and reached terminal
`completed/cancelled` status at `2026-09-05T19:42:20Z`.

Toolchain installation and the Mathlib cache step succeeded. The dependency
build was canceled. Every candidate proof step, including `FourPoint.Base`,
the cells, the chunks, `FourPoint.Main`, and the final axiom audit, was
**skipped**. A later cache-saving step failed during cancellation cleanup;
that is not a mathematical failure of the candidate. No Modal job was
started. The state was read back from the run API before publication.

The original time estimate was about 3h50m with ideal two-process scaling,
using the earlier measured per-cell and per-leaf rates in `FOUR-POINT.md`.
The run did not measure that speedup. Accordingly, its parallel-build
workflow change is not included in this publication.

### Reproduce the arithmetic without starting a search or build

From a repository environment with the declared Python dependencies:

```sh
.venv/bin/python - <<'PY'
from fractions import Fraction as Q
import mpmath as mp

with mp.workdps(80):
    H = mp.mpf(3)/2 - mp.cot(1/mp.sqrt(2))/mp.sqrt(2)

    def expression(c, p, m):
        denominator = Q(m) - c * (m - 3)
        coeff = Q(m) / denominator
        offset = Q(3 * (m - 1), p) / denominator
        value = (mp.mpf(coeff.numerator) / coeff.denominator * H
                 - mp.mpf(offset.numerator) / offset.denominator)
        return coeff, offset, value

    old = expression(Q(2310, 10**6), 2500, 435)
    candidate = expression(Q(2330, 10**6), 2500, 432)
    assert old[:2] == (Q(906250, 904171), Q(1085, 904171))
    assert candidate[:2] == (Q(14400000, 14366681), Q(17240, 14366681))
    assert old[2] < candidate[2] < mp.mpf('0.68') < mp.mpf('0.69')
    for label, value in [('registered', old[2]), ('candidate', candidate[2]),
                         ('difference', candidate[2] - old[2])]:
        print(label, mp.nstr(value, 30))
PY
```

To inspect the already-emitted source, use a checkout at the pinned
candidate commit and run:

```sh
.venv/bin/python hunts/ainta_seven_point/four_point_preflight.py
```

That command reads the generated files. Regenerating them or launching the
complete Lean workflow is not necessary to reproduce this record.

### Scope and exclusions

The existing [family-wall analysis](../family_wall/FAMILY-LIMIT.md) concerns
the current n-point pressure construction for `n>=3`. Its written argument
and interval-arithmetic witnesses give a ceiling near `0.675142509660254`,
below 68%. This experiment did not produce a new Lean proof of that ceiling,
nor does it turn a method-specific wall into a bound for every possible
zeta argument. The previously published analysis, including its repaired
case split, is the source for that statement.

The candidate branch is preserved for reproducibility. None of its generated
Lean replacements, candidate-specific preflight constant, or workflow edits
is merged with this record. The registered theorem and public headline are
unchanged.

The original broad local fast-tier attempt stopped with 28 failures, 610
passes, and one expected failure; its failures reported absent `clang`.
It was not a green full-suite run. The archival publication instead checks
the touched documentation and hunt contracts, the arithmetic snippet above,
the emitted-source preflight, the context index, and the secret guard.

```runmanifest
id: four_point_pressure-2026-09-05-c2330-disposition
hunt: four_point_pressure
started: 2026-09-05T19:32:53Z
finished: 2026-09-05T19:42:20Z
ran:
  - .venv/bin/python hunts/ainta_seven_point/four_point_gen.py 2330 2500
  - .venv/bin/python hunts/ainta_seven_point/four_point_preflight.py
  - GitHub Actions four-point workflow at d28df5f992479cd32751cb90c8c88551550582a3, run 33987435968
outcome: exact search and source preflight completed; dependency build canceled and every candidate proof step skipped; no new proved bound
artifacts:
  - hunts/four_point_pressure/MISSION.md
  - hunts/four_point_pressure/RUNS.md
```

## 2026-09-28: integration preflight at the published Hermes revision

The owner resumed the work and supplied the branch
`vizier/four-point-stronger-cert`, revision
`5522b96314f7f63198ae3ec4e71d954255f93d1a`.
The candidate module root is now `FourPointCand`, avoiding the import
ambiguity with the registered `FourPoint` library in its bridge dependency.
The parameter tuple remains `(4, 2330/1000000, 432, 2500)`.

A fresh emitted-source preflight reported 1516 cell lemmas, 11863 leaves,
220 chunks, 13 boxes, and 64 dispatch cases, with zero problems. The focused
module-root, document-numbering, hunt-discipline, doors, and Palomar
correspondence suite passed all 31 tests. These checks do not establish a
Lean kernel result. At this checkpoint the successful Hermes build log and
axiom output have been requested but are not yet in the published branch.

The GitHub checks run 36497885884 passed its tree-invariant tests and failed
only the generated `CONTEXT.md` freshness check. Its status is not evidence
of either a failed or successful Lean build.

After reconciling with main at `46c896b0`, the focused suite passed 61 tests
in 97.11 seconds, including the door commands. The expanded governance and
integration suite passed 358 tests with two slow tests deselected in 7.30
seconds. The context freshness check and whitespace check against main pass.
The workflow parses as YAML and all 13 shell steps pass `bash -n`.
Its targets follow `FourPointCand`; the unmeasured two-process Lake launcher
has been removed in favour of the existing single-Lake scheduling pattern.
No new Lean workflow was dispatched during intake.

At this checkpoint, `lean/bridge` was unchanged from current main. Candidate
proof-source changes introduced by the merge were comment punctuation only
in `Base.lean` and `Main.lean`; these were subsequently restored to the
built source bytes during the evidence audit below. Current registry
compatibility is recorded in
[PALOMAR-READINESS.md](PALOMAR-READINESS.md).

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
`FourPointCand` on 2026-09-27 (see `REPAIR-RESULT.md`); the current paths are
`hunts/ainta_seven_point/lean-four-point/FourPointCand/Main.lean` and
`.../Cells.lean`. The old manifest is left as recorded.

## 2026-09-28: integration audit of the published build evidence

The evidence arrived in `5723f194ba1c510f1cf480a5404b3147d61a7c89`.
All three raw artifact checksums pass. Hashing Git objects at `5522b963`
reproduced both source-tree digests in the preflight and final verifier.
The driver sorts complete `sha256  path` records, not filenames; the
per-file `evidence/source-manifest.json` preserves this binding.

The current candidate's 51 source files are byte-identical to the built
revision, including the original comment punctuation. The integrated bridge
is current main's version; its differences from the built revision are
comments, documentation and support scripts, not theorem declarations or
proof terms. The postbuild addendum's statement about matching branch
hashes refers to the original Hermes source branch, not this merged bridge
tree. No fresh Lean build of the integrated checkout is claimed.

Six new regression tests check raw checksums, all 49 receipts and 48
compiled-module records, all six axiom lines, both source manifests, and
the current candidate's exact source bytes, and the displayed decimal
improvement. Hermes subsequently published `958877c2`, sanitizing exactly
three local filesystem paths in the report and log. Intake confirmed that
the verification JSON and axiom output are unchanged and incorporated the
sanitized copies. No new repository-hygiene exception is needed.
Earlier launch logs and the incomplete saved-image lineage remain explicit
limitations, not silently reconstructed evidence.

After incorporating the sanitized evidence, the expanded governance and
integration suite passes 364 tests with two slow tests deselected in 6.98
seconds. The six evidence tests and four module-root tests now run in the
ordinary dependency-free CI gate. Context freshness passes. The whitespace
check passes outside the supplied build log, whose original whitespace is
preserved along with its checksum.

## 2026-09-28: Lean 4.35 and module-system port, initial pilot

The owner requested the compatibility port tracked in issue #260. The source
preparation pins Lean `v4.35.0-rc2` and canonical Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` in six contained packages.
The formerly external Zeta23 source at `3635e748` is now a contained,
attributed Apache-2.0 dependency. All 643 Lean files have module headers;
no source exceeds 10000 lines. Module visibility changes preserve the
four-point candidate's declaration and proof text byte for byte after
removing only the migration's header, import and exposed-section additions.

Compute estimate: the compiler and Mathlib changed, so the old build timings
are not treated as measured timings for this port. First time the dependency
unit `Zeta23.Defs.Counting`, with a 15-minute build bound and a 30-minute
job bound including toolchain/cache retrieval. Only that unit is authorized
by this initial workflow. Use its result to plan the larger dependency and
certificate stages. Checkpoint the unit and publish the terminal outcome,
artifact count (including zero), exact source revision and logs. No local
Lean build is run, and no successful port is claimed before CI verifies it.

The initial pilot passed in GitHub Actions run `36504004985`, source
`bb38b795096c2e26e3309050717af56b895a414f`. Lean reported version
`4.35.0-rc2`, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`.
Two upstream modules (`Zeta23.Defs` and `Zeta23.Defs.Counting`) built in
5.41 seconds, with maximum resident set size 1479748 KiB. The job including
cache/toolchain work and checkpointing took 2 minutes 28 seconds. Its raw
build log, compiler version and source revision are under
`port-evidence/36504004985/`. The reported 2885 Lake jobs include cached
Mathlib dependencies; only two new upstream module artifacts were counted.

The next target, `Zeta23Ext.Bridge.Main`, has 157 local modules in its
transitive source-import closure. Multiplying the pilot's mean by that count
gives about 425 seconds, a rough scheduling estimate only: the two elementary
pilot modules do not measure the cost of the analytic proofs. The next build
has an 18-minute bound and checkpoints completed module artifacts even on
failure. It does not run alongside the numerical suite. A failed or canceled
job produces an explicit failing verdict; no automatic retry loop is added.

The first analytic-bridge attempt, Actions run `36504395205` at source
`e0a12c9f0a64c5708fc308c8edb204c9da8f9b3b`, failed after 6 minutes
18.02 seconds of build time, with maximum resident set size 3312688 KiB.
It checkpointed 111 module artifacts and reported five failed modules.
The terminal failure and raw diagnostics remain in that run's artifact.
The next attempt repairs two product-inequality API calls, adds a direct
complex-log derivative import, puts the custom tactic in a public meta
section, and uses the pointwise logarithmic-derivative multiplication lemma
in two proofs. No theorem statement or hypothesis is changed.
