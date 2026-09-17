# Run record

## Baseline

Base `85efdcb2b4f8255caed8dbac0961c28361abd413` has successful GitHub Actions
`tests` run `34913353458` and `full` run `35095988548`, read through `gh` in
this session. The original checkout's governance subset passed 33 tests in
42.73 seconds before this worktree was created. Its Arb and mpmath interval
backends were both available. The new worktree gets its own virtual environment.

## Pilot budget, before execution

First unit: one completed-series zero solve below imaginary height 20 at
40 decimal digits. Hard wall budget: 30 seconds. At most four initial solves,
then at most five heat-continuation steps with a 60-second aggregate budget.
Measure the first unit before enlarging either range. No high-height census.

A local ball inequality, if the pilot supplies a centre, starts with one value
at 96 bits and an integrator evaluation limit of 20000. Measure that call before
choosing a repeat count. A long proof search or large mesh must move to CI and
requires a separate recorded estimate.

The first pilot hit its 60-second process timeout without returning a result.
Its unconstrained secant iteration had no per-evaluation domain guard. No
zero or timing measurement is inferred from that failed run. The revised pilot
rejects iterates outside `-1<Re(s)<4`, `abs(Im(s))<30`, limits each solve to
six seconds between evaluations, and prints each outcome immediately.

## Pilot outcomes and next bounded budget

The revised four-seed pilot completed in 0.517 seconds. Three solves returned
two distinct off-line zeros; one iterate was rejected outside the box. The
first solve took 0.148 seconds. Five heat steps through time 0.4 returned
non-real candidates. The independent 40-digit zero-time and modular-sign
tests both passed. The new ball-path test failed because its module did not
exist yet, the intended pre-implementation failure.

A six-step, 320-node measured continuation took 0.0015 seconds. It found
`z=7.646830873063853+0.42593828767886044i` at `t=1`. Later steps converged to
real roots; this is not a decided landing time. Allocate three ball integrals
at this fixed rational time and a small rational disk, initially 96 bits:
one pilot integral with a 20000-evaluation limit, then estimate repeats from
its observed runtime. No high-height scan or large search follows.

The first 96-bit heat integral at the proposed time-one centre returned in
0.0093 seconds. The zero-time Arb/Hurwitz cross-check passed with the two
earlier tests, three tests total. Budget twelve integrals for four Rouche
checks at different precisions and truncations: extrapolated integration
time 0.12 seconds, allow a 30-second wall limit including startup and tests.

## Completed bounded run

The exact checker completed after the first-function comparison was added. It
replayed four Rouche enclosures, two interval backends for the second-function
phase bound, two interval backends for the first-function domination bound,
four normalization checks, and two lesion checks. The hunt's eleven targeted
tests passed. Muse independently reviewed the complete analytic chain and
found no defect conditional on the stated enclosure premises. Gemini reran the
numerical packet and found no implementation defect. Claude Opus independently
derived the coarse first-function upper bound. These are model reviews, not
non-model truth assignments; the non-model evidence is the exact arithmetic,
Arb enclosures, mpmath interval cross-leg, and cited de Bruijn theorem.

The complete non-slow repository suite finished in 661.03 seconds with 3,094
passes, one skip, six expected failures, and one failure in the pre-existing
Hardy Z provenance check. Running that test alone in the untouched primary
checkout produced the same failure: `HardyZ.lean` last changed on 2026-09-05,
while its recorded kernel observation is dated 2026-08-13. This hunt does not
touch the Lean file, dossier, or test. The baseline defect remains open because
repair requires a new watched kernel build, which this mission expressly does
not authorize locally.

```runmanifest
id: dh_minus_heat-2026-09-17-bounded1
hunt: dh_minus_heat
started: 2026-09-16T19:18:02-05:00
finished: 2026-09-17T07:58:38-05:00
ran:
  - .venv/bin/python -m hunts.dh_minus_heat.verify
  - .venv/bin/python -m pytest -q -n0 hunts/dh_minus_heat/test_heat.py
  - .venv/bin/python scripts/71_contribution_check.py hunts/dh_minus_heat
  - .venv/bin/python -m pytest -q -m "not slow"
artifacts:
  - hunts/dh_minus_heat/rouche.json
  - hunts/dh_minus_heat/phase.json
  - hunts/dh_minus_heat/first_comparison.json
  - hunts/dh_minus_heat/verification.json
outcome: one rational disk and two zero-strip calculations support a reviewed candidate separation of the two conductor-five heat constants
```

## Second bounded run: approach the first collision

Estimate recorded before execution at `2026-09-17T08:13:22-05:00`. One
320-node continuation step previously took less than 0.001 seconds, and one
96-bit enclosed heat integral took 0.0093 seconds. Allocate at most 25 measured
steps on `1<=t<=1.1` and at most four rational-time Rouché attempts. Twelve
integrals per attempt extrapolate to 0.12 seconds, so allow a 30-second wall
limit for the scout and a 60-second wall limit for all enclosures and tests.
Stop after the latest rational time whose disk is separated from the real axis
and has a positive enclosed margin. This run does not assert that a failed disk
is the collision time and does not launch a high-height census.

The 480-node scout completed 15 continuation steps in 0.0044 seconds. The
non-real branch reached `7.543145542462766 + 0.0726463302507084 i` at
`t=217/200`; at `t=1.09` the root solver returned a real root. The latter is
only a scout failure boundary, not a decided collision. Four Arb enclosure
configurations at `t=217/200`, spanning 96 to 160 bits, theta cutoffs 24 to 28,
and integration cutoffs 7/2 and 4, all decided the later Rouché margin positive.
The conservative exact margin is `559961/2000000000000000`.

Muse independently checked that any such later off-axis disk strengthens the
strict lower bound under the closed-upper-ray argument, and warned that the
approach to the axis proves no collision time or global real-rootedness. The
first Gemini scout produced no output because its read-only session requested
write permission; it contributes no evidence. Claude Opus then independently
recomputed the direct quadrature at 50 digits. It obtained
`abs(H_t(c))=4.25e-15`, `abs(H_t'(c))=0.00286`, reproduced the centre within
`1.5e-12`, and found no normalization discrepancy.

```runmanifest
id: dh_minus_heat-2026-09-17-collision1
hunt: dh_minus_heat
started: 2026-09-17T08:13:22-05:00
finished: 2026-09-17T08:20:28-05:00
ran:
  - 480-node continuation at fifteen times from 1.01 through 1.1
  - four Arb Rouché configurations at t equals 217/200
  - .venv/bin/python -m hunts.dh_minus_heat.verify
  - .venv/bin/python -m pytest -q -n0 hunts/dh_minus_heat/test_heat.py
artifacts:
  - hunts/dh_minus_heat/collision_scout.json
  - hunts/dh_minus_heat/rouche.json
  - hunts/dh_minus_heat/verification.json
outcome: a later rational disk raises the candidate strict lower bound from 1 to 217/200 without deciding the collision time
```

## Reconciliation with current main (2026-09-17)

Merged `origin/main` (`c1c818a`, Bloch verifier environment) into this branch;
it touches nothing under `hunts/`, so no packet file changed. Reran the gates
after the merge with identical outcomes: `verify` reports 8 Rouché runs,
2 phase backends, 2 first-comparison backends, coarse margins
`5999913/4000000000000000` and `559961/2000000000000000`; the hunt plus
governance subset passes 58 with 3 expected xfails; `contribution_check`
passes 21 with 2 deselected; context, secret-tree, and whitespace checks pass.
No load-bearing argument changed, so no new review was ordered; the recorded
Muse, Gemini, and Claude Opus reviews still match the merged revision.

## Plus-normalization repair (2026-09-17)

Defect: the packet derived the minus odd kernel and sine flow but left the
plus function used in `Lambda_plus <= 1/2` implicit. Repair states
`tau_plus=sqrt(1+phi^2)-phi`, `tau_minus=-phi-sqrt(1+phi^2)`,
`a_tau=(1,tau,-tau,-1,0)` mod 5, `D_tau`, `F_tau` in the narrow frame
`s=1/2+iz`; derives `ahat=-i a/sqrt(5)`,
`omega_plus(1/x)=+x^(3/2)omega_plus(x)`, real even `g_plus`,
`F_plus(1/2+iz)=4 integral g_plus cos`, and cosine flow `H_plus,t`, while
retaining the minus sine flow as `H_minus,t` (rest of packet: `H_t`).
`Lambda_plus <= 1/2` (narrow, `<= 2` wide) is tied to the plus strip and
`H_plus,t`. Bounds, frames, and the x4 conversion are unchanged; the local
collision caveat is unchanged. Helpers generalized minimally
(`parameter_plus`, optional `tau`/`wave` args, `heat_plus_mp` wrapper);
`verify.py` gains `even_theta_transform` and
`plus_zero_time_cosine_identity` checks, `test_heat.py` gains the matching
two tests. Status stays reviewed conventional argument with
enclosure-carrying numerical steps; no novelty or RH claim.

Ran:
  - .venv/bin/python -m hunts.dh_minus_heat.verify
  - .venv/bin/python -m pytest -q -n0 hunts/dh_minus_heat/test_heat.py
  - huntspec/doors/probe/docs-numbering subset, contribution_check,
    make_context --check, secret tree, git diff --check
Outcome: plus modular sign and zero-time cosine identity pass; all bounds
unchanged.
