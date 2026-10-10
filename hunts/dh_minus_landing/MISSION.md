# Hunt #122: the second-DH lower endpoint, pushed to the tracked pair's landing time

Base: `origin/main` at `ef4e056` (2026-10-08), worktree branch
`hunt/forage-2026-10-08`. Status: exploratory probe; nothing here is a result
(`hunts/README.md`). Narrow frame `s = 1/2 + iz` throughout, as in the parent
hunt; wide-frame values are the narrow ones times four.

## The door, and why this one

`hunts/dh_minus_heat/RESULTS.md` left the second conductor-five heat constant in
the bracket `217/200 < Lambda_minus <= 567009/320000` and named three doors.
Its first door is **a later rational heat time for the same conjugate pair**,
information class "local analytic data: Arb enclosures of one value, one
derivative, and a disk-wide second-derivative majorant". The scout
(`collision_scout.json`) saw the pair at depth `0.0726` at `t = 1.085` and a
real root at `t = 1.09`, and the hunt refused, correctly, to promote that into
a collision time.

This door is chosen because it is a precise question with a numerical answer
(where does the pair land, and how close to that time can the hunt's own disk
instrument decide a non-real zero), it is decidable in seconds with instruments
already in the tree (the parent hunt's `odd_ball.rouche`, docs/37's
contour-moment discriminant tracker), and its answer reprices a recorded door:
after it, the door is worth exactly `t_c - 217/200` for this pair and is shut
for this pair, so no later session needs to climb the same ladder.

### Runners-up, and why not

1. **The parent hunt's second door, a sharper zero strip for the upper
   endpoint.** Already answered in the tree and not consumed: `hunts/lambda_dh_bounds/strip2_results.json`,
   field `control_tau_minus`, decides the minus-function phase abscissa
   `sigma* = 2.38228610898712387...` at `P = 10^5` on both backends, and STRIP2
   section 3.3 proves the phase lemma is the end of that line of argument. The
   repricing is one subtraction (recorded in RESULTS.md, "The doors"), not a
   run. Worth about `4.0e-4` of the bracket.
2. **A zero-surplus witness at `N = 576` for `paid_surplus_obstruction`.** A
   linear feasibility question, decidable, but that hunt states itself that
   zero surplus at another cutoff "would only identify `C_N = psi(N)` there"
   and supplies no scale-dependent estimate: closing it reprices nothing.
3. **Hunt #119's registered predictions for `Lambda_DH` (first DH function).**
   Open and unadjudicated, but its evaluation phase needs deep zeros above
   height 600 and a census, which is not a one-hour four-core question, and the
   contract files say whoever resumes should decide the adjudication first.
4. **The third `dh_minus_heat` door (even versus odd conductor-five kernels).**
   A theorem is asked for; no numerical experiment decides it cheaply.

Open branches checked on 2026-10-08 (`git branch -r`): `depth-bound-selfterm`,
`robin-tfree`, `weil-c4-s2`, `weil-propagation`, `openai-math-release`,
`erdos-counterexample-arm`, the `palomar` series, `gate-and-setup`,
`nobody-asked-rule`, `zeta-lab-research-director`. None touches
`hunts/dh_minus_heat` or this question.

## What was done

`probe.py` measures the landing time `t_c` of the pair by two independent
routes (an mpmath double-zero Newton solve with analytic Jacobian at 30 and 50
digits; a float64 contour-moment discriminant tracker on two grids), then
climbs five rational heat times below `t_c` with the parent hunt's Arb
Taylor/Rouche disk at four precision and cutoff configurations each. Controls:
known values (`zeta(2)`, `gamma_1`, `Xi(0)`), the recorded `217/200` disk
reproduced, the `t = 0` admissibility gate against the pilot zeros and the
Hurwitz zero-time identity, two closed-form polynomial landings for the
tracker, three instrument lesions, and one shared-layer kernel fault that the
two routes cannot see and the Hurwitz identity can. The pilot's second zero is
tracked to its own landing as a scout.

## Resource boundary

Serial numerics only, about 35 seconds per probe run on one core; no Lean
build, no CI, no paid compute, no census, no edit outside this directory and
the one case-log entry.

```huntspec
id: dh_minus_landing
question: How far can the dh_minus_heat tracked pair push the strict lower endpoint of Lambda_minus, and at what heat time does it land?
frontier: narrow bracket 217/200 < Lambda_minus <= 567009/320000 (hunts/dh_minus_heat), scout saw the pair at depth 0.0726 at t=1.085 and a real root at t=1.09
proposed_attack: measure the landing time by two independent routes, then decide Arb Taylor/Rouche disks at rational times just below it
dead_routes:
  - promoting the float scout's last off-axis time into a collision statement (refused by the parent hunt)
  - sharpening the integer tail of the prime-phase strip for the upper endpoint (already decided in lambda_dh_bounds/strip2_results.json, control_tau_minus; worth about 4e-4)
  - coefficient domination for the strip (lambda_dh_bounds/STRIP.md, a factor 2.08 weaker than the phase bound)
required_oracles:
  - Arb disk enclosures with explicit theta and integration tails, compared as exact rational endpoints (hunts/dh_minus_heat/odd_ball.py)
  - the Hurwitz-zeta zero-time identity, which shares no theta integral with either tracking route
  - closed-form polynomial landing times (y0^2/2 for an isolated pair, the quartic formula of docs/37) on the same tracker
  - the recorded 217/200 disk and its coarse bounds, rerun
kill_conditions:
  - the two landing-time routes disagree by more than 1e-10
  - the landing time moves by more than 1e-20 between 30 and 50 digits
  - the tracker fails to reproduce a pilot zero at t=0
  - no rational time above 217/200 yields a decided disk on every configuration
  - the second pilot pair lands later than the first, so the same-pair door is not the binding one
agents_may:
  - derive
  - run bounded serial numerics
  - import the parent hunt's instruments unmodified
  - plant faults and record which check catches them
agents_may_not:
  - assign evidentiary status to this hunt's output
  - promote their own claim
  - declare novelty
  - modify hunts/dh_minus_heat, zeta/, ontology/ or harness/
  - state a landing time as the de Bruijn-Newman constant, which needs every pair and the no-creation step
```
