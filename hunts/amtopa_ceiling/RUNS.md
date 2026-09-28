# Runs: `amtopa_ceiling`

Every run of this hunt, including the ones that produced nothing and the one that
had to be killed. Cost estimates were written before the runs they describe, per
the discipline this hunt was opened under.

The target repository is pinned throughout:

    AMTOPA/zeta-exact-pressure
    commit 7253fdcab9366af45b8c8caf44e408c0af44a1a7
    2026-08-13 17:26:37 +0800  "Add finite check for primitive Gauss transform"

Nothing was posted, opened, commented, forked or starred anywhere. Every external
repository was read or replayed read-only.

## Where the compute lives, and why

The authoring host is a laptop under a hard local-compute cap, with a guard that
kills heavy processes and no Lean at all. **One run in this hunt broke that cap
and took the operator's session down** (run 8 below). After that, everything
beyond a second runs on GitHub Actions, in jobs under a 20-minute timeout with
their own artifacts: `hunts/amtopa_ceiling/ci-sweep.yml`, mirrored to
`.github/workflows/hunt-amtopa-ceiling.yml` so it triggers on this branch.

---

```runmanifest
id: amtopa_ceiling-local-2026-08-24
hunt: amtopa_ceiling
started: 2026-08-24T08:55-05:00
finished: 2026-08-24T10:20-05:00
ran:
  - git clone of AMTOPA/zeta-exact-pressure into a scratch directory, detached at 7253fdcab9366af45b8c8caf44e408c0af44a1a7, read-only
  - their src/check_candidate.py, src/check_final_bound.py and src/check_window.py, unmodified
  - exact-rational replay of their scalar-Gram assembly with a rational under-estimate of the only square root, hunts/amtopa_ceiling/exact_assembly.py
  - independent reimplementation of window, kernel, functional and window constant from their proof.md, hunts/amtopa_ceiling/family.py
  - closed-form Rayleigh maximum of the window constant over 1, 2, 3, 7, 13, 17 and 25 term windows, hunts/amtopa_ceiling/probe_window.py
  - cutting-plane linear programme over the pair-weight polytope alone, hunts/amtopa_ceiling/step1_pairweights.py, which did not converge
  - cutting-plane linear programme over the pair-weight polytope and the pressure simplex jointly, hunts/amtopa_ceiling/step2_epsstar.py, whose inconsistent bracket exposed two bugs
  - saturation sweep of the total pressure with contaminated floors, withdrawn
  - candidate quantisation, killed at 1.8 GB resident after allocating an unchunked kernel matrix
  - converged two-sided bracket on eps* at their window and their total pressure, hunts/amtopa_ceiling/step5_headroom.py
  - saturation sweep of the total pressure, redone after the fix, hunts/amtopa_ceiling/step3_bsweep.py
  - single linear programme re-solve for the equality-row duals and the active set at the optimum
  - full read of src/verify_local_tables.cpp, src/build_interval_tables.py, src/write_verifier_config.py and src/check_window.py against their proof.md
outcome: their published headline reproduces to 70 decimals in exact rational arithmetic and their window constant and float minimum reproduce to the binary64 limit, with no defect found that affects their claim; their number is nevertheless not at their own family's ceiling, because the pair-weight polytope and the pressure simplex admit a floor of 0.007916857812 against their 0.007911105155, worth +3.96e-06 on the assembled proportion, and a candidate quantised into their own schema at the rational target 19791/2500000 assembles exactly to 0.6734201550790580964457598685450152133015; on the two axes where a ceiling can be computed rather than searched they are at it, the total pressure sitting at the argmax of the saturation curve with net marginal +0.006076 and the window constant being unable to rise at all inside their frequency set because the 2*j*pi harmonics are exactly M-orthogonal to the sqrt(2) fundamental [WITHDRAWN 2026-09-06: the clause from 'their number is nevertheless' to the assembled 0.67342015 is false. That floor is a float minimiser's over-report; the true floor at those weights is 0.0078946642 and the candidate's assembled bound is 1.03e-05 BELOW the record. Of the two axes called computable, the window constant is a closed form and stands; the total-pressure argmax is built from the same oracle's floors and is qualified in RESULTS.md section 4.2. The answer to the hunt's question is in RESULTS.md section 7.8: AMTOPA are at the ceiling on all five axes and the LP with a wide oracle finds nothing better than their own point. Appended rather than edited, because attempts are append-only and so is this record.]
artifacts:
  - hunts/amtopa_ceiling/RESULTS.md
  - hunts/amtopa_ceiling/exact_assembly.py
  - hunts/amtopa_ceiling/family.py
  - hunts/amtopa_ceiling/probe_window.py
  - hunts/amtopa_ceiling/ceiling.py
  - hunts/amtopa_ceiling/epsstar.py
  - hunts/amtopa_ceiling/sweep.py
  - hunts/amtopa_ceiling/make_candidate.py
  - hunts/amtopa_ceiling/artifacts/cut_pool.npy
```

```runmanifest
id: amtopa_ceiling-actions-2026-08-24
hunt: amtopa_ceiling
started: 2026-08-24T10:11-05:00
finished: 2026-08-24T10:45-05:00
ran:
  - job reproduce-amtopa-pinned, their run.sh on the pinned commit plus our three replays in a clean environment
  - job headroom-and-candidate, the eps* bracket from a clean checkout and the candidate written in their candidate.json schema
  - job pressure-saturation-curve, the pressure sweep against the shipped 2200-cut pool
  - job certificate-ours-polytope-optimum, their table builder and their C++ branch-and-bound at our rational target
  - job certificate-amtopa-baseline, the same pipeline at their own target, as a control
  - jobs window-sweep-shard-0 through 3, the seventeen-dimensional window search on four independent seeds
  - job doors-active-constraints, the LP duals and active set at the converged optimum, the pressure argmax on a fine bracket, and both ends of the window trade
  - jobs tables-<candidate>-shard-0 through 5, AMTOPA's own table builder driven over index ranges by shard_tables.py after the single-process build overran a 20-minute job
  - jobs certificate-<candidate>-s0 through s7, their C++ branch-and-bound with its root loop partitioned by root-shard.patch, at our candidate and at theirs as a control
  - ldl_probe.cpp, a seventy-line isolation of the convexity-gate regression between b3b7784 and the pinned tip
outcome: their own published finite inequality does not replay at the pinned tip, returning INCONCLUSIVE at a terminal cell with a rigorous lower bound 1.19e-07 short of their own target, while all six interval tables reproduce byte for byte against the digests in their own candidate.json; the cause is their convexity gate, which fires zero times in 72 million nodes here against 2030240 in their recorded run, because between b3b7784 (the commit their candidate.json names as the source of that run) and the tip the gate's curvature entries changed from thin points to intervals unbounded above and the interval LDL cannot certify positive definiteness of such a matrix; the direction is fail-closed, so this is a reproducibility defect and not a soundness hole, and it blocks our own candidate at the tip too, by 2.70e-08 [CORRECTED 2026-09-06: it does not. At b3b7784, with their gate firing 34,780 to 459,982 times a shard, their candidate is accepted 8 of 8 and ours is still refused on 4 of 8. Their refusal at the tip was the gate; ours was a target above the true floor. RESULTS.md sections 7.7 and 7.8.]
artifacts:
  - .github/workflows/hunt-amtopa-ceiling.yml
  - hunts/amtopa_ceiling/ci-sweep.yml
```

---

## Run by run, with the numbers

### 1. Their own scripts, on the pinned commit

Cost estimated before: four scripts, seconds each. Actual: under 5 s.

    check_candidate.py    candidate_consistency_verified=True
                          pair_weight_span_capacity_verified=True
                          position_pressure_total_verified=True 93/23000
    check_final_bound.py  scan_best_m=145
                          final_bound=0.673416490971499294950035533107490317499777...
    check_window.py       H = 0.672188158118234585169456387725654841146376619685...
                          H_floor_interval_verified=True
                          interval_window_lower_bound = 0.7616418486406763

Their headline reproduces from their own inputs, exactly as published.
**MEASURED**, their code, our host.

### 2. Exact-rational replay of the assembly

Cost estimated before: one integer square root at 200 decimals times 20,000 block
lengths, seconds. Actual: 3 s.

Their own `check_final_bound.py` uses `mpmath.mpf` at 100 dps with `mp.sqrt`,
which is arbitrary-precision floating point, while `README.md` and `proof.md`
both say *"exact arithmetic selects m=145"*. Redone in `fractions.Fraction` with
`math.isqrt` giving a rational under-estimate of the only square root, and with
the monotonicity direction asserted rather than assumed
(`d(bound)/dR > 0` needs `H > B/eps`, and `H - B/eps = 0.16104777081940091048`):

    lower  0.6734164909714992949500355331074903174997772794755665475125243371226272
    upper  0.6734164909714992949500355331074903174997772794755665475125243371226272
    theirs 0.6734164909714992949500355331074903174997772794755665475125243371226272

Seventy decimals agree. The exact scan over `m` in `[7, 20000]` returns
`argmax m = 145`, matching theirs. Their safe floor `0.6734164909` is cleared by
`7.14993e-11`. **VERIFIED**.

### 3. Independent reimplementation

Cost estimated before: numpy, milliseconds. Actual: under 2 s. Written from
`proof.md`, importing nothing of theirs.

| quantity | ours | theirs |
|---|---|---|
| `H(v)` | `0.67218815811823495743` | `0.67218815811823458517` |
| span capacities | `[2, 2, 2, 2, 2, 2]` exactly | same |
| `K(0)` | `0.91872536986556841` |, |
| `F` at their published basin | `0.007911105155226431` | `0.007911105155226424` |

Fifteen significant decimals on both, the binary64 limit. **VERIFIED**.

### 4. The window Rayleigh structure

Cost estimated before: a 17x17 linear solve, milliseconds. Actual: under 2 s.

`H_max = 2 - 1/(u^T M^{-1} u)` computed for 1, 2, 3, 7, 13, 17 and 25 terms is
`0.67250070367941172655` **in every case**, attained at `c = (1, 0, 0, ...)`.
Cause: `u_j = sinc(w_j/2) = 0` for every harmonic, and `M[0,j] = 0` for every
harmonic (computed `max |M[0,1:]| = 1.72e-16`). The second identity reduces
algebraically to `2 j^2 pi^2 (w_0^2 - 2)/w_0`, which vanishes exactly at
`w_0 = sqrt(2)`. Cost of switching on one harmonic from the pure window:
`dH = -5.6e-07` at `c_j = 1e-3` and `-5.6e-05` at `c_j = 1e-2`, quadratic, about
`-0.59 c_j^2`. **VERIFIED**.

### 5. Pair-weight cutting plane, first attempt

Cost estimated before: one global-minimum unit measured first at 5.0 s, times 18
rounds, about 90 s. Actual: 57.5 s. **Did not converge**: after 18 rounds the LP
upper bound was `0.0080314603` against a best achieved floor of `0.0077159782`, a
gap of `3.2e-04`. Recorded because it is the run that showed cutting planes on
the pair weights alone were too slow, which motivated putting the pressure vector
into the LP as well. Superseded by run 9.

### 6. Both linear axes in one LP

Cost estimated before: 20 rounds at 1.1 s per round, 22 s. Actual: 22.5 s.
Converged to a gap of `4.4e-08`, but reported an **inconsistent** bracket:
achieved floor `0.008006338789` above LP upper bound `0.007995158638`. Two bugs,
both caught by that inconsistency:

- a proximal term had been added to the LP objective, so `res.x[-1]` was no longer
  the pure `max t` value and was not an upper bound at all;
- the achieved floor was read only off a multistart, which was missing basins the
  cut pool already contained.

The shadow prices from this run are correct and are used throughout:

    d(bound)/dH   = +1.007627      d(bound)/deps = +0.642863
    d(bound)/dB   = -0.964154
    break-even d(eps)/dB    = 1.499781
    break-even d(eps)/d(-H) = 1.567405

The `eps*` bracket from this run is **withdrawn**.

### 7. Pressure sweep, contaminated

Cost estimated before: 15 values at about 30 s each, 7.5 minutes. Actual: 446.8 s.
Its floors were contaminated by bug (b) of run 6. **Withdrawn**, superseded by
run 10. Recorded because it is what first showed the marginal crossing the
break-even between `B/B0 = 1.00` and `1.25`.

### 8. Candidate generation, killed

Cost estimated before: **none written**, that is the failure. Actual: killed at
1.8 GB resident and 70% CPU, and it took the operator's session down with it.

Two faults, one technical and one procedural.

- Technical: `ceiling.W_matrix` allocated an `(N, 21, 17)` intermediate and the
  multistart called it at `N = 390000`, which is 1.1 GB in a single array. Fixed
  by chunking at 20,000 rows, with the reason written into its docstring.
- Procedural: no unit cost was estimated before the run, in a hunt whose brief
  said to estimate one unit and multiply first. That was the instruction and it
  was not followed.

Consequence: from this point every computation runs on GitHub Actions.

### 9. The converged bracket

Cost estimated before: one LP over a 22,112-row pool, measured at about 10 s.
Actual: 10 s. Converged in one round to a gap of `1.6e-17`, both bounds meeting:

    eps*(B0, their window)   0.007919365399
    AMTOPA achieve           0.007911105155     (their float minimum, reproduced)
    their accepted target    0.0079107
    headroom on the floor    +8.260e-06

Assembled at the true `H`, so the comparison is like for like: their own floor
gives `0.6734167515492229` at `m = 145`, the polytope optimum gives
`0.6734220612615708` at `m = 145`. Against their published headline
`0.6734164909714992`: `+5.570e-06`. For scale, the one-point pair-weight-free cap
is `0.0088144556`, loose by `8.95e-04`, which is why the LP and not the single
test vector is the instrument this hunt reports. **MEASURED**: LP upper bound
rigorous, achieved floor a float minimum.

### 10. Pressure sweep, redone

Cost estimated before: 15 values at about 55 s each against a 21,729-row pool,
about 14 minutes. Actual: 850.2 s.

| `B/B0` | `eps*` lower | `eps*` upper | bound | `m` |
|---|---|---|---|---|
| 0.25 | 0.0027299930 | 0.0027305525 | 0.6730015008061445 | 385 |
| 0.50 | 0.0046208925 | 0.0046209282 | 0.6732489147583361 | 235 |
| 0.75 | 0.0063144596 | 0.0063145540 | 0.6733647224807128 | 177 |
| 0.90 | 0.0073080619 | 0.0073080926 | 0.6734189561133835 | 155 |
| **1.00** | **0.0079193654** | **0.0079193654** | **0.6734220612615708** | **145** |
| 1.10 | 0.0084996468 | 0.0084997253 | 0.6734052811723370 | 136 |
| 1.25 | 0.0093153802 | 0.0093153802 | 0.6733453486423939 | 126 |
| 1.50 | 0.0106520485 | 0.0106520488 | 0.6732318828737838 | 112 |
| 1.75 | 0.0119241552 | 0.0119248361 | 0.6730788317451036 | 102 |
| 2.00 | 0.0131054032 | 0.0131152353 | 0.6728700066137836 | 95 |
| 2.50 | 0.0151776630 | 0.0151777768 | 0.6722757653775309 | 84 |
| 3.00 | 0.0172400594 | 0.0172400990 | 0.6721105568569956 | 7 |
| 4.00 | 0.0213638112 | 0.0213638713 | 0.6719283061757414 | 7 |
| 6.00 | 0.0296078150 | 0.0296079214 | 0.6715628207187594 | 7 |

Marginal floor per unit pressure, against the break-even `1.4998`:
`1.8706` pays, `1.6754` pays, `1.6382` pays, `1.5118` pays, then `1.4351` costs,
`1.3449`, `1.3223`, `1.2584`, `1.1685`, `1.0250`, `1.0201`, `1.0199`, `1.0194`.
The peak of the assembled bound is at `B/B0 = 1.00` exactly, at AMTOPA's own
`B = 93/23000`. **MEASURED**.

### 10b. The stopping rule was wrong, and Actions found it

The third methodological failure of this hunt, and the one worth the most.

Run 9 reported `eps* = 0.007919365399` and stopped at cutting-plane round 0 with
a gap of `1.6e-17`. The Actions job `headroom-and-candidate`, starting from a
**2,200-cut subset** of the same pool, ran 40 rounds, found 320 fresh cuts, and
drove the same quantity down to `0.007916857812`. More cuts can only lower an LP
upper bound, so **the Actions value is the correct one and run 9's was an
over-estimate**.

The cause is a stopping rule that could not fail: `lower` had been defined as
`min(multistart, pool minimum)`, and at the LP optimum the pool minimum **is**
the LP value by construction, so `upper - lower` was identically zero whenever
the multistart found nothing new. The loop halted at whatever value the incoming
pool already carried, and the richer the pool, the more confidently it halted
too early. Fixed in `epsstar.eps_star`: the test is now against the independent
multistart alone, and it must hold for `patience` consecutive rounds. The reason
is written into the source at the test.

What it changes: the headroom on the floor at their window and their pressure
falls from `+8.26e-06` to `+5.73e-06`, and the assembled ceiling from
`+5.57e-06` to `+3.96e-06` against their headline. What it does not change: the
sign, the shape of the pressure curve, the window Rayleigh result, or the ranking
of the doors.

### 11. Duals and the active set

One LP re-solve, seconds. `d eps*/d rhs` on the equality rows:

    span 1 capacity  +6.35008e-04      span 4 capacity  +4.7051e-05
    span 2 capacity  +1.0684e-05       span 5 capacity  +8.3364e-05
    span 3 capacity  +7.1795e-05       span 6 capacity   0  (slack)
    total pressure   +1.509447638

Net marginal value of pressure at their operating point:
`-0.964118 + 0.642748 x 1.509447638 = +0.006076`. Active set: 3 of 21 pair
weights at zero, 1 at the cap, 0 of 6 pressures at zero, and 18 of 2,200 gap
vectors active at `F = eps`, all near
`(1.98, 1.04, 1.97, 1.05, 1.97, 1.04)` and its reflections. **VERIFIED** (LP
duals) / **MEASURED** (active set).

---

## Costs estimated before the Actions jobs

| job | unit cost, measured on the authoring host | multiplied |
|---|---|---|
| `reproduce` | each script under 5 s | under 1 min |
| `headroom` | one LP over the shipped 2,200-cut pool, about 1 s | about 2 min with the multistart |
| `pressure-sweep` | 14 pressure values at about 20 s each against a 2,200-cut pool | about 5 min |
| `certificate` | interval tables at 0.0225 CPU-s per cell measured over a 400-cell smoke build, 64,954 cells = 1,462 CPU-s, about 6 min on four vCPU; their own branch-and-bound record is 3,768,186 nodes | under 20 min, node cap 3e8, exit code 3 tolerated |
| `window-sweep` | one surrogate evaluation measured at 0.0388 s; 26 generations at popsize 18 in 17 dimensions is about 8,000 evaluations | about 5 min per epoch, three epochs per shard, hard 900 s timeout inside the job |

## What run 1 actually cost, against those estimates

Actions run `32743347292`, 2026-08-24T15:11:33Z.

| job | estimated | actual | outcome |
|---|---|---|---|
| `reproduce` | under 1 min | passed | every replay matches §2 of `RESULTS.md` |
| `headroom` | about 2 min | 27 s for 40 rounds | converged, and **corrected the authoring host**, see run 10b |
| `pressure-sweep` | about 5 min | 463 s | same shape and same peak as run 10 |
| `certificate` x2 | under 20 min | **did not finish** | the single-process table build, 83,993 coarse cells and 167,987 midpoints at 50 dps, exceeded the 20-minute job timeout on a shared runner. The estimate assumed the authoring host's 0.0225 CPU-s per cell; the runner is slower per core and the estimate did not carry that. Sharded six ways in run 2 |
| `window-sweep` x4 | 3 epochs per shard | **0 epochs** | all four shards spent the entire 900 s budget on the two reference points and never entered the search. The estimate covered the search and not the setup. Reference points moved into the `doors` job in run 2 |

Two of the five estimates were wrong in the same way: they priced the thing the
job was for and not the thing the job had to do first. That is the same class of
error as run 8's missing estimate, one level up.

## 12. 2026-09-06: the verifier at `b3b7784`, Actions run `34024309937`

Workflow `hunt-amtopa-ceiling` gained a `verifier_commit` input (default `b3b7784`) and a
`certificate_only` switch; branch `hunt/amtopa-verifier-b3b7784`. Tables at the pinned tip
as before; the verifier and `write_verifier_config.py` from a second clone at `b3b7784`;
baseline candidate is the tip's `candidate.json` (the headline's certificate; `b3b7784`'s
own file has target `7897/10^6`). `candidate_data.py` honours `ZETA_CANDIDATE_PATH` at both
revisions; `root-shard.patch` applies at `b3b7784` with `git apply` (offsets 34, 7).

| job | outcome | wall |
|---|---|---|
| headroom | candidate at `19791/2500000`, float minimum `0.00791685780578066` | about 15 min |
| tables x 12 | all passed | a few minutes each |
| certificate, baseline x 8 | `SHARD_VERIFIED` x 8, convex 34,780 to 459,982 | 1 to 19 s each |
| certificate, ours x 8 | `SHARD_VERIFIED` on 0, 3, 6, 7; `INCONCLUSIVE` terminal cell on 1, 2, 4, 5 | 1 to 13 s each |

Refusing cells and rigorous lower bounds: `RESULTS.md` section 7.7. Free minutes on a public
repository; the whole run under an hour of wall clock, against the hour-per-shard the tip
needed to reach nothing.

## 13. 2026-09-06: rounds 2 and 3, the descent, and the candidate withdrawn

The workflow gained a `candidate_file` input: the `headroom` job copies a committed candidate
into place instead of running the LP, so a round is one dispatch and about ten minutes.

| round | candidate | target | Actions run | ours | note |
|---|---|---|---|---|---|
| 2 | `candidate_round2.amtopa`, round-1 cells added to the pool, LP re-solved | `19791/2500000` | `34024961426` | refused 1, 2, 4, 5 at the round-1 cells, bounds identical to twelve digits | the point moved by `5e-9`; the cells were above the target in value, the tangent bound a hair under it |
| 3 | `candidate_round3.amtopa`, same point | `19786/2500000` | `34025675594` | refused 1, 2, 4, 5 at four new cells, 1 to 5 s each | midpoint values `0.0079153` to `0.0079162`, under the LP's claimed floor `0.0079169` |

Baseline: `SHARD_VERIFIED` on 8 of 8 in both rounds, 1 to 19 s per shard, gate alive.

The descent that settled it, on the authoring host, seconds: `epsstar._fun_jac` under
L-BFGS-B at `gtol 1e-14` from each refused cell and from the reported minimum, then a
400,000-seed multistart on `[0.9, 2.3]^6` with 300 descents (19 s). Floor of `F` at the
candidate's own `(a, b)`: `0.0078959857`, confirmed at 40 digits with mpmath. Leader's
`(a, b)` under the same descent: `0.0079111052`, `3e-7` above their accepted target. The
original `harvest` (90,000 seeds, 48 descents, `maxiter` 300) run at the same `(a, b)` returns
`0.0079168578` and never sees the lower basin. Records: `RESULTS.md` section 7.7,
`artifacts/verifier_cells.json`.

Then the LP re-solved with the stronger oracle as its cut generator (400,000 seeds on
`[0.9, 2.3]^6`, 300 descents plus 200 warm starts from the pool, `gtol 1e-14`), from the
committed 2,200-cut pool plus the five true minima, 80 rounds asked, about 13 s a round on
the authoring host (`resolve_strong_oracle.py`). It ran 45 rounds, LP value down from
`0.0079186025` to `0.0079111939` with 14,060 cuts, then HiGHS failed on the next solve
(status 15, `model_status` Unknown, primal feasible) and the process died with nothing
saved but the log. The round-45 bound is monotone and stands: headroom on the two axes at
most `8.9e-8` in `eps` over the leader's floor. Table and reading in `RESULTS.md` section
7.7. Not re-run: the answer is already smaller than anything the headline can see, and a
steadier LP (dropping slack cuts, or `highs-ipm`) is the fix if anyone wants the last digit.

## 14. 2026-09-06: the window axis, three passes and a reversal

The workflow needed one change for a window that is not AMTOPA's: none. Their
`build_interval_tables.py`, `check_window.py` and `write_verifier_config.py` all read the
window from the candidate, and the `candidate_file` input already routes a committed candidate
through headroom, tables and certificate. One fix was needed to the harness itself: the
concurrency group was keyed on `github.ref`, so dispatching a second candidate from the same
branch cancelled the first ten minutes in (runs `34030130604`, `34030138950`). The candidate
is now part of the key.

| pass | what | cost | outcome |
|---|---|---|---|
| 1 | descend at each window's own saved `(a, b)`, strong oracle | 42 s a window | every floor over-reported by `2.6e-5` to `3.0e-5`; all five still above the record |
| 2 | LP re-solved at each window, fresh pool, 40 rounds | about 27 min a window, three at a time | upper and achieved meet to `5e-8`; all five above the record, best `+1.78e-5` |
| 3 | read the cells the verifier refused, then re-measure with that region seeded | 57 to 101 s a window | all five **below** the record, by `1.8e-5` to `3.7e-5` |

Two candidates at the best window, generated by `make_window_candidate.py` and pre-flighted
against their own three scripts on the authoring host (`check_candidate.py`,
`check_final_bound.py`, `check_window.py`, all pass, including the interval enclosure of `H`
at our window and interval positivity `0.7619130192389083`):

| candidate | target | Actions run | ours | baseline |
|---|---|---|---|---|
| A, margin `6.07e-6` | `9263/1250000` | `34030214675` | 6 of 8 accepted; refused on 2 and 4 | 8 of 8 |
| B, margin `3.27e-6` | `18533/2500000` | `34030138950` | 6 of 8 accepted; refused on 2 and 4 | 8 of 8 |

Both refusals are at cells with one gap near `2.91`. The interval Hessian is positive definite
there (smallest eigenvalue `0.15` to `0.17`), the functional at the midpoint is above the
target by `1.5e-6` to `2.5e-6`, and a descent from the cell reaches `2.8e-5` to `5.8e-5`
**below** it. The margin was not the problem; the floor was, for the third time.

Controls, both on the authoring host in about 100 s: the wide oracle at AMTOPA's own window and
weights returns `0.0079111052`, their published value, unchanged to `2e-13`, at their published
basin, with no `2.91` basin present; at our withdrawn pair-weight point it returns
`0.0078946642`, `2.2e-5` under `harvest` and `1.6e-5` under what the record needs. Full account
in `RESULTS.md` section 7.8.

Capstone, `lp_wide.py`, 14 min on the authoring host: the cutting-plane LP re-solved at
AMTOPA's own window and total pressure with the wide oracle as its separation routine. 40
rounds, 13,387 cuts, LP value `0.007912132524`, achieved floor `0.007909735797`, against their
own `0.0079111052`. The LP's best point is worse than theirs by `1.37e-06`. With the smaller
of the two LP upper bounds, `eps*` is bracketed `[0.0079111052, 0.0079111939]`: at most
`8.9e-08` of headroom, `+8.4e-07` on the headline at the top of it. The hunt's question is
answered.
