# Runs — `amtopa_ceiling`

Every run of this hunt, including the ones that produced nothing and the one
that had to be killed. Cost estimates were written before the runs they
describe, per the discipline note this hunt was opened under.

The target repository is pinned throughout:

    AMTOPA/zeta-exact-pressure
    commit 7253fdcab9366af45b8c8caf44e408c0af44a1a7
    2026-08-13 17:26:37 +0800  "Add finite check for primitive Gauss transform"

---

## Where the compute lives, and why

The authoring host is a laptop under a hard local-compute cap with a guard that
kills heavy processes, and with no Lean at all. **One run in this hunt broke
that cap and took the operator's session down** (see run 8). After that,
everything beyond a second runs on GitHub Actions, in jobs under 20 minutes with
their own artifacts: `hunts/amtopa_ceiling/ci-sweep.yml`, mirrored to
`.github/workflows/hunt-amtopa-ceiling.yml` so it triggers on this branch.

---

```runmanifest
id: run-1-their-scripts
question: does the published headline reproduce from their own code on the pinned commit
host: authoring laptop
cost_estimate_before: four scripts, seconds each; no estimate needed
cost_actual: under 5 s total
command: |
  git clone https://github.com/AMTOPA/zeta-exact-pressure.git
  git checkout 7253fdcab9366af45b8c8caf44e408c0af44a1a7
  cd src && PYTHONPATH=. python3 check_candidate.py
                PYTHONPATH=. python3 check_final_bound.py
                PYTHONPATH=. python3 check_window.py
outcome: |
  check_candidate.py     candidate_consistency_verified=True
                         pair_weight_span_capacity_verified=True
                         position_pressure_total_verified=True 93/23000
  check_final_bound.py   scan_best_m=145
                         final_bound=0.67341649097149929495003553310749031749977727947556...
  check_window.py        H = 0.6721881581182345851694563877256548411463766196857994939795
                         H_interval encloses it; H_floor_interval_verified=True
                         interval_window_lower_bound = 0.7616418486406763
  Their headline reproduces from their own inputs, exactly as published.
label: MEASURED — their code, our host
```

```runmanifest
id: run-2-exact-assembly
question: is their final projection actually exact, and does it hold in exact rational arithmetic
host: authoring laptop
cost_estimate_before: an integer square root at 200 decimals, times 20000 block lengths; seconds
cost_actual: 3 s
command: python3 hunts/amtopa_ceiling/exact_assembly.py
outcome: |
  Their own check_final_bound.py uses mpmath.mpf at 100 dps and mp.sqrt, which is
  arbitrary-precision FLOAT, not exact and not interval, while README.md and
  proof.md both say "exact arithmetic selects m=145". Redone here in
  fractions.Fraction with math.isqrt giving a rational under-estimate of the only
  square root, and with the monotonicity direction (d(bound)/dR > 0 iff H > B/eps,
  and H - B/eps = 0.16104777081940091048 > 0 here) asserted rather than assumed:

    lower  0.6734164909714992949500355331074903174997772794755665475125243371226272
    upper  0.6734164909714992949500355331074903174997772794755665475125243371226272
    theirs 0.6734164909714992949500355331074903174997772794755665475125243371226272

  70 decimals agree. Exact scan over m in [7, 20000] returns argmax m = 145,
  matching their scan. Their safe floor 0.6734164909 is cleared by 7.14993e-11.
label: VERIFIED — recomputed here in exact rational arithmetic
```

```runmanifest
id: run-3-independent-family
question: does an independent reimplementation of window, kernel and functional agree
host: authoring laptop
cost_estimate_before: numpy, milliseconds
cost_actual: under 2 s
command: python3 hunts/amtopa_ceiling/family.py
outcome: |
  Written from proof.md, importing nothing of theirs.
    H(v)                  ours 0.67218815811823495743  theirs 0.67218815811823458517
                          agree to 15 significant decimals (binary64 limit)
    span capacities       [2, 2, 2, 2, 2, 2] exactly
    K(0)                  0.91872536986556841 ; W(0) = 1 exactly
    F at their published basin (1.978079145369, 1.044055102239, 1.973013931233,
        1.045981098706, 1.974452906922, 1.042299648208)
                          ours 0.007911105155226431  theirs 0.007911105155226424
                          agree to 15 significant decimals
  Their published "observed floating minimum" reproduces here, at their point.
label: VERIFIED — independent reimplementation
```

```runmanifest
id: run-4-window-rayleigh
question: how much window constant can this window family reach, and where is its maximum
host: authoring laptop
cost_estimate_before: a 17x17 linear solve; milliseconds
cost_actual: under 2 s
command: python3 hunts/amtopa_ceiling/probe_window.py
outcome: |
  H(c) = 2 - 1/c1 with c1 = (u.c)^2/(c^T M c) is a Rayleigh quotient, so
  H_max = 2 - 1/(u^T M^{-1} u) in closed form. Computed for 1, 2, 3, 7, 13, 17 and
  25 terms:
      H_max = 0.67250070367941172655 in EVERY case,
      attained at c = (1, 0, 0, ...), i.e. the pure sqrt(2) window.
  Cause, exact: u_j = sinc(w_j/2) = sin(j pi)/(j pi) = 0 for every harmonic, and
  M[0,j] = 0 for every harmonic (computed max |M[0,1:]| = 1.72e-16). The second
  identity is not numerical luck: M[0,j] * 4 j^2 pi^2 D / S reduces to
  2 j^2 pi^2 (w_0^2 - 2)/w_0, which vanishes exactly when w_0 = sqrt(2).
  Cost of a harmonic, from the pure window: dH = -5.6e-7 at c_1 = 1e-3 and
  -5.6e-5 at c_1 = 1e-2, i.e. quadratic, about -0.59 c_j^2.
label: VERIFIED — closed form plus numerical confirmation
```

```runmanifest
id: run-5-pairweight-lp-first-attempt
question: what is the best floor the pair-weight polytope can deliver at their window
host: authoring laptop
cost_estimate_before: one global_min_F unit measured first at 5.0 s; 18 cutting-plane rounds -> 90 s
cost_actual: 57.5 s
command: python3 hunts/amtopa_ceiling/step1_pairweights.py
outcome: |
  Did not converge: after 18 rounds the LP upper bound was 0.0080314603 and the
  best achieved floor 0.0077159782, a gap of 3.2e-4. Recorded because it is the
  run that showed cutting planes alone were too slow, which motivated putting the
  pressure vector into the LP as well (run 6) and stabilising the cut generation.
label: MEASURED — did not converge; superseded by run 9
```

```runmanifest
id: run-6-epsstar-both-axes
question: same question with the pressure vector also an LP variable
host: authoring laptop
cost_estimate_before: 20 rounds at ~1.1 s/round = 22 s
cost_actual: 22.5 s
command: python3 hunts/amtopa_ceiling/step2_epsstar.py 20
outcome: |
  Converged to a gap of 4.4e-8 in 20 rounds. But the reported bracket was
  INCONSISTENT: achieved floor 0.008006338789 above LP upper bound 0.007995158638.
  Two bugs, both found by that inconsistency:
    (a) a proximal term had been added to the LP objective, so res.x[-1] was no
        longer the pure max-t value and was not an upper bound at all;
    (b) the achieved floor was read only off a multistart, which was missing
        basins that the cut pool already contained.
  Shadow prices of the assembly at their operating point, which are correct and
  are reused throughout:
    d(bound)/dH   = +1.007627
    d(bound)/deps = +0.642863
    d(bound)/dB   = -0.964154
    break-even d(eps)/dB      = 1.499781
    break-even d(eps)/d(-H)   = 1.567405
label: MEASURED — shadow prices kept, eps* bracket withdrawn as unsound
```

```runmanifest
id: run-7-pressure-sweep-contaminated
question: the saturation curve on the pressure axis
host: authoring laptop
cost_estimate_before: 15 values at ~30 s each = 7.5 min
cost_actual: 446.8 s
command: python3 hunts/amtopa_ceiling/step3_bsweep.py
outcome: |
  Ran, and its floors were contaminated by bug (b) of run 6. Withdrawn and
  re-run as run 10. Recorded because it is what first showed the marginal
  d(eps*)/dB crossing the break-even between B/B0 = 1.00 and 1.25.
label: WITHDRAWN — superseded by run 10
```

```runmanifest
id: run-8-candidate-generation-killed
question: quantise the LP optimum and pick a rational target
host: authoring laptop
cost_estimate_before: none written — this is the failure
cost_actual: killed at 1.8 GB resident and 70% CPU; took the operator's session down
command: python3 hunts/amtopa_ceiling/make_candidate.py --from-npy ...
outcome: |
  Two faults, one technical and one procedural.
  Technical: ceiling.W_matrix allocated an (N, 21, 17) intermediate, and the
  multistart called it at N = 390000, which is 1.1 GB in one array. Fixed by
  chunking W_matrix at 20000 rows, with the reason written into its docstring.
  Procedural: no unit cost was estimated before the run, in a hunt whose brief
  said to estimate one unit and multiply first. That was the instruction and it
  was not followed.
  Consequence: from this point every computation runs on GitHub Actions.
label: FAILED — process failure, recorded rather than tidied away
```

```runmanifest
id: run-9-headroom-converged
question: eps* at their window and their total pressure, with a sound two-sided bracket
host: authoring laptop
cost_estimate_before: one LP over a 22112-row pool measured at ~10 s
cost_actual: 10 s
command: python3 hunts/amtopa_ceiling/step5_headroom.py 40
outcome: |
  Converged in one round to a gap of 1.6e-17, both bounds meeting:
    eps*(B0, their window) = 0.007919365399
    AMTOPA achieve           0.007911105155   (their float minimum, reproduced)
    their accepted target   0.0079107
  Headroom on the floor: +8.260e-06.
  Assembled at the true H, so that the comparison is like for like:
    at AMTOPA's own floor   0.6734167515492229  (m=145)
    at the polytope optimum 0.6734220612615708  (m=145)
  Against their published headline 0.6734164909714992: +5.570e-06.
  For scale, the one-point pair-weight-free cap eps_diag is 0.0088144556, loose
  by 8.95e-04, which is why the LP and not the single test vector is the
  instrument this hunt reports.
label: MEASURED — LP upper bound rigorous; achieved floor is a float minimum
```

```runmanifest
id: run-10-pressure-sweep
question: the saturation curve on the pressure axis, redone
host: authoring laptop
cost_estimate_before: 15 values, ~55 s each against a 21729-row pool = ~14 min
cost_actual: 850.2 s
command: python3 hunts/amtopa_ceiling/step3_bsweep.py
outcome: |
  B/B0   eps*_lo         eps*_up         bound                m
  0.25   0.0027299930    0.0027305525    0.6730015008061445   385
  0.50   0.0046208925    0.0046209282    0.6732489147583361   235
  0.75   0.0063144596    0.0063145540    0.6733647224807128   177
  0.90   0.0073080619    0.0073080926    0.6734189561133835   155
  1.00   0.0079193654    0.0079193654    0.6734220612615708   145   <- peak
  1.10   0.0084996468    0.0084997253    0.6734052811723370   136
  1.25   0.0093153802    0.0093153802    0.6733453486423939   126
  1.50   0.0106520485    0.0106520488    0.6732318828737838   112
  1.75   0.0119241552    0.0119248361    0.6730788317451036   102
  2.00   0.0131054032    0.0131152353    0.6728700066137836    95
  2.50   0.0151776630    0.0151777768    0.6722757653775309    84
  3.00   0.0172400594    0.0172400990    0.6721105568569956     7
  4.00   0.0213638112    0.0213638713    0.6719283061757414     7
  6.00   0.0296078150    0.0296079214    0.6715628207187594     7
  Marginal floor per unit pressure against the break-even 1.4998:
    0.25->0.50 1.8706 pays | 0.50->0.75 1.6754 pays | 0.75->0.90 1.6382 pays
    0.90->1.00 1.5118 pays | 1.00->1.10 1.4351 COSTS | 1.10->1.25 1.3449 COSTS
    ... falling monotonically to 1.0194 at 4.00->6.00
  The peak of the assembled bound is at B/B0 = 1.00 exactly, i.e. at AMTOPA's own
  B = 93/23000, and the marginal crosses the break-even inside (1.00, 1.10).
label: MEASURED — LP uppers rigorous; floors are float minima
```

---

## Runs on GitHub Actions

`hunts/amtopa_ceiling/ci-sweep.yml`, five jobs, each under a 20-minute timeout
and each uploading its own artifact.

| job | what it settles | unit cost estimated before the run |
|---|---|---|
| `reproduce` | their `run.sh` on the pinned commit, plus runs 2, 3 and 4 in a clean environment | seconds each |
| `headroom` | run 9 re-run from a clean checkout, then the candidate in their schema | ~2 min |
| `pressure-sweep` | run 10 re-run against the shipped 2200-cut pool | ~5 min |
| `certificate` | their table builder and their C++ branch-and-bound, at our candidate and at theirs as a control | table build 64954 cells at 0.0225 CPU-s/cell measured locally = 1462 CPU-s, about 6 min on four vCPU; branch-and-bound 3768186 nodes on their own record |
| `window-sweep` | the 17-dimensional window search, four independent seeds | one surrogate evaluation measured at 0.0388 s; a 26-generation pass at popsize 18 in 17 dimensions is about 8000 evaluations = 5 min per epoch, three epochs per shard |

Outcomes are recorded in `RESULTS.md` section 7.
