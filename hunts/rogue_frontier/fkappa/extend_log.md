# Extension log: corrected C_{kappa,i} beyond i = 20

Session date: 2026-08-17. Owner: extension session (extend_*.py,
coefficients_ext.json). Mode: corrected, assembly: coefficient (eq 10.1)
throughout. All arithmetic exact (Fraction). Nothing here is committed to
git by this session.

Targets:
(a) kappa = 2 row to i = 32 or as far as compute allows; per-term bound
    1 - 2 sum_{i<=I} C_{2,i}/((i+1)(i+2)) and |C_{2,i}|^{1/i}.
(b) kappa = 3 row to i = 28+; does the partial bound turn around, and does
    |C_{3,i}|^{1/i} show a limit above or below 1.
(c) diagonal C_{i-2,i} past 20.
(d) structure guessing on the extended corrected kappa = 2 row and diagonal.

Checkpoint discipline: every computed coefficient is written to
coefficients_ext.json immediately (atomic replace) as computed.

## Timeline

- [start] Read RESULTS.md, bian_engine.py, closed_form.py, analyze.py,
  coefficients.json (both modes complete to i = 20). Existing timing:
  corrected level 20 (all six kappa rows + both diagonals, both
  assemblies) took 760 s; growth ~2.5-3.5x per level. Extending the full
  table to 32 with the stock engine is infeasible; a per-row engine plus
  optimizations is required. Profiling next.
- [row2] runner start, imax=21, procs=1, seeds up to i=20
- [row2] i=19: 0.3s gate-ok bound_thru_i=0.953261 root=0.6684 c4=1769
- [row2] i=20: 0.4s gate-ok bound_thru_i=0.953261 root=0.6433 c4=2238
- [row2] i=21: 0.6s NEW bound_thru_i=0.953261 root=0.6066 c4=2832
- [row2] runner done through i=21
- [row2] runner start, imax=34, procs=1, seeds up to i=21
- [row2] i=19: 0.0s gate-ok bound_thru_i=0.953261 root=0.6684 c4=2832
- [row2] i=20: 0.0s gate-ok bound_thru_i=0.953261 root=0.6433 c4=2832
- [row2] i=21: 0.0s gate-ok bound_thru_i=0.953261 root=0.6066 c4=2832
- [row2] i=22: 0.8s NEW bound_thru_i=0.953261 root=0.6161 c4=3509
- [row2] i=23: 1.1s NEW bound_thru_i=0.953261 root=0.5843 c4=4347
- [row3] runner start, imax=28, procs=3, seeds up to i=20
- [row2] i=24: 1.4s NEW bound_thru_i=0.953261 root=0.5731 c4=5302
- [row2] i=25: 1.9s NEW bound_thru_i=0.953261 root=0.5712 c4=6460
- [row2] i=26: 2.4s NEW bound_thru_i=0.953261 root=0.5322 c4=7763
- [row2] i=27: 3.1s NEW bound_thru_i=0.953261 root=0.5414 c4=9318
- [row2] i=28: 3.9s NEW bound_thru_i=0.953261 root=0.5335 c4=11064
- [row3] i=19: 7.6s gate-ok bound_thru_i=-0.855606 root=0.8468 c4=20984
- [row2] i=29: 5.0s NEW bound_thru_i=0.953261 root=0.4735 c4=13118
- [row2] i=30: 6.2s NEW bound_thru_i=0.953261 root=0.5121 c4=15403
- [row3] i=20: 13.4s gate-ok bound_thru_i=-0.855554 root=0.8018 c4=31379
- [row2] i=31: 7.8s NEW bound_thru_i=0.953261 root=0.5009 c4=18060
- [row2] i=32: 10.2s NEW bound_thru_i=0.953261 root=0.4691 c4=21009
- [row2] i=33: 12.3s NEW bound_thru_i=0.953261 root=0.4861 c4=24402
- [row3] i=21: 28.0s NEW bound_thru_i=-0.855550 root=0.7192 c4=46414
- [row2] i=34: 15.0s NEW bound_thru_i=0.953261 root=0.4726 c4=28140
- [row2] runner done through i=34
- [diag] runner start, imax=24, procs=2, seeds up to i=20
- [row3] i=22: 36.2s NEW bound_thru_i=-0.855562 root=0.7704 c4=67410
- [milestone] (a) kappa = 2 row COMPLETE through i = 34 (target was 32).
  Optimized engine (extend_engine.py: canonical sorted DP states,
  run-grouped transitions, restricted-support prof_component) passed the
  correctness gate: gate 0/1/2 all agree (prof_component vs stock,
  _s_sum vs stock on 692 live signature pairs, and full recomputation of
  corrected rows kappa=2,3 + diagonal i<=14 against coefficients.json);
  the runner additionally re-verified every level i<=20 against the
  committed table (gate-ok lines above). Speedup ~26x at i=22.
  Bound trajectory: 0.953313(I=11) -> 0.953261(I=20) ->
  0.953261003869 stable to 12 digits from I=31 on. Term magnitudes
  |C_{2,i}| fall ~8 orders below the i<=11 terms by i=34; the partial
  bound is numerically converged. Root growth |C_{2,i}|^{1/i} drifts
  down through 0.47-0.51 at i=30-34 (even i lower, odd i higher),
  consistent with radius of convergence near or above 2, far above 1.
  Pushing row2 to i=40 for the root trend; row3 and diag runs ongoing.
- [row2] runner start, imax=40, procs=1, seeds up to i=34
- [row2] i=19: 0.0s gate-ok bound_thru_i=0.953261 root=0.6684 c4=28140
- [row2] i=20: 0.0s gate-ok bound_thru_i=0.953261 root=0.6433 c4=28140
- [row2] i=21: 0.0s gate-ok bound_thru_i=0.953261 root=0.6066 c4=28140
- [row2] i=22: 0.0s gate-ok bound_thru_i=0.953261 root=0.6161 c4=28140
- [row2] i=23: 0.0s gate-ok bound_thru_i=0.953261 root=0.5843 c4=28140
- [row2] i=24: 0.0s gate-ok bound_thru_i=0.953261 root=0.5731 c4=28140
- [row2] i=25: 0.0s gate-ok bound_thru_i=0.953261 root=0.5712 c4=28140
- [row2] i=26: 0.0s gate-ok bound_thru_i=0.953261 root=0.5322 c4=28140
- [row2] i=27: 0.0s gate-ok bound_thru_i=0.953261 root=0.5414 c4=28140
- [row2] i=28: 0.0s gate-ok bound_thru_i=0.953261 root=0.5335 c4=28140
- [row2] i=29: 0.0s gate-ok bound_thru_i=0.953261 root=0.4735 c4=28140
- [row2] i=30: 0.0s gate-ok bound_thru_i=0.953261 root=0.5121 c4=28140
- [row2] i=31: 0.0s gate-ok bound_thru_i=0.953261 root=0.5009 c4=28140
- [row2] i=32: 0.0s gate-ok bound_thru_i=0.953261 root=0.4691 c4=28140
- [row2] i=33: 0.0s gate-ok bound_thru_i=0.953261 root=0.4861 c4=28140
- [row2] i=34: 0.0s gate-ok bound_thru_i=0.953261 root=0.4726 c4=28140
- [row2] i=35: 31.4s NEW bound_thru_i=0.953261 root=0.4574 c4=32403
- [row3] i=23: 114.1s NEW bound_thru_i=-0.855564 root=0.7246 c4=96896
- [row2] i=36: 39.0s NEW bound_thru_i=0.953261 root=0.4628 c4=37089
- [diag] i=19: 126.5s gate-ok bound_thru_i=-39257.617847 root=2.3613 c4=56346
- [row2] i=37: 57.7s NEW bound_thru_i=0.953261 root=0.4471 c4=42390
- [observation] alpha-optimization of the (11.5)-reading bound
  b(alpha) = 2 - 1/alpha - 2 sum_i C_{kappa,i} alpha^i/((i+1)(i+2)),
  the same optimization RESULTS.md section 5 applied to the printed
  table, evaluated on the CORRECTED rows (float scan, exact
  confirmation to follow at final depth): kappa = 2 peaks at ~0.9578
  near alpha = 0.972 (above the alpha -> 1 value 0.953261), and
  kappa = 3 peaks POSITIVE at ~0.493 near alpha = 0.746 even though its
  alpha -> 1 partial sums sit at -0.8556. Same truncation caveat as the
  rest of section 5: this is under Bian's own fixed-B reading; the
  i-tail is small at these alpha because the corrected rows decay.
- [row2] i=38: 65.2s NEW bound_thru_i=0.953261 root=0.4419 c4=48183
- [row2] i=39: 92.2s NEW bound_thru_i=0.953261 root=0.4420 c4=54691
- [row3] i=24: 276.4s NEW bound_thru_i=-0.855563 root=0.7176 c4=137218
- [observation] kappa = 2 magnitude scale: against the Farmer-Gonek
  factorial scale FG_i = (k-1)! 2^i/(2k)! (i = 2k+1), the corrected
  kappa = 2 terms satisfy |C_{2,i}|/FG_i in the range 10^1..10^4 for
  i = 5..39 with the i-th root of that ratio drifting DOWN through
  ~1.2 (odd i) and ~1.3 (even i). The row's decay is thus of the same
  factorial type as the entire kappa = 1 row times a slowly-decaying
  geometric-or-polynomial factor; |C_{2,i}|^{1/i} itself falls like the
  kappa = 1 row's root trajectory (~sqrt(e/k) shape), consistent with an
  ENTIRE series in alpha rather than a finite radius. Observed
  behavior only; no identification claimed.
- [check] stock-engine (unpatched bian_engine) spot check on first NEW
  terms: kappa=2 i=21 AGREE; i=22 and kappa=3 i=21 pending.
- [row2] i=40: 86.2s NEW bound_thru_i=0.953261 root=0.4235 c4=61787
- [row2] runner done through i=40
- [milestone] (a) kappa = 2 row now complete through i = 40. Bound
  1 - 2 sum_{i<=I} C_{2,i}/((i+1)(i+2)) fixed at 0.953261003869 (12
  digits) from I = 31 on; |C_{2,i}|^{1/i} down to 0.4235 at i = 40 and
  still falling. Stock-engine spot checks AGREE on new terms i = 21, 22.
- [check] closed-form generating-identity cross-check on a new-size
  inner constant: C((2,2,2,1),(2,2,2,2,2,1)) (norm 18) engine =
  identity = 149/5279735260800, AGREE. Larger pairs abandoned (TPoly
  cost; the stock-engine whole-coefficient checks are the stronger
  gate). Environment note: two unrelated compute jobs from other
  sessions share these 4 cores; timings above are inflated by that.
- [diag] i=20: 415.6s gate-ok bound_thru_i=79806.575974 root=2.3549 c4=97709
- [check] stock-engine spot checks complete: kappa=2 i=21, i=22 and
  kappa=3 i=21 all AGREE with the optimized engine's new terms.
- [diag] gate through i=20 complete (all gate-ok vs committed table);
  entering new territory i=21..24 with 2 workers.
- [row3] i=25: 281.3s NEW bound_thru_i=-0.855563 root=0.6694 c4=192474
- [row3] i=26: 358.3s NEW bound_thru_i=-0.855563 root=0.6888 c4=266630
- [diag] i=21: 773.7s NEW bound_thru_i=-162043.154140 root=2.3485 c4=174946
- [row3] i=27: 409.0s NEW bound_thru_i=-0.855563 root=0.5975 c4=366190
- [row3] i=28: 407.3s NEW bound_thru_i=-0.855563 root=0.6460 c4=497638
- [row3] runner done through i=28
- [milestone] (b) kappa = 3 row COMPLETE through i = 28 (target 28+).
  The partial bound does NOT turn around: it is converged at
  -0.855563 (increments < 2e-6 from I = 24 on; the last four partial
  bounds are -0.855564, -0.855563, -0.855563, -0.855563). At alpha = 1
  the corrected kappa = 3 machinery therefore yields a vacuous
  (negative) bound at every reachable depth, settled well before
  i = 28. |C_{3,i}|^{1/i} trajectory: 0.86 (16) -> 0.80 (20) -> 0.72
  (23) -> 0.60-0.65 (27-28): the limsup is clearly BELOW 1 (radius of
  convergence > 1), so the series converges at alpha = 1 and the
  negative value is what it converges to. The route is not dead,
  however: alpha-optimization (same reading as RESULTS.md section 5)
  reaches a POSITIVE bound ~0.493 near alpha = 0.746 for kappa = 3.
  Exact confirmation of that value at final depth in the report.
- [plan] row3 stopped at 28 by design; diagonal runner restarted with
  procs=4 (row3's cores freed; two foreign jobs still share the box).
- [diag] runner start, imax=24, procs=4, seeds up to i=21
