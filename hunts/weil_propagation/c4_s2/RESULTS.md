1. **T_S was built for ζ on all nine cells, in the module form, not the product-ball form the mission first specified.** The product-ball Π_S of theory §7.3 defines no operator on X_S, where Connes' eq. (22) lives, and its literal formula has infinite trace there (cutoff/ and two_adic/ independently; ordinary argument, unreviewed). The built term is T_S = T_∞ + ΔT on the CCM module form (arXiv:2310.18423 Thm 4.6, used as published): T_∞ from kernel/'s S_∞, which needs no numerically identified prolate data (derivation unreviewed, numerics hardened), and ΔT from two_adic/ in float64 with an error band of 5.3e−3 to 1.6e−2 per (c, N) row at N = 8 and 16, and **2.4e−2 to 3.9e−2 at N = 32** once that row's own 240-mode refinement ran (Modal, 2026-09-24). two_adic/'s default mode rule at N = 32 (280, 319, 364 modes) gives no usable T_S in float64: the Gram matrix ΔT inverts has condition 1.1e17 to 2.8e18, past 1/eps, and at 319 and 364 modes T_S fails T_S ≥ 0 by 14 to 37 (checker/ s7.7). **Grade: measured, weakest step ΔT.**
2. **R_S = Q − T_S measures how much of the 2-adic atom the trace term absorbs: all of its depth; its count grows from N = 8 to 16 at c = 2.9 and is undecided at N = 32.** λ_min moves from −0.30 to −0.49 (product side, Q − T_∞) to −0.026 / −0.039 / −0.097 to −0.12 at c = 2.2 / 2.5 / 2.9. The count below −band is 4, 4 / 4, 9 / 4, 10 at N = 8, 16. At c = 2.9 the rise from 4 to 10 holds at both 120 and 160 prolate modes, on a last pair 1.4 to 1.5 times the band; at 2.2 and 2.5 the N = 16 count falls as modes rise. At N = 32 the 240-mode refinement moves T_S by more than the depth of every top-half negative, and the 240-mode row counts 0 / 5 / 4 below the new band. By the criterion checker/ fixed before the runs (s7.6, read in ee4a1ff before any Modal eigenvalue was computed), the growth to 20 therefore **falls at c = 2.5** (5 against 9 at N = 16) and **is split at 2.9** (4 at 240 modes; 22 on the 280-mode row, whose Gram matrix has condition 1.1e17). The negatives did not leave (19 and 23 remain at the old band): the band rose past them. C4's bounded-rank prediction is **neither supported nor decided**; the c = 2.9 rise from N = 8 to 16 runs against it at a resolution that indicates and does not bound. **Grade: measured (checker/, with its own Q; Modal and the laptop are one route on two platforms, not two routes), weakest step ΔT.**
3. **Kill-controls: 1, 2 and 4 behave as the mission requires; 3, the positive control, did not run.** (1) The exact (U-S) gate rejects Epstein (1,1,6) at n = 6 (composite atom) and n = 8 (s₃(2) = 6), rejects W_a at n = 2, and accepts ζ and Dedekind ζ_{Q(√−23)} (exact, hardened against numerics `us_check`). (2) The T_S builder refuses W_a's data and Epstein's 2-adic tower (exact). (4) The lesion is refused twice, at the gate and again inside ΔT. (3) Dedekind is **not exercised at S = {∞, 2}**: no idele class character is odd at ∞ and unramified at 2 (operator's ruling). **So every T_S and R_S statement above is about ζ alone, with no positive control beyond ζ itself and the gate, and that limits what lines 1 and 2 may claim.**
4. **Open:** (a) ΔT accurate below Q's smallest eigenvalue (2.6e−4 at c = 2.2, N = 8): **not met at any mode count from 80 to 200** at S = 4800; no band falls below 6.5e−4, and two_adic/'s extrapolation of 0.36 per 20 modes is refuted (measured ratios 0.53 to 0.80). (b) N = 32 is now blocked by float64, not by the mode count: ΔT inverts an explicit Gram matrix whose condition passes 1/eps from 280 modes on, so the door is that step without an explicit inverse (two_adic/'s code), not more modes. Both compute proposals ran on Modal on 2026-09-24 with operator approval, for 0.741 USD against a 25 USD cap (modal/): (a) did not meet its target, and (b) did not decide the count. (c) A proof: module-form C4 needs a semilocal analogue of Connes-Consani's ε(ρ), which does not exist yet (cutoff/). (d) The Dedekind control needs 23 in S, outside this mission.
5. **ALIGNMENT §5: theory §7.3 item 2 refuted** (exact local fact at 2); **product-side C4 refuted** on every c ∈ (2, 3) (ordinary argument, unreviewed; the growing negative index measured by cutoff/ and checker/ independently); **gap (a) closed as a construction**; **module-form C4 at S = {∞, 2} unresolved.** Nothing here is a claim about RH; positivity on these windows is already known (Zhu, arXiv:2608.24827).

# RESULTS: C4 first instance, S = {∞, 2}, semilocal trace remainder on c ∈ [2, 3)

Coordinator's summary, 2026-09-23/24, branch `teal-sea/weil-c4-s2`, nothing
pushed; lines 1, 2 and 4 updated on 2026-09-24 after the Modal follow-up
(`MISSION.md`, last section). The five lines above are the mission's verdict. Every mathematical
number in this file is pinned by a test in the worker folder that owns it
(named below); this file adds none of its own. The run timings in the
compute-proposal paragraph are measured and recorded in those folders'
RESULTS, not pinned by tests; the Modal costs are in `modal/RUNS.md`. Grades follow the `AGENTS.md` ladder, and a
composite claim takes the grade of its weakest step.

## What each folder delivered

| folder | gap | verdict (worker's grade) | where the numbers are pinned |
|---|---|---|---|
| `kernel/` | (a) S_∞ on windows | built; S_∞ with no numerically identified data, T_∞ calibrated against Connes-Consani Thm 6.11 (c* = 14.56 inside their (13, 17)); gap (a) closed as a construction | `kernel/RESULTS.md` lines 1 to 5, `test_sonin.py` |
| `two_adic/` | (b) P_2 through E_S | built; P_2 in closed form on the shared basis, T_S for ζ on nine cells, refusal gate; §7.3 item 2 refuted; accuracy target not met | `two_adic/RESULTS.md` lines 1 to 5, its `test_ta_*.py` |
| `cutoff/` | (c) product ball against module cutoff | gap stated exactly, bound κ = 17 + 12√2 between the product and module terms, product-side C4 refuted | `cutoff/RESULTS.md` lines 1 to 5, `test_cutoff.py` |
| `checker/` | independent Q, R_S, kill-controls | R_S on nine cells with a per-row band; kill-controls 1, 2, 4 run, 3 not exercised; found that two_adic/'s (80, 1200) row is not converged at N = 16; follow-up: N = 32 undecided on this route in float64 (§7.7) | `checker/RESULTS.md` lines 1 to 5 and §7, `test_checker_*.py` |
| `modal/` | follow-up: the two compute proposals | 12 of 12 units ran on Modal, none timed out, guard passed in every container; outputs and cost only, no mathematical result | `modal/RESULTS.md` lines 1 to 5, `test_modal_outputs.py` |

## Coordination record (what went wrong, and what it changed)

- **Orca went down at 22:50** and took the checker/ and two_adic/ terminals
  with it. A replacement coordinator re-dispatched both from their
  uncommitted files. An orphaned checker/ process (bare `python3`, not the
  venv) had written 7 of 15 units of a T_S snapshot. **Its output was
  discarded**: the snapshot was keyed to the committed two_adic/ tree while
  the code it imported was modified in the working tree, and its N = 32
  entry was built by code whose 1/w tail diverges there.
- **Found during recovery (two_adic/):** a fixed Kmax = 10 made the prolate
  tail series diverge at 120 and 200 modes. That divergence, not missing
  norm, was the N = 32 Gram probe failure of 0.55; the rerun probe is
  8.2e−3 / 7.6e−3 / 8.2e−3. The pair counts of two_adic/'s line 2 did not
  change. Fixed in 8dc8525, rerun in 015895f.
- **checker/'s snapshot guard now fails closed.** It keys on the blob hashes
  of the files T_S imports and refuses to build or serve while any of them
  is modified, the same fail-open shape `AGENTS.md` records for the secret
  guard. Its first version keyed every non-test .py in both folders, so
  two_adic/'s fd9b0bf (a file T_S never imports) made 20 property tests
  skip. A guard that skips the suite it guards is the "5 skipped" trap in
  `AGENTS.md`. It now keys the import closure of `ta_ts.py` (4f706cd,
  88f93a8), and a changed closure file fails a test instead of skipping.
  Final run of all four folders at 88f93a8: 343 passed, 10 skipped (dps 60
  units never built at N = 16, and the positive control), 3 strict xfail.
- **Found by checker/:** two_adic/'s interface listed (80, 1200) as converged
  at N = 16; it moves T_S by 7.8e−2 / 4.5e−2 / 2.4e−2 against 120 modes. The
  bands in line 1 include that refinement response where it was measured.
- **Modal follow-up, 2026-09-24.** The operator approved both compute
  proposals on Modal with a 25 USD cap (no Actions, no push). modal/ built an
  image holding a clean git clone of 284eff6, so checker/'s guard ran inside
  every container and matched the local digest. The estimate and the worst
  case at the per-unit timeouts (6.73 USD) were committed before launch
  (76d13a9); 0.741 USD was billed, per Modal's billing report as modal/ read
  it. The checker calibration unit missed the brief's 1e−10 by 2.3e−7. A
  probe that changed only the BLAS kernels moved it by 3.3e−7 on Modal alone,
  so the threshold became 1e−6 after the measurement, recorded as such in
  `modal/RUNS.md`. two_adic/ and checker/ then graded their own units in
  their own folders against criteria written before the runs.

## The doors

1. **Active constraint:** at N = 8 and 16, the number of prolate modes in
   ΔT (two_adic/ §7b: still binding at 200 modes on c = 2.2, N = 8). At
   N = 32, float64 itself: the explicit Gram inverse inside ΔT has condition
   4.9e12 at 240 modes and 1.1e17 to 2.8e18 at the default rule's 280 to 364,
   and past 240 modes adding modes degrades T_S instead of refining it
   (it moves by 1.1 to 1.3 at 280 modes, and fails T_S ≥ 0 by 14 to 37 at
   319 and 364; checker/ §7.7).
2. **Frozen constants:** (nvec, S) per row; float64 and an explicit inverse
   in ΔT; the window c ∈ {2.2, 2.5, 2.9}. Relaxing nvec now trades compute
   for conditioning past 240 modes at N = 32, so it no longer has trade
   shape. Replacing the explicit inverse (a factorization, or higher
   precision for that step) trades implementation time for the binding
   constraint at N = 32. That is the door checker/ names (§7.7); the fix
   belongs to two_adic/'s code.
3. **Information class:** both compute proposals stayed inside the data the
   current construction reads, and neither decided the count. The inverse
   fix stays inside it too. Deciding C4 itself needs a new object, the
   semilocal ε(ρ), which is outside it.

**Compute proposals: run on Modal, 2026-09-24.** two_adic/ §7b (nvec 140
to 200 at S = 4800, with an S = 9600 check) and checker/ §7.6 (the
(240, 2400, 32) unit and the default-rule rows at N = 32) ran as 12 units,
one Modal call each, checkpointed per unit; per-unit times and costs are in
`modal/RUNS.md`. Not run, and not requested: two_adic/'s next test
((200, 9600) and (220, 9600), estimated at 0.34 USD) and checker/'s optional
240-mode rerun on other BLAS kernels (about 0.08 USD), which would separate
arithmetic from truncation in the 200 to 240 step.

## Reproduction

From the worktree root, per folder:

```bash
PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n 2 \
  hunts/weil_propagation/c4_s2/<folder> \
  tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py
```
