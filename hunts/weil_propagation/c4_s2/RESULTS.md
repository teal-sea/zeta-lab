1. **T_S was built for ζ on all nine cells, in the module form, not the product-ball form the mission first specified.** The product-ball Π_S of theory §7.3 defines no operator on X_S, where Connes' eq. (22) lives, and its literal formula has infinite trace there (cutoff/ and two_adic/ independently; ordinary argument, unreviewed). The built term is T_S = T_∞ + ΔT on the CCM module form (arXiv:2310.18423 Thm 4.6, used as published): T_∞ from kernel/'s S_∞, which needs no numerically identified prolate data (derivation unreviewed, numerics hardened), and ΔT from two_adic/ in float64 with an error band of 5.3e−3 to 1.6e−2 per (c, N) row at N = 8 and 16, and **3.0e−2 / 1.4e−2 / 8.2e−3 at N = 32** (c = 2.2 / 2.5 / 2.9). ΔT's explicit Gram inverse was replaced on 2026-09-24 by a QR of the Gram factor (two_adic/ c3dca00): the ill-conditioning came from the s cutoff, not from the functions, and on a test case at cond(G) = 2.6e15 the new route matches a 256-bit reference to 6.8e−9 where the old one was off by 1.6e−2. Under it no eigenvalue of T_S lies below −band on any row, including the 319 and 364-mode rows at N = 32, which the old route broke by 14 to 37 (checker/ s7.8). **Grade: measured, weakest step ΔT.**
2. **R_S = Q − T_S measures how much of the 2-adic atom the trace term absorbs: all of its depth. Its negative count at c = 2.9 grows 4, 10, 20 at N = 8, 16, 32; at 2.5 and 2.2 it does not grow at N = 32.** λ_min moves from −0.30 to −0.49 (product side, Q − T_∞) to −0.026 / −0.039 / −0.097 to −0.12 at c = 2.2 / 2.5 / 2.9. The count below −band is 4, 4 / 4, 9 / 4, 10 at N = 8, 16. At c = 2.9 the rise from 4 to 10 holds at both 120 and 160 prolate modes, on a last pair 1.4 to 1.5 times the band; at 2.2 and 2.5 the N = 16 count falls as modes rise. At N = 32, under the QR rho and by the reading checker/ committed before any rebuilt row was analysed (49db49f): at c = 2.9 the count is **20** on the delivered row and on the 240, 280 and 319-mode rows (21 at 364), the band is two_adic/'s probe (8.2e−3), no refinement moves T_S by more than 4.95e−3, and none of the 12 top-half negatives (−1.45e−2 to −1.21e−2) is shallower than a response. At 2.5 the refined rows count 6 and 5 against 9 at the band 1.4e−2 set by the 319-mode row; at the 240-mode row's band (1.1e−2) they would count 14 and 12, so the 2.5 verdict rests on the band rule (a sensitivity computed after the numbers, labelled as such). At 2.2 every build counts 0. C4's bounded-rank prediction is **not supported at c = 2.9**: the count grows with N at every resolution tried there. That is measured evidence against it, not a refutation: ΔT is measured grade, its band indicates and does not bound, and three values of N are not a limit. (The first build's reading of N = 32 as undecided, from the explicit inverse, is kept in checker/ s7.7.) **Grade: measured (checker/, with its own Q; one route in float64), weakest step ΔT.**
3. **Kill-controls: 1, 2 and 4 behave as the mission requires; 3, the positive control, did not run.** (1) The exact (U-S) gate rejects Epstein (1,1,6) at n = 6 (composite atom) and n = 8 (s₃(2) = 6), rejects W_a at n = 2, and accepts ζ and Dedekind ζ_{Q(√−23)} (exact, hardened against numerics `us_check`). (2) The T_S builder refuses W_a's data and Epstein's 2-adic tower (exact). (4) The lesion is refused twice, at the gate and again inside ΔT. (3) Dedekind is **not exercised at S = {∞, 2}**: no idele class character is odd at ∞ and unramified at 2 (operator's ruling). **So every T_S and R_S statement above is about ζ alone, with no positive control beyond ζ itself and the gate, and that limits what lines 1 and 2 may claim.**
4. **Open:** (a) ΔT accurate below Q's smallest eigenvalue (2.6e−4 at c = 2.2, N = 8): **not met at any mode count from 80 to 200** at S = 4800; no band falls below 6.5e−4, and two_adic/'s extrapolation of 0.36 per 20 modes is refuted (measured ratios 0.53 to 0.80). (b) The c = 2.9 growth is measured, not bounded: turning it into a statement needs ΔT with an error bound rather than a response band. The c = 2.5 count at N = 32 depends on which refined row sets the band. The float64 inverse that blocked N = 32 is fixed (two_adic/ c3dca00). Modal, 2026-09-24, with operator approval: the two compute proposals (0.741 USD; (a) did not meet its target, the first N = 32 build did not decide the count) and the rebuild of all eleven checker/ units under the fixed rho (0.57 USD), 1.31 USD of a 25 USD cap (modal/). (c) A proof: module-form C4 needs a semilocal analogue of Connes-Consani's ε(ρ), which does not exist yet (cutoff/). (d) The Dedekind control needs 23 in S, outside this mission.
5. **ALIGNMENT §5: theory §7.3 item 2 refuted** (exact local fact at 2); **product-side C4 refuted** on every c ∈ (2, 3) (ordinary argument, unreviewed; the growing negative index measured by cutoff/ and checker/ independently); **gap (a) closed as a construction**; **module-form C4 at S = {∞, 2} unresolved**, with measured evidence against its bounded-rank prediction at c = 2.9 (n_− = 4, 10, 20 at N = 8, 16, 32). Nothing here is a claim about RH; positivity on these windows is already known (Zhu, arXiv:2608.24827).

# RESULTS: C4 first instance, S = {∞, 2}, semilocal trace remainder on c ∈ [2, 3)

Coordinator's summary, 2026-09-23/24, branch `teal-sea/weil-c4-s2`, nothing
pushed; lines 1, 2, 4 and 5 updated on 2026-09-24 after the Modal follow-up
and the rho follow-up (`MISSION.md`, last two sections). The five lines above are the mission's verdict. Every mathematical
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
| `two_adic/`, follow-up 2 | the explicit Gram inverse in ΔT | diagnosed (the s cutoff, not the functions), replaced by a QR of the Gram factor, acceptance A1 to A4 fixed before the run and passed | `two_adic/RESULTS.md` s10, `test_ta_rho_diag.py`, `test_ta_rho_check.py`, `test_ta_mellin.py` |
| `modal/` | follow-up: the two compute proposals, then the rebuild under the fixed rho | 12 of 12 units ran on Modal, none timed out, guard passed in every container; outputs and cost only, no mathematical result | `modal/RESULTS.md` lines 1 to 5, `test_modal_outputs.py` |

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
  their own folders against criteria written before the runs. checker/'s
  re-grade made two_adic/'s citations of it stale (2 tests failed); two_adic/
  refreshed them (aa5e3d3). Closing run of all five folders at aa5e3d3:
  438 passed, 10 skipped, 6 xfailed (the 3 strict ones here, and 3 known
  incomplete doors sections of other hunts in `tests/test_hunt_doors.py`).
- **Rho follow-up, 2026-09-24.** Approved by the operator after the Modal
  follow-up ended on the explicit inverse. Sequential by design: changing
  `ta_mellin.py` moves T_S's input digest (1dcab230 to b2e7787b), so
  checker/'s guard refused every old row, N = 8 and 16 included, until all
  eleven units were rebuilt. two_adic/ committed its diagnosis (5b5a311) and
  its acceptance before changing rho; the coordinator's brief had pointed at
  the wrong Gram function (`gram_v`), and two_adic/ corrected it. modal/
  rebuilt all eleven units on Modal (calibration 7.1e−15 against 1e−10,
  estimate committed first, 0.57 USD) and computed no eigenvalue, so
  checker/ committed its reading (49db49f) before any rebuilt row was
  analysed (3e36fa4). The falsifier two_adic/ fixed in advance (T_S at 280,
  319 and 364 modes with no eigenvalue below −band) passed on every cell.
  checker/'s re-grade again made two_adic/'s citations stale; two_adic/
  refreshed them and graded its own s10.4 predictions (a799c3d, 506cbe9):
  all held except the 240-mode row's move at c = 2.2 (2.97e−2, not about
  1e−2). Closing run of all five folders at 506cbe9: 546 passed,
  10 skipped, 6 xfailed (the same 3 strict here and 3 in other hunts).

## The doors

1. **Active constraint:** the accuracy of ΔT, stated as a response band,
   not a bound. At N = 8 and 16 the number of prolate modes binds (two_adic/
   §7b: still binding at 200 modes on c = 2.2, N = 8). At N = 32, after the
   QR rho, the band is set by two_adic/'s probe at c = 2.9 and by the
   refinement response at 2.5 and 2.2; float64 no longer binds there
   (checker/ §7.8). The explicit inverse that did bind is recorded in
   checker/ §7.7.
2. **Frozen constants:** (nvec, S) per row, with S/nvec² as the quantity
   that sets the Gram condition (two_adic/ s10.1); float64 for ΔT; the band
   rule (which refined row sets band(c, 32), which decides c = 2.5); the
   window c ∈ {2.2, 2.5, 2.9}. The explicit inverse is no longer frozen
   (replaced, two_adic/ c3dca00).
3. **Information class:** both compute proposals and the rho fix stayed
   inside the data the current construction reads. A bound on ΔT (rather
   than a band) would too. Deciding C4 itself needs a new object, the
   semilocal ε(ρ), which is outside it.

**Compute proposals: run on Modal, 2026-09-24.** two_adic/ §7b (nvec 140
to 200 at S = 4800, with an S = 9600 check) and checker/ §7.6 (the
(240, 2400, 32) unit and the default-rule rows at N = 32) ran as 12 units,
one Modal call each, checkpointed per unit; per-unit times and costs are in
`modal/RUNS.md`. Not run, and not requested: two_adic/'s next test
((200, 9600) and (220, 9600), estimated at 0.34 USD) and checker/'s optional
240-mode rerun on other BLAS kernels (about 0.08 USD), which would separate
arithmetic from truncation in the 200 to 240 step (superseded: under the QR
rho the platform drift is 3e−12). **Rebuild under the fixed rho, same day:**
all eleven checker/ units in `modal/out_rho/` (`modal/RUNS.md` s7), 0.57 USD;
`modal/out/` is kept as the record of the old route.

## Reproduction

From the worktree root, per folder:

```bash
PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n 2 \
  hunts/weil_propagation/c4_s2/<folder> \
  tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py
```
