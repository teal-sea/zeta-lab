1. **T_S was built for ζ on all nine cells, in the module form, not the product-ball form the mission first specified.** The product-ball Π_S of theory §7.3 defines no operator on X_S, where Connes' eq. (22) lives, and its literal formula has infinite trace there (cutoff/ and two_adic/ independently; ordinary argument, unreviewed). The built term is T_S = T_∞ + ΔT on the CCM module form (arXiv:2310.18423 Thm 4.6, used as published): T_∞ from kernel/'s S_∞, which needs no numerically identified prolate data (derivation unreviewed, numerics hardened), and ΔT from two_adic/ in float64 with an error band of 5.3e−3 to 1.6e−2 per (c, N) row. **Grade: measured, weakest step ΔT.**
2. **R_S = Q − T_S measures how much of the 2-adic atom the trace term absorbs: all of its depth, not demonstrably its count.** λ_min moves from −0.30 to −0.49 (product side, Q − T_∞) to −0.026 / −0.039 / −0.097 to −0.12 at c = 2.2 / 2.5 / 2.9. The count below −band is 4, 4, 3 / 4, 9, 20 / 4, 10, 20 at N = 8, 16, 32. At c = 2.9 the rise from 4 to 10 (N = 8 to 16) holds at both 120 and 160 prolate modes, on a last pair 1.4 to 1.5 times the band. At 2.2 and 2.5 the N = 16 count falls as modes rise, and every N = 32 count is confounded with mode truncation. C4's bounded-rank prediction is **neither supported nor decided**; the c = 2.9 evidence runs against it at a resolution that indicates and does not bound. **Grade: measured (checker/, with its own Q), weakest step ΔT.**
3. **Kill-controls: 1, 2 and 4 behave as the mission requires; 3, the positive control, did not run.** (1) The exact (U-S) gate rejects Epstein (1,1,6) at n = 6 (composite atom) and n = 8 (s₃(2) = 6), rejects W_a at n = 2, and accepts ζ and Dedekind ζ_{Q(√−23)} (exact, hardened against numerics `us_check`). (2) The T_S builder refuses W_a's data and Epstein's 2-adic tower (exact). (4) The lesion is refused twice, at the gate and again inside ΔT. (3) Dedekind is **not exercised at S = {∞, 2}**: no idele class character is odd at ∞ and unramified at 2 (operator's ruling). **So every T_S and R_S statement above is about ζ alone, with no positive control beyond ζ itself and the gate, and that limits what lines 1 and 2 may claim.**
4. **Open:** (a) ΔT accurate below Q's smallest eigenvalue (2.6e−4 at c = 2.2, N = 8). The target is not met; prolate-mode truncation binds (4.5e−3, then 1.6e−3, in spectral norm from 80 to 100 to 120 modes), not the Gram step. (b) The N = 32 rows against more modes, which is what decides whether the count at c = 2.5 and 2.9 grows. Both are CI proposals with measured per-unit costs, not run, because they need a push. (c) A proof: module-form C4 needs a semilocal analogue of Connes-Consani's ε(ρ), which does not exist yet (cutoff/). (d) The Dedekind control needs 23 in S, outside this mission.
5. **ALIGNMENT §5: theory §7.3 item 2 refuted** (exact local fact at 2); **product-side C4 refuted** on every c ∈ (2, 3) (ordinary argument, unreviewed; the growing negative index measured by cutoff/ and checker/ independently); **gap (a) closed as a construction**; **module-form C4 at S = {∞, 2} unresolved.** Nothing here is a claim about RH; positivity on these windows is already known (Zhu, arXiv:2608.24827).

# RESULTS: C4 first instance, S = {∞, 2}, semilocal trace remainder on c ∈ [2, 3)

Coordinator's summary, 2026-09-23/24, branch `teal-sea/weil-c4-s2`, nothing
pushed. The five lines above are the mission's verdict. Every number in them
is pinned by a test in the worker folder that owns it (named below); this
file adds no number of its own. Grades follow the `AGENTS.md` ladder, and a
composite claim takes the grade of its weakest step.

## What each folder delivered

| folder | gap | verdict (worker's grade) | where the numbers are pinned |
|---|---|---|---|
| `kernel/` | (a) S_∞ on windows | built; S_∞ with no numerically identified data, T_∞ calibrated against Connes-Consani Thm 6.11 (c* = 14.56 inside their (13, 17)); gap (a) closed as a construction | `kernel/RESULTS.md` lines 1 to 5, `test_sonin.py` |
| `two_adic/` | (b) P_2 through E_S | built; P_2 in closed form on the shared basis, T_S for ζ on nine cells, refusal gate; §7.3 item 2 refuted; accuracy target not met | `two_adic/RESULTS.md` lines 1 to 5, its `test_ta_*.py` |
| `cutoff/` | (c) product ball against module cutoff | gap stated exactly, bound κ = 17 + 12√2 between the product and module terms, product-side C4 refuted | `cutoff/RESULTS.md` lines 1 to 5, `test_cutoff.py` |
| `checker/` | independent Q, R_S, kill-controls | R_S on nine cells with a per-row band; kill-controls 1, 2, 4 run, 3 not exercised; found that two_adic/'s (80, 1200) row is not converged at N = 16 | `checker/RESULTS.md` lines 1 to 5 and §7, `test_checker_*.py` |

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
  guard.
- **Found by checker/:** two_adic/'s interface listed (80, 1200) as converged
  at N = 16; it moves T_S by 7.8e−2 / 4.5e−2 / 2.4e−2 against 120 modes. The
  bands in line 1 include that refinement response where it was measured.

## The doors

1. **Active constraint:** the number of prolate modes in ΔT at the top
   frequencies of each N. Q and T_∞ are known far below float64; the band
   is set by mode truncation, and 12 to 14 of the 20 negatives at N = 32
   live on |n| > N/2, where that truncation concentrates.
2. **Frozen constants:** (nvec, S) per row, chosen to fit the 10-minute
   local limit (two_adic/'s own rule asks for 364 / 319 / 280 modes at
   N = 32); float64 for ΔT; the window c ∈ {2.2, 2.5, 2.9}. Relaxing nvec
   trades only compute. float64 is not what binds while the mode error is
   of order 1e−3 (checker/ §7.6).
3. **Information class:** both CI proposals stay inside the data the
   current construction reads (more modes, larger S). Deciding C4 itself
   needs a new object, the semilocal ε(ρ), which is outside it.

**CI proposals, not run (a push is outside this mission):** two_adic/
§7b, nvec 140 to 200 at S = 4800 with an S = 9600 check, about 40 CPU
minutes in one job; checker/ §7.6, the (240, 2400, 32) unit and the
default-rule rows at N = 32, per unit checkpointed. The 200-mode N = 32
unit took 247 s; the 240-mode unit passed 9.2 CPU-minutes without
finishing, so a CI job should time one unit first.

## Reproduction

From the worktree root, per folder:

```bash
PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n 2 \
  hunts/weil_propagation/c4_s2/<folder> \
  tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py
```
