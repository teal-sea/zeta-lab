# Level 6a: theta_full = 0.02 — the overdraw closed

## Disposition

Level 5 ended with the combined per-pair budget overdrawing by 0.151–0.387
of slack at every depth and two named reversing estimates. Both landed:

```text
theta_full = 0.02  at unit pair density,
ball-hardened caps at every probe depth, worst combined budget 0.9991,
shallow pair charge exactly 0.
```

The directive's milestone equation — rigorous single-pair theta + global
multi-pair closure ⟹ theta_full > 0 — now holds with the labels below,
which are the honest boundary of the claim:

- **caps**: ball-hardened pentadiagonal counting bound (configuration-free
  on the on-line layer), evaluated at seven probe depths spanning the
  strip; the full-ladder hardened penta scan is the named compute follow-up
  (the shallow cells close at 0.57 with charge 0, far from binding);
- **eta**: measured-exact on its adversary family (single-worst-depth
  ordinate lattices at density nu_p = 1, worst phase, optimal split) — the
  configuration-free pair layer is the named level-6b task, with the dense
  pair lattice as its kill control.

The Phase-7 gate (reconnect the gap floor, compute the proportion) remains
closed until 6b; nothing here computes a proportion.

## Lever 1 — the pentadiagonal counting dual

The tridiagonal chain undercharged mid-range pairs: an adjacent-cell pair
at distance 0.2 paid `min omega^2 over [0, 0.5]` = 0.315 against a true
0.77 — the min sits at the far end of a too-wide range. The refinement
keeps the counting theorem's shape and narrows the ranges. Cells of width
`delta` with three charges:

```text
same cell        (d < delta)          : K1 = min omega^2 [0, delta]
adjacent cells   (d < 2 delta)        : K2 = min omega^2 [0, 2 delta]
second neighbours (delta < d < 3delta): K3 = min omega^2 [delta, 3 delta]
```

with `3 delta <= 0.9` keeping every range inside omega's first positive
stretch, and the value solved exactly by a pentadiagonal DP (state =
counts in the last two cells, the third-range interaction folded in as an
upper envelope). Controls: with K3 = 0 it reduces to the level-4 chain
exactly (`< 1e-6` at delta = 0.3125); more charges only lower the value;
and the bound still dominates every measured adversary of levels 3–5.

Measured caps (theta = 0, as fractions of slack, hardened):

| depth | level-5 assumption | penta hardened | needed (1 − eta) |
|---|---|---|---|
| 0.01 | — | 0.571 | 1.000 |
| 0.05 | 0.90 | 0.585 | 0.723 |
| 0.15 | 0.92 | 0.588 | 0.699 |
| 0.25 | 0.92 | 0.595 | 0.699 |
| 0.35 | 0.86 | 0.670 | 0.699 |
| 0.45 | 0.85 | 0.696 | 0.697 |
| 0.49 | 0.85 | 0.680 | 0.699 |

The mid-depth gains (x1.26 at y = 0.25 over the tridiagonal, on top of the
level-5 numbers having been conservative assumptions) are what close the
budget; y = 0.45 is the binding depth with 0.0009 to spare.

## Lever 2 — the optimal charge split, and a bug the controls caught

The split of each negative pair-pair term between its participants is free
in the accounting, and eta is a max over rows, so the right split is a
min-max problem. Solved by iterative reweighting toward equalised row
ratios:

| depth | proportional (level 5) | optimal |
|---|---|---|
| 0.01 | — | **0.000** |
| 0.05 | 0.487 | 0.277 |
| 0.15–0.49 | 0.30–0.44 | 0.30 |

Recorded because it is instructive: the first optimiser *raised* eta to
0.75–0.78 — it summed worst-case lattices over **all** neighbour depths
simultaneously, a density-6nu_p adversary. The ordinate density budget is
nu_p in total, and the row masses are linear in per-depth counts, so the
worst mix is the single worst depth: the charge is a max, not a sum. With
that fixed, the min-max equalises at ~0.30 across the strip and the
shallow end pays exactly zero, which is the depth-graded design doing its
job.

## The verdict

Float scan (fine theta grid):

| theta | worst combined budget | verdict |
|---|---|---|
| 0.00 | 0.992 at y = 0.45 | closed |
| 0.02 | 0.9991 at y = 0.45 | **closed** |
| 0.03 | 1.0027 | open |
| 0.30 | > 1 comfortably | open (power control) |

Ball-hardened at theta = 0.02, all probe depths:

```text
y = 0.01: 0.571   y = 0.05: 0.861   y = 0.15: 0.889   y = 0.25: 0.896
y = 0.35: 0.971   y = 0.45: 0.9991  y = 0.49: 0.980         all closed
```

theta_full = 0.02 is deliberately not optimised further (the directive's
operating rule); its value is that it is positive. The binding margin at
y = 0.45 is 9e-4 of slack — thin, and stated rather than rounded away.

## What stands between this and Phase 7

1. **Level 6b**: the configuration-free pair layer — the counting dual on
   the T kernel at mixed depths, against the dense-pair-lattice kill
   control. The eta side of today's verdict is measured on its adversary
   family, not yet dual-bounded.
2. **The full-ladder hardened penta scan** (compute, not mathematics): the
   probe grid spans the strip and the shallow cells are far from binding,
   but the graduation pipeline wants the ladder.
3. Then Phase 7: the gap floor, every truncation/taper/census term
   one-sided, and the first computation of whether the retained
   `theta_full * Delta_gap` clears the error budget — the question the
   whole hierarchy exists to earn.

## Controls ledger

| control | instrument | measured |
|---|---|---|
| charge ordering and one-sidedness | `test_charges_are_ordered...` | K1 > K2 > K3 >= 0; every range sample above its floor |
| reduction to the level-4 chain | `test_penta_reduces_to_tri...` | agreement < 1e-6 when K3 = 0 |
| monotonicity | `test_penta_never_exceeds_tri...` | penta <= tri on the shared ladder |
| projection (levels 3–5 adversaries) | `test_penta_dominates...` | dominated at every probe depth |
| real gain where the deficit lived | `test_penta_gains...` | < 0.85x tri at y = 0.25 |
| split optimality | `test_eta_optimal_beats...` | max eta 0.303 < proportional 0.487 |
| depth grading | `test_shallow_pairs...` | eta(0.01) = 0.000 |
| verdict power | `test_assembly_open...` | theta = 0.3 fails at the binding depth |
| hardened closure | `test_hardened_assembly...` | closed at probe depths under ball arithmetic |

## Reproduction

```bash
.venv/bin/python hunts/frontier_math/penta_bound.py          # ~1 min
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_penta_bound.py                  # ~45 s
```

The hardened assembly is `penta_bound.hardened_assembly(theta=0.02)`
(~75 s). Deterministic throughout.
