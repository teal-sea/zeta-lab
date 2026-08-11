# Level 6b: the density question — the two adversaries exclude each other

## Disposition

Level 6a's theta_full = 0.02 carried the label "at unit pair density".
This level asks what happens when the density is the adversary's to
choose, and the answer has a structure worth stating before the numbers:
**the on-line adversary and the pair-density adversary cannot both show
up.** Dense pair clusters are nearly immune to on-line attack (the
compensation factor collapses tenfold from nu_p = 1 to 2), and they pay
their own stacking; sparse pair layers are on-line-vulnerable but produce
little pair-pair negativity. The joint budget, measured across the whole
interpolation, holds everywhere — worst margin **+0.0704** exactly at the
pinch (nu_p = 1.5, deep) where the separable accounting had broken by
−0.60.

theta_full = 0.02 is thereby corroborated at the joint level across all
tested densities. The honest labels are in the last section; the Phase-7
gate stays closed.

## The separable budget breaks, and that record is kept

Summing the level-6a per-pair hardened caps is valid (each damage term
belongs to one pair's row), giving the global requirement
`sum T_signed >= - sum (1 - capfrac) slack`. Measured across lattice
families (nu_p = 0.5–3, four depths, three phases) and the collective
battery: **24 of 68 configurations break it**, worst at nu_p = 1.5,
y = 0.49 with margin −0.599. Deep mid-density lattices maximise pair-pair
negativity (T/slack = −0.92) while the budget offers only 0.32. If the
per-pair caps were simultaneously attainable, theta_full would be dead at
those densities — the level-5 lesson repeating one level up.

## The compensation factor: why they are not simultaneously attainable

A single on-line configuration cannot deal every pair its worst case: a
zero at one pair's most negative offset (g* ~ 0.7) sits in a neighbouring
pair's positive region when the pairs are 0.5–0.8 apart. Measured (greedy
joint on-line adversary against whole lattices, theta = 0.02):

| nu_p | chi = joint damage / summed caps |
|---|---|
| 1.0 | 0.139–0.174 |
| 2.0 | **0.016–0.018** |

At unit density the joint attack already reaches only ~15% of the summed
caps; at density 2 it is one-sixtieth. Density is a defensive liability
for the adversary's own pair layer.

## The joint budget across the interpolation

`used = joint on-line profit/slack + max(0, -T_signed)/slack` against 1:

| nu_p | y = 0.35 | y = 0.45 | y = 0.49 |
|---|---|---|---|
| 0.75 | +1.170 | +1.122 | +1.092 |
| 1.00 | +1.251 | +1.569 | +1.710 |
| 1.25 | +0.100 | +0.076 | **+0.074** |
| 1.50 | +0.187 | +0.089 | +0.070 |
| 2.00 | +0.397 | +0.162 | +0.117 |
| 3.00 | +0.828 | +0.324 | +0.226 |

(entries are margins, 1 − used). The trade-off curve pinches at
nu_p ~ 1.25–1.5 deep — T-negativity near its maximum while the on-line
attack is already collapsed — and clears by 7%. On both flanks the margin
grows: sparse layers have positive T (stacking-dominant), dense layers pay
their stacking and blind the on-line attack further.

## The stacking floor (the provable seed)

One-sided, all depth pairs on the probe grid, grid + Lipschitz margin:

```text
T(dt, y, y') >= +2.78   for |dt| <= 0.2,     dies by delta_p = 0.3
                                              (at the strip edge, mapped)
```

Every same-window pair the adversary adds pays this floor — the third
instance of the self-defeat pattern (depth paid quartic slack at level 3,
on-line density paid quadratic packing at level 4, pair density pays
stacking here).

## Honest labels

- The **T-side is exact** for the tested lattices, and the family sweep
  covers the battery shapes; but it is a family, not all configurations.
- The **joint on-line profit is a greedy measured adversary** — a lower
  bound on the true joint supremum. The +0.07 pinch margin is against the
  greedy; a cleverer joint attack could be stronger. The named theorem
  object is therefore the **joint cap**: an on-line counting dual against
  a cluster of pairs (the level-4 machinery with the damage field summed
  over pair centres), which would upper-bound the joint profit and convert
  this measured verdict into a configuration-free one. Nothing about the
  mechanism suggests the greedy is far from the sup — the collapse of chi
  is geometric (band overlap), not adversary-weakness — but that is an
  argument, not a bound.
- Mixed-depth lattices are covered only through the battery shapes; the
  depth-split machinery of level 5 applies but has not been rerun jointly.
- No proportion is computed. The Phase-7 gate stays closed behind the
  joint cap dual and the full-ladder hardened scan.

## Controls ledger

| control | instrument | measured |
|---|---|---|
| stacking floor positive at working width | `test_stacking_floor_is_positive...` | +2.78 one-sided at delta_p = 0.2 |
| floor boundary mapped honestly | `test_stacking_floor_boundary...` | dies at 0.3, at the strip edge |
| separable budget breaks where expected | `test_separable_budget_breaks...` | worst −0.599 at deep mid-density |
| compensation collapse | `test_compensation_collapses...` | chi: 0.15 -> 0.017 from nu 1 to 2 |
| joint budget across the sweep | `test_joint_budget_holds...` | worst margin +0.0704 > 0.05 |
| cap table consistency | `test_capfrac_lookup...` | matches level 6a |

## Reproduction

```bash
.venv/bin/python hunts/frontier_math/pair_density.py        # ~2 s
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_pair_density.py                # ~5 s
```
