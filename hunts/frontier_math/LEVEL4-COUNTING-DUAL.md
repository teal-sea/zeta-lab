# Level 4: the counting dual — theta > 0, configuration-free

## Disposition

Level 3 left two named gaps in promotion order: a bound on the adversary's
value valid over **all** configurations (its worst case was measured over
two families), and the multi-pair slack partition. This level closes the
first with an elementary counting theorem whose one-sided evaluation
delivers

```text
secured theta* = 0.1   (grid; worst depth-cell margin +1e-5, which is
                          ~10% RELATIVE to that shallow cell's slack)
```

for the level-3 per-pair inequality with the adversary side now
configuration-free, and reduces the second to a measured frame with the
remaining step named. The gap between the secured 0.1 and level 3's
measured 0.9 is the counting bound's documented looseness (dropped
non-adjacent payments, cell sups), not a change in the mathematics.

## The theorem (the "rational dual object" of the hierarchy row)

Partition the offset line into cells of width `delta`. For any finite
configuration `X`:

- same-cell pairs are within `delta`, so each pays internal mass at least
  `K_delta = min over [0, delta] of omega^2`;
- adjacent-cell pairs are within `2 delta`, so each pays at least
  `K_{2delta}`;
- non-adjacent payments are dropped — one-sided in the adversary's favour.

With `F_j >= sup over cell j of f+` (`f = -2W` is the damage) and
`c = 1 - theta`, the adversary's value is at most

```text
max over n_j >= 0 of  sum_j [ n_j F_j - c K_delta n_j(n_j - 1)
                              - c K_{2delta} n_j n_{j+1} ],
```

a tridiagonal chain program solved **exactly** by dynamic programming over
the cell chain. The chain term is what secures: without it (equivalently,
`delta` past the first zero of `omega`, where `K_{2delta} = 0`) the bound's
free density is `1/delta` and the securing scan fails by an order of magnitude
(`test_chain_charge_beats_the_plain_bound`: 19.2 vs the plain bound at
`y = 0.45`). At `theta = 1` every charge vanishes and the cap is infinite —
matching level 3's dense-regime failure exactly.

## One-sided cells (the "one-sided continuum cell bounds")

Cell sups of the damage come from closed-form centre values of
`C = Re Phi2(g+iy)`, `S = -Im Phi2(g+iy)` inflated by elementary
Cauchy–Schwarz Lipschitz constants:

```text
|dS/dg| <= (L/2) aL sigma(y)     |dC/dg| <= (L/2) aL E(y)
|dS/dy| <= (L/2) aL E(y)         |dC/dy| <= (L/2) aL sigma(y)
```

so `f+ <= 4 (Sbar^2 - Cund^2)+ / (aL)^2` holds on the whole `(g, y)` cell.
The sup-evaluation grid (step 0.0125, inflation ~2–4% of `|S|`) is
decoupled from the capacity partition `delta` — coupling them was the first
implementation's fatal looseness. Beyond the fine region the far tail uses
the *depth-scaled* majorant

```text
|S| <= psi_S(y)/g^2,
psi_S = (c_rho/w) sinh(yL/2) + 4 y cosh(yL/2) + y^2 aL sinh(yL/2)
```

(`||(phi^2 sinh(y.))''||_1` via the paper's (2.13) norms), which vanishes
linearly in `y` — a depth-blind tail majorant would silently fail the
shallow depth cells, where the slack vanishes too. The depth ladder is
geometric with ratio 1.18 refined to 1.04 from `y = 0.09`, and the slack is
always evaluated at the shallow lip of each depth cell while damage is
inflated to the deep lip.

## The soundness incident, recorded because it is instructive

The first implementation *failed its own projection control*: the measured
level-3 lattice adversary exceeded the "bound" at two depths. The leak was
a factor-2 error in the damage (`f = -2W` carries factor 4 against the
`C/S` split, not 2) hidden inside otherwise-plausible margins. The control
that caught it is the hierarchy's own level-4 row — *projection to every
lower level must reproduce its controls* — and it is now a permanent test
(`test_bound_dominates_level3_adversaries`). A bound that had only been
compared against its own cells would have shipped wrong.

## Measured record

| theta | worst depth-cell margin | verdict |
|---|---|---|
| 0.0 | +1e-5 (binding cells are shallow; ~10% relative) | OK |
| 0.1 | +1e-5 | OK |
| 0.2 | −0.261 | fails (mid-depth cells `y ~ 0.15–0.29`) |
| 0.5 | −9.82 | fails |

- **Domination** (projection rule): measured level-3 profits 0.138 / 1.889
  / 6.998 at `y = 0.1 / 0.3 / 0.45` sit under caps 0.191 / 3.901 / 19.230.
  The level-2 `+-g*` cluster and the single-point LAW I reduction are also
  dominated (tests).
- **Lesion**: dropping the Lipschitz inflation produces genuine sup
  violations (0.115 / 0.347 / 0.725 at the three probe depths) — the
  inflation is load-bearing, not decorative.
- **Tightness**: at `y = 0.1` the cap is within 39% of the measured
  adversary; at `y = 0.45` within 2.7x. The looseness is concentrated at
  depth, where the dropped non-adjacent payments matter most.

## Gap 2: the halved-slack partition frame

Charging each pair-pair interaction half to each participant against half
of each pair's `8 sigma^2 + 8 sigma^4` slack:

| depths | worst T | half budget | fits |
|---|---|---|---|
| (0.30, 0.30) | −2.84 | 4.94 | yes |
| (0.45, 0.45) | −16.34 | 22.70 | yes |
| (0.49, 0.20) | −5.37 | 17.84 | yes |

Stacked pairs (coincident ordinates) are positive (+8.94, +25.58), so
pair-density concentration is self-defeating, as on-line density was. The
remaining step is the pair-pair analogue of this module's cell bound at
combined depths `y ± y'` — the same machinery, one more layer — and it
stays **named, not claimed**.

## What is and is not delivered

Delivered: the counting theorem (exact, elementary); its one-sided
evaluation securing `theta = 0.1` configuration-free at the single-pair
reduction; the chain mechanism identified as the load-bearing sharpening;
the projection/lesion control suite; the partition frame with measured
coverage.

Not delivered, named in promotion order: (i) the arb-enclosure pass over
the same finitely many cells (evaluation is double precision with the
inflation margins doing the one-sided work — the binding margins are ~10%
relative, far above float noise, but the enclosure pass is what the
graduation pipeline requires); (ii) the theta gap 0.1 → 0.9 (the moment
problem over the psd kernel `FT[omega^2] >= 0`, which the counting bound
deliberately avoids needing); (iii) the multi-pair closure. No proportion
is computed; the Phase-6 gate stays closed.

## Reproduction

```bash
.venv/bin/python hunts/frontier_math/counting_bound.py      # ~5.5 min
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_counting_bound.py              # ~40 s
```

Deterministic throughout: fixed grids, exact DP, no random search.
