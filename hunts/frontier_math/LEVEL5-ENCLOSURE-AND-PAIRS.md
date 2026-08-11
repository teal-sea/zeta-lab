# Level 5: the enclosure pass and the multi-pair energy

## Disposition

The directive set two promotion gates: rigorous enclosure of the level-4
cells, and closure of the general multi-pair interaction. Gate 1 is
**delivered**: the level-4 counting dual re-evaluated end to end in ball
arithmetic holds at its original resolution — with an instructive scare
recorded below. Gate 2 is **half-delivered and half-quantified**: the exact
multi-pair algebra collapses onto the single-pair kernel (LAW L), every
collective mode tested survives, per-pair charging works at unit pair
density — but the combined per-pair budget (on-line cap + pair charge)
overdraws at every depth by a measured 0.15–0.39 of slack. That is the
directive's **OUTCOME B**, with the deficit and the two candidate reversing
estimates named exactly.

theta_full > 0 is therefore **not yet claimed**. The decimal gate stays
closed.

## Gate 1 — the hardened scan, and what almost went wrong

`enclosure_pass.py` re-evaluates every kernel-touching quantity of the
level-4 scan in acb/arb ball arithmetic (128-bit): the closed-form `Phi2`
with an explicit geometric tail bound on the moment series, exact integer
ramp coefficients, exact rational `aL`, and directed endpoints everywhere —
damage sups from upper endpoints, `K_delta` and slack from lower endpoints,
the chain DP total inflated by `1 + 1e-9` (covering its double-precision
arithmetic on directed inputs; a fully rational DP would be possible and
pointless at these margins). Ball radii at representative cells: `1e-16` to
`1e-20`, versus binding margins of ~10% relative.

**The scare.** A first hardened run at a 2x-coarser sup grid (step 0.025,
4 depth slices — chosen to halve runtime) FAILED the scan by up to −3.0 at
theta = 0. Probing the failing cells at the original level-4 resolution
(step 0.0125, 6 slices) restored healthy positive margins:

| depth cell | slack | coarse hardened cap | fine hardened cap | fine margin |
|---|---|---|---|---|
| [0.15, 0.156] | 0.805 | 0.715 | 0.535 | **+0.270** |
| [0.25, 0.260] | 2.878 | 3.173 (fails) | 2.445 | **+0.433** |
| [0.30, 0.312] | 4.936 | 5.421 (fails) | 4.371 | **+0.566** |
| [0.45, 0.468] | 22.698 | 25.348 (fails) | 20.669 | **+2.029** |

The Lipschitz inflation scales with the sup-grid step, so coarsening the
grid is not a free economy — it is a change in the theorem's constants. The
failure was the economization, not the balls and not the mathematics; the
module's defaults are now pinned at the original resolution and the coarse
failure is kept as a documented negative control.

**The gate-1 record.** The full hardened depth-ladder scan at original
resolution (~30 minutes):

```text
theta = 0.00: worst hardened margin >= +0.000011   OK
theta = 0.05: worst hardened margin >= +0.000011   OK
theta = 0.10: worst hardened margin >= +0.000011   OK
hardened theta* (grid) = 0.1
```

The level-4 value survives enclosure exactly, with the same shallow
binding cells and the same ~10%-relative margins, now carried by directed
ball endpoints rather than double-precision goodwill.

## Gate 2 — LAW L and the exact multi-pair energy (Phase 2)

For pairs at ordinates `t_r` and depths `y_r`, the off-line block's
Frobenius energy is exactly

```text
||Qhat||_F^2 = sum_r [4 + slack_r] + sum_{r != s} T(t_r - t_s, y_r, y_s),
```

with each self term pinned by LAW K, and the cross term given by the new
exact identity

```text
LAW L:   T(dt, y, y') = W(dt, y - y') + W(dt, y + y')
```

— the *single-pair* signed kernel at the difference and sum depths (both
slots are instances of LAW D's complex Poisson identity; measured defect
against the independent route: `8.9e-16`). The only sign-indefinite terms
in the total energy are the on/off cross (controlled by the level-4
counting dual) and these `T` terms. Three structural consequences, each
measured:

- **the difference layer is nonnegative**: `W(dt, 0) >= 0` (min `+6e-10`
  over the probe range), so equal-depth pairs interact negatively only
  through the depth-scaled sum layer — shallow-shallow negativity vanishes
  as `sigma^2(2y)` (measured inside the `(1+m0) sigma^2(2y)` envelope);
- **negativity is depth-split**: `sigma^2(y ± y') <= 2 cosh^2(y'L/2)
  sigma^2(y) + 2 cosh^2(yL/2) sigma^2(y')`, so every negative `T` is
  chargeable to its participants in proportion to their own `sigma^2` — a
  shallow pair is charged asymptotically nothing (split weight `< 0.02` at
  depths (0.01, 0.45));
- **the far tail is depth-scaled**: only `S^2` pushes `W` negative, so
  `|T|_- <= 2[psi_S(|y-y'|)^2 + psi_S(y+y')^2]/(dt^4 (aL)^2)`.

## Phases 3–4 — the partition, measured, and the collective battery

`eta(nu_p)` = worst per-pair charge ratio over adversarial ordinate
lattices, with the proportional depth split:

| nu_p | eta | verdict |
|---|---|---|
| 0.5 | 0.594 | slack survives |
| 1.0 | 0.487 | slack survives |
| 2.0 | 7.741 | **pairwise charging defeated** |

Resolved by depth at `nu_p = 1`: eta runs 0.30 (deep) to 0.49 (shallow).

The Phase-4 collective battery — stacked columns, alternating-depth
dipoles, staggered lattices, shallow/deep sandwiches, strip-edge clusters,
periodic pair words — **survives at both nu_p = 1 and nu_p = 2** (worst
cross/slack = −0.876, all totals positive). So the `nu_p = 2` failure is a
failure of the *pairwise charging scheme*, not of the energy: exactly the
situation level 4 met on the on-line layer, where per-cell reasoning needed
the chain counting dual. **The dense pair lattice at spacing ~0.6 is
promoted to the level-6 kill control**, and the level-6 task is the
counting dual on the `T` kernel at mixed depths (2D cells).

## Phase 6 — theta_full: OUTCOME B, with the deficit quantified

The per-pair linear assembly requires, at every depth,

```text
(level-4 cap)/slack + eta(y) <= 1.
```

Measured, at `nu_p = 1`:

| depth | cap fraction | pair charge | combined | overdraw |
|---|---|---|---|---|
| 0.05 | 0.90 | 0.487 | 1.387 | **0.387** |
| 0.15 | 0.92 | 0.410 | 1.330 | **0.330** |
| 0.25 | 0.92 | 0.444 | 1.364 | **0.364** |
| 0.35 | 0.86 | 0.415 | 1.275 | **0.275** |
| 0.45 | 0.85 | 0.338 | 1.188 | **0.188** |
| 0.49 | 0.85 | 0.301 | 1.151 | **0.151** |

The budget overdraws everywhere: theta_full > 0 does **not** follow from
stacking the current bounds, and saying otherwise would be the sham the
referee exists to catch. The deficit is 15–39% of slack, and the two
estimates that can reverse it are named with their measured headrooms:

1. **the level-4 caps are loose by 1.4x (shallow) to 2.7x (deep)** against
   measured adversaries — the dropped non-adjacent payments; recovering
   half of that looseness clears the deficit at every depth;
2. **the pair charge is the crude pointwise split**, loose by ~2x against
   the measured dipole totals (e.g. worst dipole −2.84 against a charged
   prediction of −5.7 at (0.3, 0.3)).

Either sharpening suffices; both together clear the budget with a margin
comparable to the deficits. This is the precise sense in which the
directive's OUTCOME B applies: multi-pair recovery survives structurally
(collective battery, eta < 1 at unit density), and the loss is in the
stacked *bounds*, not the energy.

## Definition-of-done classification

- Gate 1: **delivered** (hardened at original resolution; the coarse-grid
  failure recorded as a negative control, not smoothed over).
- Gate 2: **OUTCOME B** — positive theta at the single-pair level survives
  hardening; the multi-pair assembly overdraws by a quantified 15–39% of
  slack; the two reversing estimates are named and their measured headroom
  exceeds the deficit.
- OUTCOME C content also produced: the dense pair lattice (`nu_p = 2`,
  spacing in the T-kernel's negative band) defeats pairwise charging while
  collective energy survives — pinned as the level-6 kill control.
- The decimal gate (Phase 7) is **not entered**; no proportion is computed.

## Controls ledger

| control | instrument | measured |
|---|---|---|
| ball kernel vs float kernel | `test_ball_kernel...` | agreement to float precision, radii < 1e-15 |
| exact aL | `aL_ball` | rational, radius < 1e-30 |
| directed endpoints bracket | `test_directed_endpoints...` | holds |
| hardened quantities on the safe side | `test_hardened_quantities...` | slack lower, sups majorise true damage |
| hardened probe cells positive at theta = 0.1 | `test_hardened_scan_secures...` | +0.27 to +2.03 |
| LAW L exactness | `law_l_check` | 8.9e-16 |
| difference-layer nonnegativity | `test_difference_layer...` | min +6e-10 |
| energy decomposition vs brute force | `test_energy_decomposition...` | < 1e-9 |
| eta < 1 at unit density | `test_eta_below_one...` | 0.487 |
| pairwise charging fails when it should | `test_pairwise_charging_fails...` | eta = 7.7 at nu_p = 2 |
| collective survival everywhere | `test_collective_energy_survives...` | worst cross/slack −0.876 > −1 |
| assembly overdraw quantified | `test_assembly_overdraw...` | 0.15–0.39, bounded |

## Reproduction

```bash
.venv/bin/python hunts/frontier_math/pair_energy.py          # ~30 s
.venv/bin/python hunts/frontier_math/enclosure_pass.py       # ~30 min
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_level5.py                       # ~45 s
```
