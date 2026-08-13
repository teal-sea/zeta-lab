# k >= 2: what the budget's superadditivity does and does not buy

**Date:** 2026-08-13. **Reads:** `gram_form.py` (the three-term form),
`kpair_identity.py` (the identity and the joint search), `PROOF-LEDGER.md`
defect #20.

## 0. The state, corrected

`PROOF-LEDGER.md` carries an entry reading "`k >= 2`: OPEN on the BUDGET side
... short by a factor 1.99". **That entry is superseded a few lines below it**
by defect #20, and a reader who stops at the first entry will price this
problem wrongly. The 1.99 came from `multi_pair_requirement`, which charges
damage per pair against a joint budget floor; the identity shows the two sides
are maximised by *different configurations*, so the factor does not bound the
truth.

What the object itself measures (joint annealing over atoms, centres and
depths, `n <= 24`, 60 restarts):

| k | 1 | 2 | 3 | 4 | 6 |
|---|---|---|---|---|---|
| worst relative margin | +0.4915 | +0.3719 | +0.3908 | **+0.3430** | +0.3618 |

No downward trend in `k`. The statement looks true with about a third of
relative margin in hand, and the planted-fault ladder agrees with that number
independently (a worst margin of 0.343 predicts first violation at damage
inflation `1.522`; the ladder first goes negative at `1.5`).

**So `k >= 2` is missing a proof, not missing plausibility.**

## 1. The reduction that is already in hand

`gram_form.py` puts the slack in three terms,

    slack_k = B(T,y) + Cross(X,T,y) + R(X)/400,

with `B >= 0` provable in one line from `Retention.energy_F_ge` (already
kernel-checked) and `R >= 0` a sum of squares. So the whole question is

    (Q)   B(T,y) + R(X)/400  >=  sum_{a,p} D(y, x_a - t_p).

## 2. The budget is exactly superadditive, and by how much

Writing `|That(w)|^2 = k + sum_{p != q} cos(tau_pq w)` and integrating term by
term against `c2(w) cosh^2(y w) dw` gives an identity that is not written down
anywhere else in this hunt:

    B(T, y)  -  sum_p B({t_p}, y)  =  sum_{p != q} Psi(tau_pq, y),

    Psi(tau, y) = -(1/2) [ D(0, tau) + D(2y, tau) ].

Checked numerically over 200 random configurations (`k` in 2..6, `y` in
[0.05, 0.5], centres in [-40, 40]): worst residual **1.78e-15**. It is the
same cross-pair term the `kpair_identity` slack already carries, arrived at
from the budget side instead.

## 3. What that kills

The obvious route to `k >= 2` is to apply the closed `k = 1` inequality once
per pair and add. Doing so needs, exactly,

    (S)   sum_{p != q} Psi(tau_pq, y)  >=  (k - 1) * R(X)/400,

because each of the `k` copies consumes the whole repulsion `R`, and only one
`R` is available. **(S) is false in general, and the identity says why in one
line: its left side depends only on the centre gaps `tau`, its right side only
on the atoms `X`.** Spread the centres and `D(., tau) -> 0`, so the left side
goes to zero while `R(X)` is untouched and can be large.

The escape "use only a fraction `lambda` of `R` per pair" needs `lambda <= 1/k`,
i.e. a `k = 1` bound that is asymptotically repulsion-free — and
`PROOF-LEDGER.md` already records that the repulsion-free route is
"arithmetically dead, not merely lossy".

**So the per-pair decomposition is dead for a structural reason, not for want
of sharper constants.** That agrees with the ledger's verdict and now has a
one-line proof rather than a measurement behind it.

## 4. Where that leaves the search

Any proof of (Q) has to be genuinely joint in `X` and `T`. The two adversary
routes both pay, and a proof has to make that quantitative in one argument:

* **Spread the centres** so every pair sees atoms at a damage peak — but only
  two positions carry the top peak (`+/- 6.517`) and the rest decay like
  `1/s^2`, so `damage/gain` falls (measured `1.0420` at `k = 2`, `0.2483` at
  `k = 12`).
* **Stack the centres** to keep `damage/k` maximal — but coincident centres
  contribute `D(2y,0) + D(0,0)`, which enters with a minus sign and is a
  *gain* of `1.7556` per ordered pair.

The quantity that interpolates them is the centre packing: tight packing makes
`Psi` large, loose packing limits how many pairs one atom can damage at once
(`counting_bound.py`'s "at most one pair per damage window" is the combinatorial
half of this). A proof of (Q) most plausibly comes from bounding
`sum_{a,p} D(y, x_a - t_p)` by an incidence count controlled by the minimum
centre gap, and playing that against `Psi` summed over the same gaps.

**This is a direction, not a schedule.** Nothing above is a proof of `k >= 2`,
and none of it moves the constant. Nothing here is evidence about RH.

## 5. The anatomy of the binding configurations

Decomposing `slack_k` into its four terms at the worst configuration found for
each `k` (fixed-`n` annealer, 20 000 iterations):

| k | gain | damage | repulsion | cross | slack | rel | max incidences |
|---|---|---|---|---|---|---|---|
| 2 | 0.0675 | 0.0358 | 0.0150 | **-0.0184** | 0.0284 | 0.420 | 2 |
| 4 | 0.0675 | 0.0189 | 0.0064 | **-0.0289** | 0.0261 | 0.387 | 3 |
| 8 | 0.1688 | 0.0591 | 0.0106 | **-0.0517** | 0.0686 | 0.407 | 5 |
| 12 | 0.2777 | 0.1421 | 0.0551 | **-0.1018** | 0.0889 | 0.320 | 10 |

Three things this says, none of them obvious from the identity:

1. **The cross term is a cost, not a gain, at every binding configuration**,
   and by `k = 12` it is comparable to the damage (`-0.102` against `0.142`).
   The `+1.7556`-per-ordered-pair *gain* from coincident centres is real but
   the adversary does not take it — stacking buys relief it does not want.
2. **Incidence is not limited.** One atom sits inside the damage window of
   10 of the 12 pairs at `k = 12`. Whatever "at most one pair per damage
   window" bounds, it is not this, so the damage side scales with `k`
   essentially in full.
3. **Everything scales linearly in `k`.** `cross/k` runs `0.0092, 0.0072,
   0.0065, 0.0085`; gain and damage likewise. That is *why* the relative
   margin stabilises instead of collapsing, and it means an argument has to
   be linear in `k` too — anything that loses a factor of `k` cannot work.

## 6. Repulsion cannot be dropped (confirming the ledger independently)

The table above shows repulsion contributing under 20% of the gain at the
binding configurations, which invites the thought that it could be discarded
and the shared-repulsion difficulty with it. **It cannot.** Minimising the
relative margin with the repulsion term deleted:

| k | 1 | 2 | 4 | 8 | 12 |
|---|---|---|---|---|---|
| margin without repulsion | **-0.2990** | -0.1343 | -0.0668 | -0.1810 | +0.0247 |

Negative already at `k = 1`, decisively. (The `k = 12` positive is search
weakness on a harder landscape, not a reversal.) The small repulsion values in
§5 are an artefact of reading them off configurations chosen to bind the
*full* slack; an adversary allowed to ignore repulsion immediately picks
different ones.

So `PROOF-LEDGER.md`'s "the route that drops the repulsion term is
arithmetically dead" holds, reached here from a different direction. Repulsion
is load-bearing, it is paid once however large `k` is, and any proof must
carry that asymmetry rather than route around it.

## 7. The extremal configuration lives on a `2*pi` lattice

The saved `k = 12` witness (`k_trend.WITNESS_K12`) has centre gaps

    37.553  131.918  44.043  12.632  6.225  6.236  12.803  6.235  6.238
    12.904  18.789

and dividing by `2*pi` gives `5.977, 20.995, 7.010, 2.010, 0.991, 0.992,
2.038, 0.992, 0.993, 2.054, 2.990` — every one within 2..5% of an integer.
The atoms show the same thing, in clusters of near-coincident points separated
by multiples of the same step.

That is not decoration. The nine damage windows sit at `6.5167, 12.6988,
18.9400, ...`, whose successive gaps run `6.182, 6.241, 6.260, 6.270, 6.274,
6.277, 6.279, 6.279` — converging to `2*pi`. The adversary needs its atoms
inside the damage windows of as many pairs at once as possible, and the window
spacing *is* the lattice step.

**The restriction is essentially free.** Minimising with centres and atoms
confined to `c0 + 2*pi*Z` and `x0 + 2*pi*Z` (two real offsets, integer sites,
depths free):

| k | 2 | 4 | 8 | 12 | 16 |
|---|---|---|---|---|---|
| lattice-restricted | +0.4510 | +0.3473 | **+0.2796** | +0.2500 | +0.2434 |
| free, best known | ~0.372 | ~0.343 | ~0.284 | ~0.2305 | ~0.2365 |

At `k = 8` the restricted search finds a *worse* configuration than the free
one, and by `k = 16` the two agree to `0.007`. Restricting costs nothing and
searches better, because the space is smaller.

**This is a genuine reduction**: the continuum of centre and atom positions
collapses to integers plus two offsets. It is not yet a finite problem, since
`k` and the occupancy pattern remain.

## 8. But the occupancy is not periodic, so there is no small cell

The obvious next hope — if the sites are a lattice, take the occupancy periodic
and let `k -> infinity` on one cell — **fails**. Occupying every `p`-th site
with centres and every `q`-th with atoms, at depth `1/2`, offsets optimised on
a `24 x 24` grid:

| p, q | 1,1 | 1,2 | 2,2 | 3,3 | best |
|---|---|---|---|---|---|
| margin at `k = 32` | +24.45 | +12.66 | **+0.694** | +0.911 | **+0.694** |

Every uniform periodic pattern is *benign* — the best is `+0.694` against a
binding `~0.24`, a factor of three of slack. The margins do converge in `k`
(`p=q=2` runs `0.8100, 0.7514, 0.7154, 0.6940`), so the limits exist; they are
simply not where the adversary lives.

What the binding configurations use is the lattice **with irregular occupancy
and mixed depths** — at `k = 12`, ten of twelve depths on an endpoint and a
gap pattern `1,1,2,1,1,2,3,...` rather than a constant stride. So the
`k -> infinity` problem does not reduce to a small periodic cell, and the
combinatorics of *which* sites are occupied is carrying the difficulty.
