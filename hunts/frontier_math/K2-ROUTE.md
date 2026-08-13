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
