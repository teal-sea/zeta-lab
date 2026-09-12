"""The two-species restatement of blocker 2, and the depth-extended landscape.

`K2-ROUTE.md` section 2 derives the budget superadditivity
`Psi(tau,y) = -(1/2)[D(0,tau) + D(2y,tau)]` and section 4 asks for a proof
of (Q) that is "genuinely joint in X and T".  This module starts from one
line that was sitting in plain sight:

    D(0, tau) = -Qre(0, tau)^2 = -Kpair(tau)        (Qim vanishes at depth 0)

so `Psi(tau,y) = (1/2)Kpair(tau) - (1/2)D(2y,tau)`, and the whole k-pair
slack rearranges into a TWO-SPECIES system in which the centres are atoms
of a second kind:

    4*slack_k =   2k*Shq(y)                                (per-centre budget)
                + 2*sum_{p!=q} Kpair(tau_pq)               (centre-centre repulsion, rate 2)
                + (1/200)*sum_{a!=b} Kpair(x_ab)           (atom-atom repulsion, rate 1/200)
                - 4*sum_{a,p} D(y, x_a - t_p)              (atom-centre damage, depth y)
                - 2*sum_{p!=q} D(2y, tau_pq)               (centre-centre damage, depth 2y)

checked against `gram_form.slack_direct` at 1.8e-14 over 400 random
instances (:func:`identity_residual`), and in the general-depth form (pair
`p` at depth `y_p`; kernels `K_{y_p+y_q} + K_{|y_p-y_q|}`) against
`kpair_identity.slack_k` at 3.6e-15 (:func:`identity_residual_general`).

Two consequences, both structural:

1. **Centres repel each other through the SAME `Kpair` kernel the atoms
   use, at 400x the atoms' rate, and suffer the SAME window damage at
   doubled depth.**  The k=1 proof's three pillars (window confinement,
   `Kpair` floors, the integer trade) therefore have exact analogues for
   the centre species, and the `k = 2` case closes this way
   (`k2_closure.py`, `K2-TWO-SPECIES.md`).

2. **The k-large binding regime is the centre gas damaging itself.**  On
   the worst uniform lattice (spacing `6.285`, i.e. `2*pi` to 0.03%) the
   centre self-energy eats 87.8% of the per-centre budget as k -> inf
   (:func:`centre_gas_row`), while the same lattice poisons atom farming:
   every window position of one centre sits in the near-zone of the next,
   where the SIGNED atom field is `~ -0.85` (:func:`signed_field`).  The
   few-atom/many-pair adversary of `shared_repulsion.py` (worst at n=5,
   k=23) is this mechanism, not a failure of atom counting.

## The depth-extended landscape (centre-centre damage lives at depth <= 1)

Measured here because the k=1 table stops at depth 1/2
(:func:`depth1_windows`, :func:`no_damage_radius`, :func:`far_constant`):

* the no-damage radius SHRINKS with depth: first damage at `s = 6.0653`
  at depth 1/2 (the k=1 table's `I_0` left edge) but `s = 5.3984` at
  depth 1.  `no_damage`'s `28/5` does NOT hold at depth 1.
* depth-1 windows are ~1.75-1.89 wide (vs 0.96), NEST the depth-1/2
  windows, and the profile `Dam/y'^2` grows mildly with depth
  (`1.759e-2 -> 2.073e-2` at window 0).
* the far-field constant `sup Dam(y',s)(s^2-2)/y'^2` is `0.6636` at
  depth 1 on `[8,400]`, the proved `637/1000` of `Wt_tail_le` (stated
  for depth <= 1/2) is EXCEEDED at depth 1 and cannot be borrowed as-is.

Nothing here is proved; every number is a scan-grade measurement in double
precision.  Nothing here is evidence about RH.
"""

from __future__ import annotations

import math
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import gram_form as gf  # noqa: E402

__all__ = [
    "kpair", "dam", "signed_field", "four_slack_two_species",
    "four_slack_general", "identity_residual", "identity_residual_general",
    "d_zero_is_minus_kpair", "no_damage_radius", "depth1_windows",
    "far_constant", "centre_gas_row", "centre_gas_row_closed",
    "LANDSCAPE_RECORD", "NAMED_GAPS", "report",
]


def kpair(u: float) -> float:
    """`Kpair(u) = Qre(0,u)^2 = phi_r(u)^2`, the shared repulsion kernel."""
    return gf.phi_r(u) ** 2


def dam(y: float, s: float) -> float:
    """`Dam(y,s) = max(0, D(y,s))`."""
    return max(0.0, gf.damage(y, s))


def signed_field(xs, ts, y: float):
    """Per-atom SIGNED total field `sum_p D(y, x - t_p)` at each x in xs.

    An atom contributes `4 * field(x)` to the deficit; where the field is
    negative the atom is a net loss to the adversary.  This is what makes
    tight centre lattices barren for atoms.
    """
    return [sum(gf.damage(y, x - t) for t in ts) for x in xs]


def four_slack_two_species(xs, ts, y: float) -> float:
    """`4*slack_k` in the equal-depth two-species form."""
    k, n = len(ts), len(xs)
    bud = 2 * k * gf.shq(y)
    rep_t = 2 * sum(kpair(tp - tq) for i, tp in enumerate(ts)
                    for j, tq in enumerate(ts) if i != j)
    rep_x = (1 / 200) * sum(kpair(xs[a] - xs[b]) for a in range(n)
                            for b in range(n) if a != b)
    dam_xt = 4 * sum(gf.damage(y, x - t) for x in xs for t in ts)
    dam_tt = 2 * sum(gf.damage(2 * y, tp - tq) for i, tp in enumerate(ts)
                     for j, tq in enumerate(ts) if i != j)
    return bud + rep_t + rep_x - dam_xt - dam_tt


def four_slack_general(xs, ts, ys) -> float:
    """General depths: pair `p` at depth `y_p`; kernels split per pair."""
    n = len(xs)
    bud = 2 * sum(gf.shq(yp) for yp in ys)
    rep_t = 0.0
    for i, (tp, yp) in enumerate(zip(ts, ys)):
        for j, (tq, yq) in enumerate(zip(ts, ys)):
            if i != j:
                rep_t += -2 * (gf.damage(yp + yq, tp - tq)
                               + gf.damage(abs(yp - yq), tp - tq))
    rep_x = (1 / 200) * sum(kpair(xs[a] - xs[b]) for a in range(n)
                            for b in range(n) if a != b)
    dam_xt = 4 * sum(gf.damage(yp, x - tp) for x in xs
                     for tp, yp in zip(ts, ys))
    return bud + rep_t + rep_x - dam_xt


def identity_residual(trials: int = 200, seed: int = 20260815) -> float:
    """Worst |4*slack_direct - two_species| over random instances."""
    rng = random.Random(seed)
    worst = 0.0
    for _ in range(trials):
        n, k = rng.randint(1, 8), rng.randint(1, 6)
        xs = [rng.uniform(-40, 40) for _ in range(n)]
        ts = [rng.uniform(-40, 40) for _ in range(k)]
        y = rng.uniform(0.01, 0.5)
        worst = max(worst, abs(4 * gf.slack_direct(xs, ts, y)
                               - four_slack_two_species(xs, ts, y)))
    return worst


def identity_residual_general(trials: int = 100, seed: int = 7) -> float:
    """Worst |4*kpair_identity.slack_k - general two-species| (mixed depths)."""
    import kpair_identity as ki
    rng = random.Random(seed)
    worst = 0.0
    for _ in range(trials):
        n, k = rng.randint(1, 6), rng.randint(2, 5)
        xs = [rng.uniform(-30, 30) for _ in range(n)]
        ts = [rng.uniform(-30, 30) for _ in range(k)]
        ys = [rng.uniform(0.01, 0.5) for _ in range(k)]
        v1 = 4 * ki.slack_k(xs, list(zip(ys, ts)))
        worst = max(worst, abs(v1 - four_slack_general(xs, ts, ys)))
    return worst


def d_zero_is_minus_kpair(us=(0.0, 0.3, 1.7, 6.517, 12.4, 33.3, 59.9)) -> float:
    """`D(0,u) + Kpair(u) = 0` exactly: Qim vanishes at depth 0."""
    return max(abs(gf.damage(0.0, u) + kpair(u)) for u in us)


# -- the depth-extended landscape ------------------------------------------

def no_damage_radius(y: float, s_hi: float = 12.0, step: float = 1e-4) -> float:
    """First `s > 0` with `Dam(y,s) > 0` (bisected to 1e-10)."""
    s = step
    while s <= s_hi:
        if gf.damage(y, s) > 0:
            lo, hi = s - step, s
            for _ in range(60):
                mid = (lo + hi) / 2
                if gf.damage(y, mid) > 0:
                    hi = mid
                else:
                    lo = mid
            return hi
        s += step
    return float("inf")


def depth1_windows(y: float = 1.0, s_lo: float = 4.0, s_hi: float = 62.0,
                   step: float = 2e-4):
    """`(left, right, peak_s, peak/y^2)` per damage window of `Dam(y, .)`."""
    out, s, prev, left = [], s_lo, gf.damage(y, s_lo) > 0, None
    if prev:
        left = s_lo
    while s <= s_hi:
        pos = gf.damage(y, s) > 0
        if pos and not prev:
            lo, hi = s - step, s
            for _ in range(50):
                mid = (lo + hi) / 2
                if gf.damage(y, mid) > 0:
                    hi = mid
                else:
                    lo = mid
            left = hi
        if prev and not pos:
            lo, hi = s - step, s
            for _ in range(50):
                mid = (lo + hi) / 2
                if gf.damage(y, mid) > 0:
                    lo = mid
                else:
                    hi = mid
            out.append((left, lo))
        prev = pos
        s += step
    if prev:
        out.append((left, s_hi))
    rows = []
    for (l, r) in out:
        a, b = l, r
        grr = (math.sqrt(5) - 1) / 2
        c, d = b - grr * (b - a), a + grr * (b - a)
        for _ in range(80):
            if gf.damage(y, c) < gf.damage(y, d):
                a, c = c, d
                d = a + grr * (b - a)
            else:
                b, d = d, c
                c = b - grr * (b - a)
        pk = (a + b) / 2
        rows.append((l, r, pk, gf.damage(y, pk) / y ** 2))
    return rows


def far_constant(y: float, lo: float = 8.0, hi: float = 400.0,
                 step: float = 5e-3) -> float:
    """`sup Dam(y,s)*(s^2-2)/y^2` on [lo, hi], the Wt-style constant."""
    sup, s = 0.0, lo
    while s <= hi:
        sup = max(sup, dam(y, s) * (s * s - 2) / y ** 2)
        s += step
    return sup


def centre_gas_row(lam: float, y: float = 0.5, dmax: int = 200) -> float:
    """Per-centre self-energy of the uniform centre lattice, k -> inf.

    `sum_{d>=1} [4*Dam(2y, d*lam) - 4*Kpair(d*lam)]`, in the x4
    normalisation, against the per-centre budget `2*Shq(y)`.

    **The distance index runs over d >= 1 once, not over both signs**, and
    that is correct: the two-species form sums over ORDERED pairs, and the
    factor 4 already carries it. Verified against the form itself rather
    than argued, the net centre-centre cost per centre computed directly
    from `four_slack_two_species` on a `2*pi` lattice converges to this
    value from below (0.099826 at k=21, 0.107251 at k=51, 0.110325 at
    k=101, against 0.114013 here).

    An earlier version of this docstring said "(both neighbours)". It was a
    misleading gloss on correct arithmetic, and it cost a wrong entry in
    NAMED_GAPS G4, see that entry.
    """
    return sum(4 * dam(2 * y, d * lam) - 4 * kpair(d * lam)
               for d in range(1, dmax + 1))


def centre_gas_row_closed(y: float = 0.5) -> float:
    """The uniform-lattice centre-gas row at the critical `2*pi` spacing,
    in closed form.

    `centre_gas_row`'s summand is not a new object.  `Kpair(u) = Qre(0,u)^2
    = -D(0,u) = kernel(0,u)` (this is `d_zero_is_minus_kpair`), and
    `Dam(2y,s) = -kernel(2y,s)` wherever the rectification is inactive, so
    at `y = 1/2` the summand is

        4*Dam(1,s) - 4*Kpair(s) = -4*[kernel(0,s) + kernel(1,s)] = -4*kappa(s)

    with `kappa` exactly `counting_lemma.kappa`.  The two modules had been
    summing the same kernel without either saying so.

    `counting_lemma` already carries the Poisson collapse for that kernel:
    `c2` is supported on `[-1,1]` and vanishes at the endpoints, so summing
    at spacing exactly `2*pi` kills every alias and

        sum_{d in Z} kappa(2*pi*d) = 2*c2(0).

    Splitting off `d = 0` gives this row in closed form:

        row(2*pi) = -4*c2(0) + 2*kappa(0) = 0.11433003938654052...

    Two facts make the transfer legitimate rather than formal.  The
    rectification `max(0, .)` in `dam` never binds on this lattice (`D(1,
    2*pi*d) > 0` for every `d` checked to 200), so no clipping breaks the
    band-limitedness Poisson needs.  And `kappa(2*pi*d)` decays only like
    `1/d`, which is why the truncated `centre_gas_row` approaches this value
    from below as `O(1/dmax)` rather than reaching it.

    Scope, stated because it is the whole point: this is the UNIFORM lattice
    at the critical spacing, not the configuration extremum.  T1 in
    `K2-TWO-SPECIES.md` asks for a bound over all centre configurations and
    that remains an optimisation obligation.  What is no longer an
    optimisation obligation is the uniform-lattice value itself.
    """
    if y != 0.5:
        raise ValueError(
            "the closed form is derived at y = 1/2, where the summand is "
            "exactly -4*kappa; no other depth is claimed")
    import counting_lemma as cl
    return -4 * cl.C2_ZERO + 2 * cl.kappa(0.0)


LANDSCAPE_RECORD = {
    "no_damage_radius": {0.5: 6.065319, 0.75: 5.735725, 1.0: 5.398373},
    "depth1_window0": {"left": 5.39837, "right": 7.28492,
                       "peak": 6.2055, "cap_over_y2": 2.072721e-2},
    "profile_growth_window0": {0.1: 1.650680e-2, 0.5: 1.758570e-2,
                               1.0: 2.072721e-2},
    "far_constant": {0.5: 0.621997, 1.0: 0.663592, "proved_le_half": 0.637},
    "centre_gas": {"worst_uniform_lam": 6.285, "row": 0.114045,
                   "budget_floor_per_centre": 0.12986, "ratio": 0.878,
                   "row_is_truncated": "0.114045 and 0.878 are the dmax=200 "
                                       "readings. kappa(2*pi*d) decays like "
                                       "1/d, so they understate by 2.85e-4 "
                                       "and the understatement flatters the "
                                       "margin. Exact at 2*pi: row "
                                       "0.11433003938654052, ratio 0.88041 "
                                       "(centre_gas_row_closed).",
                   "convention": "d >= 1 once; the x4 factor carries the "
                                 "ordered-pair sum. Checked against "
                                 "four_slack_two_species, which converges "
                                 "to this row from below as k grows.",
                   "irregular_1121123_corrected": 0.0602},
    "kpair_resonant": {6.065: 6.621863e-3, 6.238: 3.088070e-3,
                       6.517: 2.733364e-4, 12.755: 3.2e-10},
}

NAMED_GAPS = (
    "G1 the two-species form is an IDENTITY (residuals 1.8e-14 / 3.6e-15); "
    "nothing about it is a bound.  The k=2 closure that uses it is in "
    "k2_closure.py and is measured grade, not proved.",
    "G2 every landscape number is a scan (double precision, grid + "
    "bisection), not an enclosure; the depth-1 analogues of no_damage, "
    "Qim_far_sq_abs and Wt_tail_le are NOT kernel-checked and the proved "
    "depth<=1/2 constants do not cover depth 1 (0.6636 > 0.637).",
    "G3 the per-point depth monotonicity of Dam(y,s)/y^2 on y in (0,1] "
    "carries a measured wobble (9.1e-6 near s=6.67 at depth 1; 9.9e-5 in "
    "the signed-growth profile at s=0): any table built on profile "
    "domination needs those pads.",
    "G4 WITHDRAWN 2026-08-18, and it was wrong in the operator's favour. "
    "It read: 'the centre-gas extremum over CONFIGURATIONS is not the "
    "uniform lattice: the 1,1,2,1,1,2,3 pattern at step 2*pi gives a "
    "per-row 0.1200 > 0.1140.' The 0.1200 reproduces exactly, but it was "
    "measured as a middle-centre row over an explicit chain summing "
    "BOTH sign directions, and compared against centre_gas_row, which "
    "sums d >= 1 once. A two-sided number against a one-sided one, off by "
    "exactly 2.0027. Halved to the correct convention the pattern gives "
    "~0.0602, far BELOW the uniform lattice's 0.114263, so it is not a "
    "counterexample to lattice extremality and never was. Run 37fb06a9 "
    "flagged the non-reproduction (its three readings all used 7 centres "
    "and so missed the long-chain reading that produces the number); the "
    "cause is recorded here. Lattice extremality now has no recorded "
    "counterexample. T1 remains an optimisation obligation rather than a "
    "formula, but for want of a proof, not for want of a counterexample.",
    "G5 k >= 3 remains open; nothing here is evidence about RH.",
)


def report() -> dict:
    print("= the two-species identity =")
    print(f"  equal-depth residual (400 rand):   {identity_residual():.3e}")
    print(f"  general-depth residual (100 rand): {identity_residual_general():.3e}")
    print(f"  D(0,u) + Kpair(u) worst:           {d_zero_is_minus_kpair():.3e}")
    print("= the depth-extended landscape =")
    for y in (0.5, 0.75, 1.0):
        print(f"  no-damage radius at depth {y}: {no_damage_radius(y):.6f}")
    print(f"  far constant depth 1/2: {far_constant(0.5):.6f}   depth 1: "
          f"{far_constant(1.0):.6f}   (proved for depth<=1/2: 0.637)")
    print("= the centre gas =")
    best = max(((centre_gas_row(l), l) for l in
                [5.4 + 0.005 * i for i in range(421)]), key=lambda t: t[0])
    print(f"  worst uniform lattice: lam={best[1]:.3f}  row={best[0]:+.6f}  "
          f"vs per-centre budget floor 0.12986")
    print("= named gaps =")
    for g in NAMED_GAPS:
        print(f"  * {g}")
    return LANDSCAPE_RECORD


if __name__ == "__main__":
    report()
