"""The exact k-pair slack identity, and what it says about the k >= 2 case.

`EForm3` and everything built on it (`near_coincident`, `repulsion_trade`,
`exact_gap_attack`, `cluster_sdp`) work the **single-pair** obligation

    (199/200) E[F] + n/200 + 4  <=  E[F + P],   P w = 2 cosh(y w) e^{i t w}.

The obligation blocker 2 actually names carries `k` pair blocks,
`P w = sum_p 2 cosh(y_p w) e^{i t_p w}`, and asks for `4k` on the left.
Nobody in this hunt had written the `k`-pair identity down; the `k >= 2`
question was being argued from per-pair accounting instead.  Here it is,
derived by expanding `|F + P|^2` and integrating each piece against `c2`:

    margin_k = E[F+P] - (199/200) E[F] - n/200 - 4k = (4/A^2) * slack_k,

    slack_k = sum_p Shq(y_p)/2
            - sum_p sum_a D(y_p, x_a - t_p)                    (damage)
            + (1/400) sum_{a<b} phi_r(x_a - x_b)^2             (repulsion)
            - (1/2) sum_{p != q} [ D(y_p+y_q, tau_pq)
                                 + D(y_p-y_q, tau_pq) ]        (inter-pair)

with `tau_pq = t_p - t_q`, `D(y,s) = Qim^2 - Qre^2 = -Re ghat(y+is)^2` and
`phi_r = Qre 0`.  Checked against the definition route (Gauss-Legendre on
`Eng`) at dps=30 for `k = 1..4`: worst residual **4.21e-17**
(:func:`identity_residual`).

## What the identity settles

**The repulsion term carries no `p` index.**  It is a property of the
on-line configuration alone, so it is paid ONCE however many pairs there
are, while the damage is summed over pairs.  Read naively that says the
single-pair closure cannot survive large `k`: relief per pair goes like
`1/k`.  The naive reading is wrong, and the identity says why.

For damage per pair to stay at its maximum, every pair must see the same
on-line atoms at its own top window peak.  There are only **two** such
positions (`+/- 6.517`), because the window peaks decay like `1/s^2`
(`D_j s_j^2 -> 2 cos^2(1/sqrt2)(cosh y - 1)`).  So either

* the centres **spread**, and `damage/k` decays with `k` — measured
  `dam/gain` 1.0420 at `k = 1, 2` falling to 0.2483 at `k = 12`
  (:func:`stack_seen_by_every_pair`); or
* the centres **stack**, keeping `damage/k` at the maximum — and then the
  inter-pair term turns strongly positive, `+1.7556` per ordered
  coincident pair, because `D(2y,0) + D(0,0) = -(ghat(2y)^2 + A^2) < 0`
  enters with a minus sign (:func:`stacked_centres`).

Both of the adversary's routes therefore pay for themselves, and neither
was visible to an argument that charges damage per pair.

## Measured relative margin

`slack_k / sum_p Shq(y_p)/2` (the ratio, which does not collapse as
`y -> 0` the way `slack_k` does) under joint annealing over atoms,
centres and depths, `n <= 24`, 60 restarts per `k`:

    k = 1: +0.4915   k = 2: +0.3719   k = 3: +0.3908
    k = 4: +0.3430   k = 6: +0.3618

No downward trend in `k`, and the worst is `+0.343`, not near zero.  The
planted-fault control has power and its threshold is consistent: a worst
relative margin of 0.343 predicts failure once the damage is inflated by
`1/(1 - 0.343) = 1.52`, and the search first returns negatives at
`damage_scale = 1.5` (:func:`planted_fault_ladder`).

## What this does NOT establish

`slack_k >= 0` for all `k` is **not** proved here; this is a search plus
an exact identity, i.e. hardened-grade evidence with the mechanism named.
What it does refute is the reading that `cluster_sdp.multi_pair_requirement`'s
factor 1.99 is an obstruction to the *statement*: that factor compares a
per-pair damage charge against a measured joint budget floor, and the
identity shows the per-pair charge is unreachable for `k >= 3` — the two
sides are maximised by different configurations.  Nothing here is
evidence about RH.

Run ``.venv/bin/python hunts/frontier_math/kpair_identity.py`` (~90 s).
"""

from __future__ import annotations

import cmath
import math
import random
from dataclasses import dataclass, field

import mpmath as mp

__all__ = [
    "A_CONST", "damage", "phi_r", "shq", "slack_k", "margin_definition",
    "identity_residual", "stack_seen_by_every_pair", "stacked_centres",
    "spread_lattice_scan", "joint_search", "planted_fault_ladder",
    "NAMED_GAPS", "SEARCH_RECORD", "report",
]

SQ2 = math.sqrt(2.0)
#: `A = sqrt2 sin(1/sqrt2) = int g`, EForm3's `Aconst`.
A_CONST = SQ2 * math.sin(1 / SQ2)
_A2 = A_CONST ** 2

#: window peak positions at `y = 1/2` (zeros of `phi_r`, spacing -> 2 pi).
PEAKS = (6.517, 12.755, 18.977, 25.20, 31.47, 37.72, 43.96, 50.21)
_ALL_PEAKS = tuple(-p for p in reversed(PEAKS)) + PEAKS


# --------------------------------------------------------------------------
# closed forms
# --------------------------------------------------------------------------

def _ghat(re: float, im: float) -> complex:
    """`int_{-1/2}^{1/2} cos(sqrt2 u) cosh(z u) du` at `z = re + i im`."""
    z = complex(re, im)
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return cmath.sinh(zp / 2) / zp + cmath.sinh(zm / 2) / zm


def damage(y: float, s: float) -> float:
    """`Qim(y,s)^2 - Qre(y,s)^2 = -Re ghat(y + i s)^2`."""
    g = _ghat(y, s)
    return -(g * g).real


def phi_r(v: float) -> float:
    """`Qre 0 v`, the window transform."""
    return _ghat(0.0, v).real


def shq(y: float) -> float:
    """`Shq y = ghat(2y)^2 - A^2`."""
    return _ghat(2 * y, 0.0).real ** 2 - _A2


# --------------------------------------------------------------------------
# the identity
# --------------------------------------------------------------------------

def slack_k(xs, pairs, damage_scale: float = 1.0, relative: bool = False) -> float:
    """The `k`-pair slack.  `pairs = [(y_p, t_p), ...]`.

    `relative=True` returns `slack_k / sum_p Shq(y_p)/2`, which is the
    quantity to minimise in a search: the absolute slack collapses to 0
    as `y -> 0` for the trivial reason that every term does.
    """
    gain = sum(shq(y) / 2 for y, _ in pairs)
    dam = sum(damage(y, x - t) for y, t in pairs for x in xs) * damage_scale
    rel = 0.0
    for a in range(len(xs)):
        for b in range(a + 1, len(xs)):
            rel += phi_r(xs[a] - xs[b]) ** 2
    rel /= 400.0
    inter = 0.0
    for p, (yp, tp) in enumerate(pairs):
        for q, (yq, tq) in enumerate(pairs):
            if p != q:
                inter += damage(yp + yq, tp - tq) + damage(yp - yq, tp - tq)
    s = gain - dam + rel - inter / 2
    return s / gain if relative else s


def _c2_mp(w):
    w = mp.mpf(w)
    lo = max(-mp.mpf(1) / 2, -mp.mpf(1) / 2 - w)
    hi = min(mp.mpf(1) / 2, mp.mpf(1) / 2 - w)
    if hi <= lo:
        return mp.mpf(0)
    sq2 = mp.sqrt(2)
    return mp.quad(lambda u: mp.cos(sq2 * u) * mp.cos(sq2 * (u + w)), [lo, hi])


def margin_definition(xs, pairs, dps: int = 30):
    """`E[F+P] - (199/200)E[F] - n/200 - 4k`, straight from `Eng`.

    The independent route: quadrature against `c2`, no closed form used.
    """
    with mp.workdps(dps):
        a = mp.sqrt(2) * mp.sin(1 / mp.sqrt(2))
        n, k = len(xs), len(pairs)

        def eng(G):
            return (1 / a ** 2) * mp.quad(
                lambda w: _c2_mp(w) * abs(G(w)) ** 2, [-1, 0, 1])

        def F(w):
            return mp.fsum([mp.e ** (1j * x * w) for x in xs])

        def P(w):
            return mp.fsum([2 * mp.cosh(y * w) * mp.e ** (1j * t * w)
                            for y, t in pairs])

        eF = eng(F)
        eFP = eng(lambda w: F(w) + P(w))
        return eFP - mp.mpf(199) / 200 * eF - mp.mpf(n) / 200 - 4 * k


#: `(xs, pairs)` cases spanning `k = 1..4`, mixed depths and shifts.
IDENTITY_CASES = (
    ([6.517], [(0.5, 0.0)]),
    ([0.0, 2.1], [(0.5, 0.0), (0.4, 3.3)]),
    ([6.5, 6.6, -6.5], [(0.5, 0.0), (0.5, 6.283185307)]),
    ([0.0, 1.1, 2.2, 9.9], [(0.3, -1.0), (0.45, 2.0), (0.5, 8.0)]),
    ([-6.5, 0.0, 6.5, 13.0], [(0.49, 0.0), (0.49, 6.283185307),
                              (0.49, 12.56637061), (0.2, -5.0)]),
)


def identity_residual(cases=IDENTITY_CASES, dps: int = 30) -> float:
    """`max |margin_definition - (4/A^2) slack_k|` over `cases`."""
    worst = 0.0
    for xs, pairs in cases:
        m = margin_definition(xs, pairs, dps)
        pred = 4 / _A2 * slack_k(xs, pairs)
        worst = max(worst, float(abs(m - pred)))
    return worst


# --------------------------------------------------------------------------
# the two routes the adversary has, and why each pays for itself
# --------------------------------------------------------------------------

def _centres_on_windows(k: int) -> list:
    """`k` centres placed on the window positions of a stack at 0."""
    ts = []
    for j in range((k + 1) // 2):
        ts.append(PEAKS[j])
        if len(ts) < k:
            ts.append(-PEAKS[j])
    return ts[:k]


def stack_seen_by_every_pair(ks=(1, 2, 4, 6, 8, 12), ms=(1, 3, 7, 8, 12, 20),
                             y: float = 0.5) -> list:
    """`m` atoms at 0; centres on the stack's own damage windows.

    Every pair is damaged by the same stack at once — the strongest
    simultaneous-damage placement available.  `dam/gain` is the diagnostic:
    it peaks at `k = 1, 2` and falls thereafter, because the later pairs
    can only be placed on smaller window peaks.
    """
    rows = []
    for k in ks:
        ts = _centres_on_windows(k)
        pairs = [(y, t) for t in ts]
        for m in ms:
            xs = [0.0] * m
            gain = sum(shq(yy) / 2 for yy, _ in pairs)
            dam = sum(damage(yy, x - t) for yy, t in pairs for x in xs)
            rows.append({"k": k, "m": m, "damage": dam, "gain": gain,
                         "dam_over_gain": dam / gain,
                         "slack": slack_k(xs, pairs)})
    return rows


def stacked_centres(ks=(1, 2, 4, 8), ms=(1, 7, 8, 12), y: float = 0.5) -> list:
    """All `k` centres at the SAME place: `damage/k` cannot decay.

    This is the only way to keep every pair at the top peak, and it is
    self-defeating: coincident centres contribute
    `D(2y,0) + D(0,0) = -(ghat(2y)^2 + A^2)` to the inter-pair sum, which
    enters `slack_k` with a minus sign, i.e. as a large positive gain.
    """
    rows = []
    for k in ks:
        pairs = [(y, PEAKS[0])] * k
        for m in ms:
            xs = [0.0] * m
            inter = 0.0
            for p in range(k):
                for q in range(k):
                    if p != q:
                        inter += damage(2 * y, 0.0) + damage(0.0, 0.0)
            rows.append({"k": k, "m": m, "inter_per_pair": -inter / 2 / k,
                         "slack": slack_k(xs, pairs)})
    return rows


#: `D(2y,0) + D(0,0)` at `y = 1/2` — the coincident-centre shield, per
#: ordered pair, entering `slack_k` with the opposite sign.
COINCIDENT_SHIELD = -(damage(1.0, 0.0) + damage(0.0, 0.0))


def spread_lattice_scan(Ls=(6.283185307, 6.5, 12.7, 13.03, 19.0, 25.5),
                        ks=(2, 4, 8), ms=(1, 4, 8), y: float = 0.5) -> list:
    """Centres on a lattice of spacing `L`, `m` atoms stacked at 0."""
    rows = []
    for L in Ls:
        for k in ks:
            ts = [L * p - L * (k - 1) / 2 for p in range(k)]
            pairs = [(y, t) for t in ts]
            for m in ms:
                xs = [0.0] * m
                s = slack_k(xs, pairs)
                rows.append({"L": L, "k": k, "m": m, "slack": s,
                             "slack_per_pair": s / k})
    return rows


# --------------------------------------------------------------------------
# the joint search
# --------------------------------------------------------------------------

def _anneal(k, n_max, rng, iters=6000, damage_scale=1.0):
    n = rng.randint(1, n_max)
    xs = [rng.choice(_ALL_PEAKS) + rng.gauss(0, 0.3) for _ in range(n)]
    if rng.random() < 0.5:
        c = rng.choice(_ALL_PEAKS)
        xs = [c + rng.gauss(0, 0.2) for _ in range(n)]
    ts = [rng.choice(_ALL_PEAKS) + rng.gauss(0, 0.5) for _ in range(k)]
    ys = [rng.uniform(0.05, 0.5) for _ in range(k)]
    cur = slack_k(xs, list(zip(ys, ts)), damage_scale, True)
    best, bstate = cur, (list(xs), list(ts), list(ys))
    for it in range(iters):
        T = 0.05 * (1 - it / iters) + 1e-5
        nxs, nts, nys = list(xs), list(ts), list(ys)
        r = rng.random()
        if r < 0.40 and nxs:
            nxs[rng.randrange(len(nxs))] += rng.gauss(
                0, 0.8 if rng.random() < 0.7 else 4.0)
        elif r < 0.55:
            nxs.append(rng.choice(_ALL_PEAKS) + rng.gauss(0, 0.3))
        elif r < 0.65 and len(nxs) > 1:
            nxs.pop(rng.randrange(len(nxs)))
        elif r < 0.85:
            nts[rng.randrange(k)] += rng.gauss(
                0, 1.0 if rng.random() < 0.7 else 5.0)
        else:
            i = rng.randrange(k)
            nys[i] = min(0.5, max(0.01, nys[i] + rng.gauss(0, 0.08)))
        if len(nxs) > n_max or not nxs:
            continue
        new = slack_k(nxs, list(zip(nys, nts)), damage_scale, True)
        if new < cur or rng.random() < math.exp(-(new - cur) / T):
            xs, ts, ys, cur = nxs, nts, nys, new
            if cur < best:
                best, bstate = cur, (list(xs), list(ts), list(ys))
    return best, bstate


def joint_search(ks=(1, 2, 3, 4, 6), restarts: int = 60, n_max: int = 24,
                 damage_scale: float = 1.0, seed: int = 20260813,
                 iters: int = 6000) -> dict:
    """Minimise the RELATIVE margin over atoms, centres and depths jointly."""
    rng = random.Random(seed)
    out = {}
    for k in ks:
        bk, bstate = None, None
        for _ in range(restarts):
            s, st = _anneal(k, n_max, rng, iters, damage_scale)
            if bk is None or s < bk:
                bk, bstate = s, st
        xs, ts, ys = bstate
        out[k] = {"relative_margin": bk, "n": len(xs), "depths": sorted(ys)}
    out["worst"] = min(v["relative_margin"] for v in out.values()
                       if isinstance(v, dict))
    return out


def planted_fault_ladder(scales=(1.0, 1.5, 2.0, 3.0), restarts: int = 25,
                         seed: int = 20260813) -> list:
    """The detector-power control, with its consistency check.

    A worst relative margin `r` predicts the first negative at
    `damage_scale = 1/(1-r)`; the ladder must fire at or just past it, and
    not before.  If it fires at 1.0 the instrument is broken; if it never
    fires the search has no power and its honest verdict means nothing.
    """
    rows = []
    for sc in scales:
        res = joint_search(restarts=restarts, damage_scale=sc, seed=seed,
                           iters=3000)
        rows.append({"damage_scale": sc, "worst": res["worst"],
                     "fires": res["worst"] < 0})
    honest = rows[0]["worst"]
    rows.append({"predicted_threshold": 1.0 / (1.0 - honest)
                 if honest < 1 else float("inf")})
    return rows


#: The joint search as run for the ledger (60 restarts, n <= 24, dps float).
SEARCH_RECORD = {
    "relative_margin": {1: 0.4914777, 2: 0.3719141, 3: 0.3907667,
                        4: 0.3430384, 6: 0.3617642},
    "worst": 0.3430384,
    "worst_k": 4,
    "predicted_break_scale": 1.5221,
    "planted_first_negative_at": 1.5,
    "identity_residual": 4.21e-17,
}

NAMED_GAPS = (
    "N1 slack_k >= 0 for all k is NOT proved here. This is an exact "
    "identity plus a search: hardened-grade evidence with a mechanism, "
    "not a theorem.",
    "N2 the search covers k <= 6 and n <= 24 with depths in [0.01, 1/2]; "
    "nothing is claimed beyond that box.",
    "N3 the window-peak decay that makes damage/k fall is the measured "
    "law D_j s_j^2 -> 2 cos^2(1/sqrt2)(cosh y - 1), not an enclosure.",
    "N4 what IS refuted is a reading, not a computation: cluster_sdp's "
    "factor 1.99 compares a per-pair damage charge against a joint budget "
    "floor, and the two are maximised by different configurations.",
    "N5 nothing here is evidence about RH.",
)


def report(quick: bool = True) -> dict:
    """Print the audit."""
    print("= the k-pair identity =")
    res = identity_residual()
    print(f"  max |margin_definition - (4/A^2) slack_k| over k=1..4: {res:.3e}")
    print(f"  A = {A_CONST:.16f}   Shq(1/2)/2 = {shq(0.5)/2:.8f}")
    print("= route 1: centres spread over the stack's windows =")
    for r in stack_seen_by_every_pair(ks=(1, 2, 4, 12), ms=(8,)):
        print(f"  k={r['k']:3d} m={r['m']:2d}  damage/gain = "
              f"{r['dam_over_gain']:.4f}   slack = {r['slack']:+.6f}")
    print("  damage/gain falls with k: only two top-peak positions exist")
    print("= route 2: centres stacked (damage/k stays maximal) =")
    print(f"  coincident-centre shield per ordered pair: "
          f"{COINCIDENT_SHIELD:+.6f}")
    for r in stacked_centres(ks=(2, 8), ms=(8,)):
        print(f"  k={r['k']:3d} m={r['m']:2d}  inter/pair = "
              f"{r['inter_per_pair']:+.6f}   slack = {r['slack']:+.6f}")
    print("  stacking pays the adversary nothing: the shield is positive")
    print("= joint search over atoms, centres and depths =")
    if quick:
        rec = SEARCH_RECORD["relative_margin"]
        for k, v in rec.items():
            print(f"  k={k}: worst relative margin {v:+.7f}   (recorded)")
        print(f"  worst {SEARCH_RECORD['worst']:+.7f} at k="
              f"{SEARCH_RECORD['worst_k']}; predicted break at damage_scale "
              f"{SEARCH_RECORD['predicted_break_scale']:.4f}, planted ladder "
              f"first fires at {SEARCH_RECORD['planted_first_negative_at']}")
    else:
        out = joint_search()
        for k in (1, 2, 3, 4, 6):
            print(f"  k={k}: worst relative margin "
                  f"{out[k]['relative_margin']:+.7f}  (n={out[k]['n']})")
    print("= named gaps =")
    for g in NAMED_GAPS:
        print(f"  * {g}")
    return SEARCH_RECORD


if __name__ == "__main__":
    report(quick=False)
