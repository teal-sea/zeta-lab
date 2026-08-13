"""The co-optimizing adversary: pairs AND on-line points chosen together.

WHY THIS INSTRUMENT EXISTS.  Every adversary in this hunt so far held one
side fixed: `mt_adversary.py` optimized on-line placements against a FIXED
pair set; the joint layer (`paper_joint.py`) swept pair FAMILIES (lattices,
dipoles, phases) and took the sup over on-line configurations for each.
The audit (`EXTERNAL-AUDIT-2026-08-12.md` §3) named the untested corner:
nothing ever let the adversary co-design the pair positions, pair depths,
on-line positions and multiplicities against the joint field at once.  The
mutual-exclusion mechanism of LEVEL6B (dense pair sets shield themselves,
sparse ones produce little negativity) is measured across swept
interpolations; this module attacks it at its optimum.

THE TARGET.  The retention inequality at theta, in the identification
dictionary's units (audit (*)), per configuration:

    damage  <=  (1 - theta) * R  +  sum_p slack(y_p)  +  cross,

    damage = -2 tr(P Q) = -2 sum_i m_i sum_p W(x_i - t_p, y_p),
    cross  = sum_{p != q} tr(Q_p Q_q) = 2 sum_{p<q} T(t_p - t_q, y_p, y_q),
    R      = sum_{i != j} m_i m_j omega^2(x_i - x_j)
             + sum_i m_i (m_i - 1) * omega^2(0),

so the adversary maximizes V = damage - cross - (1-theta) R - sum slack
and a violation is V > 0.  Note the SELF-STACKING term in R: the band
dual charges m zeros stacked on one band m(m-1) K (coincident distinct
points), so the defender's honest budget includes m_i (m_i - 1) at
omega^2(0) = 1.  `identification_seam.GridAssembly.R` omits it because
that battery never stacked; the matrix verification below therefore
expands multiplicities into coincident unit points, which restores it.

EVERYTHING IS CLOSED FORM during the search (`paper_chain.PaperChain`:
W, T, omega2, slack) -- microseconds per evaluation -- and the winners
are re-checked on explicit truncated-grid matrices (`GridAssembly`,
K = 1200) so no verdict rests on the closed forms alone.

WHAT A CLEAN RESULT DOES AND DOES NOT MEAN.  Finding V > 0 kills the
candidate 0.6725106958 (tenth defect; the ledger is built for it).
Finding V < 0 everywhere is a MEASUREMENT: local search over seeded
restarts, not a proof, and not the uniformity the audit names as the
open obligation.  It moves nothing up the ladder; it only fails to move
the candidate down.  Nothing here computes a proportion and nothing
here is evidence about RH.

Run ``.venv/bin/python hunts/frontier_math/coopt_adversary.py`` (~3 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import PaperChain  # noqa: E402

THETA = 0.995
#: pair depths live in the open strip; the closed-form field is smooth up
#: to y = 1/2 and the clamp below keeps the optimizer inside (0, 1/2).
Y_LO, Y_HI = 1e-4, 0.4999
#: positions beyond this are pointless (the kernel is O(1/g)) and the
#: clamp keeps Nelder-Mead from wandering off to flat infinity.
X_MAX = 60.0

_chain = PaperChain()


# ---------------------------------------------------------------------------
# the closed-form objective
# ---------------------------------------------------------------------------


def budget_terms(xs, ms, ts, ys, theta: float = THETA) -> dict:
    """All terms of (*) in closed form for one configuration."""
    xs = np.asarray(xs, float)
    ms = np.asarray(ms, float)
    ts = np.asarray(ts, float)
    ys = np.clip(np.asarray(ys, float), Y_LO, Y_HI)
    damage = 0.0
    for t, y in zip(ts, ys):
        damage += -2.0 * float((ms * _chain.W(xs - t, y)).sum())
    cross = 0.0
    for i in range(len(ts)):
        for j in range(i + 1, len(ts)):
            cross += 2.0 * _chain.T(ts[i] - ts[j], ys[i], ys[j])
    om2 = _chain.omega2(xs[:, None] - xs[None, :])
    M = np.outer(ms, ms) * om2
    R = float(M.sum() - np.trace(M)) + float((ms * (ms - 1)).sum())
    slack = float(sum(_chain.slack(y) for y in ys))
    return {"damage": damage, "cross": cross, "R": R, "slack": slack,
            "V": damage - cross - (1 - theta) * R - slack}


def V(xs, ms, ts, ys, theta: float = THETA) -> float:
    return budget_terms(xs, ms, ts, ys, theta)["V"]


# ---------------------------------------------------------------------------
# seeds: the structured corners plus rng restarts
# ---------------------------------------------------------------------------


def _damage_min(y: float, band: int = 1) -> float:
    """Argmin of W(., y) in the band-th negative band (closed form scan)."""
    g = np.arange(0.2, 25.0, 0.002)
    w = _chain.W(g, y)
    mins, lo = [], None
    for k in range(1, len(g)):
        if w[k] < 0 and lo is None:
            lo = k
        if lo is not None and (w[k] >= 0 or k == len(g) - 1):
            seg = slice(lo, k)
            mins.append(float(g[seg][np.argmin(w[seg])]))
            lo = None
            if len(mins) >= band:
                break
    return mins[band - 1]


def joint_damage_minima(pairs, n: int = 3, span: float = 30.0):
    """The n deepest local minima of the JOINT field sum_p W(. - t_p, y_p)."""
    g = np.arange(-span, span, 0.002)
    w = np.zeros_like(g)
    for t, y in pairs:
        w += _chain.W(g - t, y)
    idx = [k for k in range(1, len(g) - 1)
           if w[k] < w[k - 1] and w[k] <= w[k + 1] and w[k] < 0]
    idx.sort(key=lambda k: w[k])
    return [float(g[k]) for k in idx[:n]]


@dataclass
class Seed:
    name: str
    xs: list
    ms: list
    ts: list
    ys: list


def seeds() -> list:
    g1 = _damage_min(0.49, 1)
    g2 = _damage_min(0.49, 2)
    gs = _damage_min(0.05, 1)
    out = [
        Seed("single pair, one zero at min", [g1], [1], [0.0], [0.49]),
        Seed("single pair, m=2 at min", [g1], [2], [0.0], [0.49]),
        Seed("single pair, m=3 at min", [g1], [3], [0.0], [0.49]),
        Seed("single pair, zeros at two minima", [-g1, g1], [1, 1],
             [0.0], [0.49]),
        Seed("battery worst: double zeros both minima", [-g1, g1], [2, 2],
             [0.0], [0.49]),
        Seed("two near-coincident pairs", [-g1, g1], [1, 1],
             [0.0, 0.11], [0.49, 0.49]),
        Seed("two pairs, first-band offset", [g1, g1 + 6.406], [2, 2],
             [0.0, 6.406], [0.49, 0.49]),
        Seed("three pairs aligned shallow-deep",
             [g1], [2], [0.0, 0.0, 0.0], [0.49, 0.25, 0.1]),
        Seed("shallow pair, zero at its min", [gs], [1], [0.0], [0.05]),
        Seed("shallow pair, m=2", [gs], [2], [0.0], [0.05]),
        Seed("two shallow pairs aligned", [gs], [2], [0.0, 0.05],
             [0.05, 0.05]),
        Seed("lattice nu=0.5, zeros free", [g1, g2, -g1], [1, 1, 1],
             [k * 4 * math.pi for k in range(4)], [0.49] * 4),
    ]
    # on-line points at the JOINT minima of each multi-pair seed
    extra = []
    for s in out:
        if len(s.ts) >= 2:
            mins = joint_damage_minima(list(zip(s.ts, s.ys)), n=3)
            if mins:
                extra.append(Seed(s.name + " [joint minima]",
                                  mins, [2] * len(mins), s.ts, s.ys))
    return out + extra


def rng_seeds(count: int = 40, rng=None) -> list:
    rng = rng or np.random.default_rng(0)
    out = []
    for k in range(count):
        npair = int(rng.integers(1, 4))
        non = int(rng.integers(1, 4))
        ts = np.concatenate([[0.0], rng.uniform(-20, 20, npair - 1)])
        ys = rng.uniform(0.02, Y_HI, npair)
        xs = rng.uniform(-20, 20, non)
        ms = rng.integers(1, 4, non)
        out.append(Seed(f"rng{k}", list(xs), list(ms), list(ts), list(ys)))
    return out


# ---------------------------------------------------------------------------
# the search
# ---------------------------------------------------------------------------


def polish(seed: Seed, theta: float = THETA, maxiter: int = 4000) -> dict:
    """Nelder-Mead on [ts[1:], ys, xs] (t_0 pinned by translation
    invariance; multiplicities held at the seed's integers)."""
    npair, non = len(seed.ts), len(seed.xs)

    def unpack(v):
        ts = np.concatenate([[seed.ts[0]], v[:npair - 1]]) \
            if npair > 1 else np.asarray(seed.ts)
        ys = np.clip(v[npair - 1:2 * npair - 1], Y_LO, Y_HI)
        xs = np.clip(v[2 * npair - 1:], -X_MAX, X_MAX)
        return xs, ts, ys

    def neg(v):
        xs, ts, ys = unpack(v)
        return -V(xs, seed.ms, ts, ys, theta)

    v0 = np.concatenate([seed.ts[1:], seed.ys, seed.xs])
    res = minimize(neg, v0, method="Nelder-Mead",
                   options={"maxiter": maxiter, "fatol": 1e-12,
                            "xatol": 1e-8})
    xs, ts, ys = unpack(res.x)
    rec = budget_terms(xs, seed.ms, ts, ys, theta)
    rec.update({"name": seed.name, "xs": list(xs), "ms": list(seed.ms),
                "ts": list(ts), "ys": list(ys), "evals": res.nfev})
    return rec


def hunt(theta: float = THETA, rng_count: int = 40) -> list:
    rows = [polish(s, theta) for s in seeds() + rng_seeds(rng_count)]
    rows.sort(key=lambda r: -r["V"])
    return rows


def ratio_polish(seed: Seed, theta: float = THETA,
                 maxiter: int = 2500) -> dict:
    """Maximize the ENGAGED ratio (damage - cross) / budget instead of
    the difference.  The difference's supremum is 0, attained by
    decoupling (walk the zeros away, shrink the depth), so it says
    nothing about how close an engaged attack comes; the ratio does,
    and the single-pair dual's cap corresponds to ~0.49 of it."""
    npair, non = len(seed.ts), len(seed.xs)

    def unpack(v):
        ts = np.concatenate([[seed.ts[0]], v[:npair - 1]]) \
            if npair > 1 else np.asarray(seed.ts)
        ys = np.clip(v[npair - 1:2 * npair - 1], Y_LO, Y_HI)
        xs = np.clip(v[2 * npair - 1:], -X_MAX, X_MAX)
        return xs, ts, ys

    def neg(v):
        xs, ts, ys = unpack(v)
        r = budget_terms(xs, seed.ms, ts, ys, theta)
        budget = (1 - theta) * r["R"] + r["slack"]
        if budget < 1e-9:
            return 0.0
        return -(r["damage"] - r["cross"]) / budget

    v0 = np.concatenate([seed.ts[1:], seed.ys, seed.xs])
    res = minimize(neg, v0, method="Nelder-Mead",
                   options={"maxiter": maxiter, "fatol": 1e-10,
                            "xatol": 1e-7})
    xs, ts, ys = unpack(res.x)
    rec = budget_terms(xs, seed.ms, ts, ys, theta)
    budget = (1 - theta) * rec["R"] + rec["slack"]
    rec.update({"name": seed.name, "ratio": (rec["damage"] - rec["cross"])
                / budget if budget > 1e-9 else 0.0,
                "xs": list(xs), "ms": list(seed.ms),
                "ts": list(ts), "ys": list(ys)})
    return rec


# ---------------------------------------------------------------------------
# matrix verification of the winners (multiplicities expanded so the
# coincident-point self-stacking enters the matrix R as well)
# ---------------------------------------------------------------------------


def verify_on_matrices(rec: dict, K: int = 1200, jitter: float = 1e-9) -> dict:
    from identification_seam import GridAssembly
    xs, ms = [], []
    for x, m in zip(rec["xs"], rec["ms"]):
        for c in range(int(m)):
            xs.append(x + c * jitter)
            ms.append(1)
    ga = GridAssembly(xs, ms, list(zip(rec["ts"], rec["ys"])), K=K)
    damage = -2 * ga.trPQ()
    cross = ga.cross_total()
    R = ga.R()
    slack = sum(_chain.slack(y) for y in rec["ys"])
    Vm = damage - cross - (1 - THETA) * R - slack
    return {"V_matrix": Vm, "V_closed": rec["V"],
            "defect": abs(Vm - rec["V"]),
            "damage_matrix": damage, "cross_matrix": cross, "R_matrix": R}


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------


def dictionary_control(K: int = 1200) -> dict:
    """Closed forms against matrices on the battery's three ADV rows."""
    g1 = _damage_min(0.49, 1)
    g2 = _damage_min(0.49, 2)
    worst = 0.0
    for xs, ms in ([[-g1, g1], [1, 1]], [[-g2, -g1, g1, g2], [1] * 4],
                   [[-g1, g1], [2, 2]]):
        rec = budget_terms(xs, ms, [0.0], [0.49])
        chk = verify_on_matrices(
            {"xs": xs, "ms": ms, "ts": [0.0], "ys": [0.49], "V": rec["V"]},
            K=K)
        worst = max(worst, chk["defect"])
    return {"worst_defect": worst}


def lesion_budget_without_slack(theta: float = THETA) -> float:
    """Detector power: with the slack term deleted from the budget the
    battery's worst row MUST violate.  Returns that (positive) V."""
    g1 = _damage_min(0.49, 1)
    rec = budget_terms([-g1, g1], [2, 2], [0.0], [0.49], theta)
    return rec["V"] + rec["slack"]


def theta_one_control() -> tuple:
    """At theta = 1 the R charge is deleted, so stacking m zeros on the
    damage minimum is uncharged: the profit must grow linearly in m and
    end positive (which is exactly why both duals report cap = inf)."""
    g1 = _damage_min(0.49, 1)
    vals = []
    for m in (1, 4, 16):
        r = budget_terms([g1], [m], [0.0], [0.49], theta=1.0)
        vals.append(r["damage"] - r["cross"] - r["slack"])
    ok = vals[0] < vals[1] < vals[2] and vals[2] > 0
    return ok, vals


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------


def audit(rng_count: int = 40):
    print("= controls =")
    dc = dictionary_control()
    print(f"  dictionary (closed vs matrix, battery rows): "
          f"worst defect {dc['worst_defect']:.3e}")
    lv = lesion_budget_without_slack()
    print(f"  lesion (slack deleted from budget): V = {lv:+.5f} "
          f"({'violates as it must' if lv > 0 else 'LESION FAILED'})")
    ok, vals = theta_one_control()
    print(f"  theta=1 uncompensated profit grows with m: {vals} "
          f"({'ok' if ok else 'CONVENTION BROKEN'})")
    print(f"= the hunt (theta = {THETA}) =")
    rows = hunt(rng_count=rng_count)
    print(f"  {'seed':<44} {'V':>12} {'damage':>10} {'cross':>10} "
          f"{'R':>9} {'slack':>9}")
    for r in rows[:12]:
        print(f"  {r['name']:<44} {r['V']:>12.6f} {r['damage']:>10.5f} "
              f"{r['cross']:>10.5f} {r['R']:>9.4f} {r['slack']:>9.5f}")
    violations = [r for r in rows if r["V"] > 0]
    print(f"  restarts: {len(rows)}   violations: {len(violations)}")
    print("= matrix verification of the top three =")
    for r in rows[:3]:
        chk = verify_on_matrices(r)
        print(f"  {r['name']:<44} V_closed {chk['V_closed']:+.6f}   "
              f"V_matrix {chk['V_matrix']:+.6f}   defect {chk['defect']:.2e}")
    print("= engaged-ratio hunt (structured seeds) =")
    ratios = sorted((ratio_polish(s) for s in seeds()),
                    key=lambda r: -r["ratio"])
    for r in ratios[:5]:
        print(f"  {r['name']:<44} ratio {r['ratio']:>8.4f}   "
              f"damage {r['damage']:>9.5f}   slack {r['slack']:>9.5f}")
    worst_ratio = ratios[0]["ratio"]
    print(f"  worst engaged ratio: {worst_ratio:.4f} of budget "
          f"(violation would be > 1)")
    if violations:
        print("\n  *** VIOLATION FOUND: the candidate dies here; ledger it. ***")
    else:
        best = rows[0]
        print(f"\n  co-optimized worst margin: V = {best['V']:+.6f} "
              f"at '{best['name']}' -- measured, not a proof.")
    return rows


if __name__ == "__main__":
    audit()
