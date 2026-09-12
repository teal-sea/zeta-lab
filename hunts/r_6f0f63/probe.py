"""Hunt R-6F0F63, the ceiling of the Delsarte LP for kissing numbers.

The fourth instance of the lab's ceiling procedure (issue #110): reproduce a
published certificate, read its verifier for soundness, measure where the
method's own ceiling is, then push the method to that ceiling.

The object here is the **Delsarte / Odlyzko-Sloane linear programming bound**
for the kissing number tau_n.  The certificate is a single univariate
polynomial:

    f(t) = sum_{k=0}^{d} f_k G_k^{(n)}(t),   G_k^{(n)}(1) = 1

with

    (P1) f_0 > 0,
    (P2) f_k >= 0 for k >= 1,
    (P3) f(t) <= 0 for all t in [-1, 1/2],

and the conclusion tau_n <= f(1)/f_0 = (sum_k f_k)/f_0.

Everything in this file is float grade.  Nothing here is a bound on anything
until (P3) has been checked on the *interval*, which is the whole point of the
soundness half: the standard way to compute this bound discretises (P3) onto a
finite node set, and a discretised (P3) is a relaxation, so the LP optimum on a
node set is a number that can sit *below* the true LP value and therefore below
no valid bound at all.

Three things are measured:

  1. the raw LP optimum on a node grid (what the optimisation reports),
  2. the sup of f over the true interval (what the verifier must check), and
     the repaired bound (f(1) - M)/(f_0 - M) when the sup M is positive,
  3. the ceiling: the best value the parameterisation can reach as the degree
     d grows, and the degree at which it stops moving.

Run:  .venv/bin/python hunts/r_6f0f63/probe.py
"""

from __future__ import annotations

import json
import time
from pathlib import Path

import numpy as np
from numpy.polynomial import chebyshev as C
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent

# The constraint interval of the kissing-number problem: cos(60 degrees) = 1/2.
T_LO, T_HI = -1.0, 0.5


# ---------------------------------------------------------------------------
# 1. Gegenbauer polynomials, normalised to G_k(1) = 1
# ---------------------------------------------------------------------------
def gegenbauer_matrix(n: int, d: int, t: np.ndarray) -> np.ndarray:
    """Return the (len(t), d+1) matrix [G_0(t) ... G_d(t)] for dimension n.

    Recurrence (Odlyzko-Sloane 1979, eq. 2):
        G_0 = 1, G_1 = t,
        (k + n - 3) G_k = (2k + n - 4) t G_{k-1} - (k - 1) G_{k-2}.
    For n = 3 this is Legendre; for n = 2 it is Chebyshev T_k.  n = 1 is
    excluded: the denominator vanishes at k = 2.
    """
    if n < 2:
        raise ValueError("recurrence is degenerate for n < 2")
    t = np.asarray(t, dtype=float)
    out = np.empty((t.size, d + 1))
    out[:, 0] = 1.0
    if d >= 1:
        out[:, 1] = t
    for k in range(2, d + 1):
        out[:, k] = ((2 * k + n - 4) * t * out[:, k - 1] - (k - 1) * out[:, k - 2]) / (
            k + n - 3
        )
    return out


def cheb_nodes(m: int, lo: float = T_LO, hi: float = T_HI) -> np.ndarray:
    """m Chebyshev-clustered nodes on [lo, hi] (endpoints included)."""
    j = np.arange(m)
    x = np.cos(np.pi * j / (m - 1))          # 1 .. -1
    return 0.5 * (lo + hi) + 0.5 * (hi - lo) * x[::-1]


# ---------------------------------------------------------------------------
# 2. The verifier, the half the published number depends on and does not show
# ---------------------------------------------------------------------------
def sup_on_interval(n: int, f: np.ndarray) -> tuple[float, float]:
    """Return (M, t_star): the sup of f over [-1, 1/2] and where it is attained.

    f is a polynomial of degree d, so it is reconstructed *exactly* (up to
    rounding) by Chebyshev interpolation at d+1 nodes on the interval; the
    critical points are then the roots of the derivative, obtained from the
    Chebyshev companion matrix.  This does not depend on any node set the LP
    used, which is the point: the LP's own grid cannot certify itself.
    """
    d = f.size - 1
    fn = lambda t: gegenbauer_matrix(n, d, np.atleast_1d(t)) @ f  # noqa: E731
    p = C.Chebyshev.interpolate(fn, deg=d, domain=[T_LO, T_HI])
    cands = [T_LO, T_HI]
    if d >= 1:
        r = p.deriv().roots()
        r = r[np.abs(r.imag) < 1e-9].real
        cands.extend(r[(r >= T_LO) & (r <= T_HI)].tolist())
    cands = np.array(cands, dtype=float)
    vals = fn(cands)
    i = int(np.argmax(vals))
    return float(vals[i]), float(cands[i])


def repaired_bound(n: int, f: np.ndarray) -> dict:
    """Turn an LP output into a statement that survives its own verifier.

    If sup_{[-1,1/2]} f = M > 0 the polynomial is not admissible.  Shifting
    f -> f - M restores (P3) exactly, leaves every f_k (k>=1) untouched, and
    yields the valid value (f(1) - M)/(f_0 - M) whenever f_0 > M.  So a failed
    verification is not fatal, it is a *worse number*, and the difference
    between the two numbers is the size of the lie the grid was telling.
    """
    M, t_star = sup_on_interval(n, f)
    f0, f1 = float(f[0]), float(f.sum())
    if M <= 0.0:
        return {"sup": M, "t_star": t_star, "admissible": True, "value": f1 / f0}
    if f0 - M <= 0:
        return {"sup": M, "t_star": t_star, "admissible": False, "value": None}
    return {
        "sup": M,
        "t_star": t_star,
        "admissible": False,
        "value": (f1 - M) / (f0 - M),
    }


# ---------------------------------------------------------------------------
# 3. The LP
# ---------------------------------------------------------------------------
def lp_bound(n: int, d: int, m: int = 400) -> dict:
    """Solve the node-discretised Delsarte LP in dimension n at degree d."""
    t = cheb_nodes(m)
    A = gegenbauer_matrix(n, d, t)           # (m, d+1), constraint A f <= 0
    c = np.ones(d + 1)                       # minimise f(1) = sum f_k
    bounds = [(1.0, 1.0)] + [(0.0, None)] * d   # f_0 == 1 normalisation
    res = linprog(c, A_ub=A, b_ub=np.zeros(m), bounds=bounds, method="highs")
    if not res.success:
        # Low degrees are genuinely infeasible: f = f_0 + f_1 t with f_1 >= 0
        # cannot be <= 0 at t = 1/2 while f_0 = 1.  That is information, not an
        # error, so it is reported rather than raised.
        return {
            "n": n,
            "degree": d,
            "nodes": m,
            "status": str(res.message).split(".")[0],
            "grid_value": None,
            "sup_on_interval": None,
            "argmax": None,
            "admissible": False,
            "verified_value": None,
            "coeffs": None,
        }
    f = np.asarray(res.x, dtype=float)
    ver = repaired_bound(n, f)
    return {
        "n": n,
        "degree": d,
        "nodes": m,
        "status": "optimal",
        "grid_value": float(res.fun),
        "sup_on_interval": ver["sup"],
        "argmax": ver["t_star"],
        "admissible": ver["admissible"],
        "verified_value": ver["value"],
        "coeffs": f.tolist(),
    }


# ---------------------------------------------------------------------------
# 3b. Reproduction: the two published certificates, rebuilt from their roots
# ---------------------------------------------------------------------------
#: The inner products realised by the E8 root system and by the Leech minimal
#: vectors.  The optimal Delsarte polynomial vanishes to order 2 at the
#: interior contact values and to order 1 at the interval endpoints, which
#: fixes it up to scale.  Rebuilding it this way rather than copying printed
#: coefficients is the whole reproduction: if the structure is right the
#: Gegenbauer coefficients come out non-negative on their own.
CONTACT = {
    8: [-0.5, 0.0],
    24: [-0.5, -0.25, 0.0, 0.25],
}


def published_certificate(n: int) -> np.ndarray:
    """(t+1) * prod (t - c)^2 over interior contacts * (t - 1/2), in G_k basis."""
    p = np.polynomial.Polynomial([1.0, 1.0])            # t + 1
    for c in CONTACT[n]:
        p = p * np.polynomial.Polynomial([-c, 1.0]) ** 2
    p = p * np.polynomial.Polynomial([-0.5, 1.0])       # t - 1/2
    d = p.degree()
    x = np.cos(np.pi * np.arange(d + 1) / d)            # d+1 nodes on [-1, 1]
    return np.linalg.solve(gegenbauer_matrix(n, d, x), p(x))


# ---------------------------------------------------------------------------
# 4. The planted-fault ladder.  A verifier that cannot fail is not a verifier.
# ---------------------------------------------------------------------------
def _p2_slack(f: np.ndarray) -> float:
    """min_{k>=1} f_k: the second sign condition, which (P3) alone cannot see."""
    return float(f[1:].min()) if f.size > 1 else 0.0


def planted_faults() -> list[dict]:
    out = []

    for n, exact in ((8, 240.0), (24, 196560.0)):
        f = published_certificate(n)
        M, _ = sup_on_interval(n, f)
        val = f.sum() / f[0]
        out.append(
            {
                "fault": f"none (control): published certificate rebuilt, n={n}",
                "expect": f"P2 and P3 hold and the value is exactly {exact:.0f}",
                "sup": M,
                "p2_slack": _p2_slack(f),
                "value": val,
                "fired": not (M <= 1e-12 and _p2_slack(f) >= -1e-12),
                "pass": (
                    M <= 1e-12
                    and _p2_slack(f) >= -1e-12
                    and abs(val - exact) < 1e-6 * exact
                ),
            }
        )

    f8 = published_certificate(8)

    # (b) shift the polynomial up by eps: (P3) fails by exactly eps.
    bad = f8.copy()
    bad[0] += 0.01 * f8[0]
    M, _ = sup_on_interval(8, bad)
    out.append(
        {
            "fault": "f_0 *= 1.01 on the exact n=8 certificate (breaks P3)",
            "expect": "verifier reports sup ~ 0.01*f_0 > 0",
            "sup": M,
            "fired": M > 1e-9,
            "pass": abs(M - 0.01 * f8[0]) < 1e-9,
        }
    )

    # (c) break (P2) instead of (P3): a defect no interval scan of f can see.
    bad = f8.copy()
    k = int(np.argmax(bad[1:])) + 1
    bad[k] = -abs(bad[k])
    M, _ = sup_on_interval(8, bad)
    out.append(
        {
            "fault": f"f_{k} negated on the exact n=8 certificate (breaks P2 only)",
            "expect": "P3 scan stays clean; only the P2 check fires",
            "sup": M,
            "p2_slack": _p2_slack(bad),
            "fired": _p2_slack(bad) < 0,
            "pass": _p2_slack(bad) < 0,
        }
    )

    # (d) a deliberately starved node set: the failure mode the procedure is
    #     looking for.  Few nodes -> the LP reports a value below the truth.
    coarse = lp_bound(8, 12, m=14)
    out.append(
        {
            "fault": "node set starved to 14 points at degree 12, n=8",
            "expect": "grid value below 240 and verifier reports sup > 0",
            "grid_value": coarse["grid_value"],
            "sup": coarse["sup_on_interval"],
            "fired": coarse["sup_on_interval"] > 1e-9,
            "pass": coarse["sup_on_interval"] > 1e-9 and coarse["grid_value"] < 240.0,
        }
    )
    return out


# ---------------------------------------------------------------------------
# 5. The sweeps
# ---------------------------------------------------------------------------
def degree_sweep(dims, dmax: int = 30, m: int = 600, tol: float = 1e-6) -> dict:
    """For each dimension: the value as a function of degree, and the ceiling.

    The ceiling is the best *verified* value the parameterisation reaches over
    d <= dmax, and the smallest degree that reaches it to within `tol`
    relative.  A ceiling reported at d = dmax is a floor on the ceiling, not
    the ceiling: say so rather than pretending the sweep saturated.
    """
    table = {}
    for n in dims:
        curve, best, best_d = [], float("inf"), None
        for d in range(1, dmax + 1):
            r = lp_bound(n, d, m=m)
            v = r["verified_value"]
            curve.append(
                {
                    "degree": d,
                    "grid_value": r["grid_value"],
                    "verified_value": v,
                    "sup": r["sup_on_interval"],
                    "admissible": r["admissible"],
                }
            )
            if v is not None and (best_d is None or v < best * (1 - 1e-12)):
                best, best_d = v, d
        # smallest degree within tol (relative) of the best value seen
        sat = next(
            (c["degree"] for c in curve
             if c["verified_value"] is not None
             and c["verified_value"] <= best * (1 + tol)),
            None,
        )
        table[str(n)] = {
            "ceiling": best,
            "argmin_degree": best_d,
            "saturation_degree": sat,
            "sweep_exhausted": best_d == dmax,
            "curve": curve,
        }
    return table


def node_sweep(n: int, d: int, ms) -> list[dict]:
    """The other free parameter: how many nodes the semi-infinite constraint got."""
    return [
        {k: v for k, v in lp_bound(n, d, m=m).items() if k != "coeffs"} for m in ms
    ]


# ---------------------------------------------------------------------------
def main() -> None:
    t0 = time.time()
    dims = list(range(3, 25))

    faults = planted_faults()
    if not all(x["pass"] for x in faults):
        print("PLANTED-FAULT LADDER FAILED; the sweep below is not to be trusted")

    sweep = degree_sweep(dims, dmax=30, m=600)
    ms = [8, 12, 20, 40, 100, 300, 600, 1200, 2400, 5000, 10000, 20000]
    nodes = node_sweep(24, 10, ms)
    nodes8 = node_sweep(8, 6, [4, 6, 8, 12, 20, 60, 200, 600, 2400, 10000, 40000])
    # The soundness headline, as a boolean rather than a paragraph: a node set
    # can make the LP report a "bound" that is *below* the true kissing number.
    for row in nodes:
        row["false_bound"] = row["grid_value"] is not None and row["grid_value"] < 196560
    for row in nodes8:
        row["false_bound"] = row["grid_value"] is not None and row["grid_value"] < 240

    # The two anchors that need no citation: the LP is exactly tight in
    # dimensions 8 and 24, where it proves tau_8 = 240 and tau_24 = 196560.
    anchors = {}
    for n, exact in ((8, 240.0), (24, 196560.0)):
        f = published_certificate(n)
        anchors[str(n)] = {
            "exact_kissing_number": exact,
            "certificate_degree": f.size - 1,
            "certificate_value": f.sum() / f[0],
            "certificate_sup": sup_on_interval(n, f)[0],
            "certificate_p2_slack": _p2_slack(f),
            "gegenbauer_coeffs_normalised": (f / f[0]).tolist(),
            "lp_ceiling": sweep[str(n)]["ceiling"],
        }

    out = {
        "hunt": "r_6f0f63",
        "object": "Delsarte/Odlyzko-Sloane LP bound for kissing numbers",
        "grade": "measured (float); no interval arithmetic anywhere in this file",
        "planted_faults": faults,
        "degree_sweep": sweep,
        "node_sweep_n24_d10": nodes,
        "node_sweep_n8_d6": nodes8,
        "anchors": anchors,
        "seconds": round(time.time() - t0, 1),
    }
    def _plain(o):
        if isinstance(o, np.bool_):
            return bool(o)
        if isinstance(o, np.integer):
            return int(o)
        if isinstance(o, np.floating):
            return float(o)
        raise TypeError(type(o))

    (HERE / "results.json").write_text(
        json.dumps(out, indent=2, default=_plain) + "\n"
    )

    print(f"planted faults: {sum(x['pass'] for x in faults)}/{len(faults)} pass")
    print(f"{'n':>3} {'ceiling':>14} {'deg':>4} {'sat':>4} {'exhausted':>9}")
    for n in dims:
        s = sweep[str(n)]
        print(
            f"{n:>3} {s['ceiling']:>14.3f} {s['argmin_degree']:>4} "
            f"{s['saturation_degree']:>4} {str(s['sweep_exhausted']):>9}"
        )
    print(f"\n{out['seconds']} s -> results.json")


if __name__ == "__main__":
    main()
