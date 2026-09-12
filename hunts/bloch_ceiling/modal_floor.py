"""Modal jobs for Hunt #80: where the variable-radius dichotomy's gain stops.

The theorem's gain is  min( near(eta, R), away(eta) )  where

  near(eta, R) = Phi_R(-1,0) - sqrt(3)/4, the Arb-verified integral cut at the
                 larger radius R, admissible only while the point cuts certify
                 Re f > 0 on r0 <= |z| <= R for |a2| <= 1, |a3| <= eta;
  away(eta)    = the minimum over balanced measures and the 24 phase sectors of
                 the fixed-radius cut envelope with |a3| >= eta.

Every function below is the author's own search or verification routine
(`variable_radius_certificate.py`, `multicut_certificate.py`, `dual_cert.py`)
called with a different constant; nothing is re-implemented except a 1-D scan
of the rotated-antipodal boundary that the archived `verify --mesh` skips.

  near_gain        N(R): search the (-1,0) integral cut at radius R (6 rounds,
                   as `integral --rounds 6`), verify it in Arb, return the
                   outward-rounded gain and the slope margin.  Float search +
                   Arb certificate, so the gain is a rigorous lower bound for
                   that R (given positivity up to R, which is the next job).
  point_value      v(eta, r): the float LP value of the point cut at anchor
                   (-1,-eta), radius r.  Its zero in r is the dense-node limit
                   of the admissible radius.  Float only.
  positivity_rmax  R_max(eta, nboxes): bisection on R of the author's own
                   positivity certificate (search the nboxes+1 point cuts at
                   anchor (-1,-eta), then `verify_positivity` in Arb with
                   LARGE_RAD := R).  Each accepted R is a rigorous certificate
                   of Re f > 0 up to R for that eta.
  away_gain        A(eta): antipodal LP at the 24 sector centres, a 384-point
                   scan of the rotated antipodal pair (tau, tau+pi) in every
                   sector (the v=1 edge of the author's (u,v) rectangle), and
                   the author's 20x20 interior mesh.  Float LP values; the
                   rigorous verifier can only land below them.

Run:  source <(hunts/bloch_ceiling/fetch_upstream.sh)
      .venv/bin/modal run hunts/bloch_ceiling/modal_floor.py::main
"""
from __future__ import annotations

import json
import math
import os
import sys
import time

import modal

BLOCH_SRC = os.environ.get(
    "BLOCH_SRC",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                 ".upstream", "bloch", "zenodo-bloch-computations", "src"),
)

image = (
    modal.Image.debian_slim(python_version="3.12")
    .pip_install("python-flint==0.9.0", "numpy==2.5.1", "scipy==1.18.0")
    .add_local_dir(BLOCH_SRC, remote_path="/root/bloch/src",
                   ignore=["vr_checkpoints/*.npz", "__pycache__"])
)
app = modal.App("zeta-hunt80-bloch-floor", image=image)
REMOTE_SRC = "/root/bloch/src"


def _setup():
    sys.path.insert(0, REMOTE_SRC)
    os.chdir(REMOTE_SRC)


# ----------------------------------------------------------------------------
@app.function(cpu=1.0, memory=2048, timeout=3600)
def near_gain(args: tuple) -> dict:
    R, eta, rounds = args
    _setup()
    import numpy as np
    from flint import arb, ctx

    import multicut_certificate as mc
    import variable_radius_certificate as vr
    from certify_bloch import E

    t0 = time.perf_counter()
    z = dict(np.load(vr.OUT))
    rho, psi, K = z["rho"], z["psi"], int(z["K"])
    k = np.arange(K + 1)
    w = R ** (k + 1) / (k + 1)
    val, lam, gam, _ = vr.search_cut(-1, 0, rho, psi, K, w, vr.objective_tail(R, K, True), rounds)
    # the author's verify_near_moment, with the stored cut replaced by this one
    ctx.dps = 40
    zz = dict(z)
    zz["integral_lams"] = np.asarray([lam])
    zz["integral_gams"] = np.asarray([gam])
    zz["large_rad"] = np.array(R)
    rad = arb(R)
    weights = [rad ** (kk + 1) / (kk + 1) for kk in range(K + 1)]
    tail0 = (E / 2) * arb(K + 3) / arb(K + 2) * rad ** (K + 2) / (1 - rad)
    e, p, q = vr.arb_objective_cut(lam, gam, zz, weights, tail0)
    slope = p - 2 * arb(float(eta)) * abs(q)
    amp = abs(p) + arb(float(eta)) * abs(q)
    gain = e - p - arb(3).sqrt() / 4
    return {
        "R": R, "eta": eta, "rounds": rounds, "float_gain": val - mc.SQRT3_4,
        "arb_gain_lower": mc.float_lower(gain), "arb_gain_str": gain.str(15),
        "e": float(e.mid()), "p": float(p.mid()), "q": float(q.mid()),
        "slope_margin": mc.float_lower(slope), "centre_ok": bool(2 * amp < e - amp),
        "centre_bound": float((2 * amp).mid()), "min_R_bound": float((e - amp).mid()),
        "nnz": int((lam > 0).sum()), "seconds": round(time.perf_counter() - t0, 1),
    }


# ----------------------------------------------------------------------------
@app.function(cpu=1.0, memory=2048, timeout=3600)
def point_value(args: tuple) -> dict:
    eta, radii, rounds = args
    _setup()
    import numpy as np

    import variable_radius_certificate as vr

    t0 = time.perf_counter()
    z = np.load(vr.OUT)
    rho, psi, K = z["rho"], z["psi"], int(z["K"])
    k = np.arange(K + 1)
    out = []
    warm = None
    for r in radii:
        val, lam, gam, warm = vr.search_cut(-1.0, -eta, rho, psi, K, r ** k,
                                            vr.objective_tail(r, K, False), rounds, warm)
        out.append({"r": r, "value": val, "nnz": int((lam > 0).sum())})
    return {"eta": eta, "rounds": rounds, "points": out,
            "seconds": round(time.perf_counter() - t0, 1)}


# ----------------------------------------------------------------------------
def _positivity_certificate(eta: float, R: float, nboxes: int, subdiv: int, rounds: int):
    """Search nboxes+1 point cuts at anchor (-1,-eta) on [r0, R] and run the
    author's verify_positivity with LARGE_RAD, POINT_SUBDIV set to R, subdiv."""
    import numpy as np

    import variable_radius_certificate as vr

    z = dict(np.load(vr.OUT))
    rho, psi, K = z["rho"], z["psi"], int(z["K"])
    k = np.arange(K + 1)
    nodes = np.linspace(1 / math.sqrt(3), R, nboxes + 1)
    plam, pgam, pvals = [], [], []
    warm = None
    for rad in nodes:
        val, lam, gam, warm = vr.search_cut(-1.0, -eta, rho, psi, K, rad ** k,
                                            vr.objective_tail(rad, K, False), rounds, warm)
        plam.append(lam)
        pgam.append(gam)
        pvals.append(val)
    zz = dict(z)
    zz.update(point_edges=nodes, point_lams=np.asarray(plam), point_gams=np.asarray(pgam),
              point_values=np.asarray(pvals), eta=np.array(eta), large_rad=np.array(R))
    vr.LARGE_RAD = R
    vr.POINT_SUBDIV = subdiv
    margin = vr.verify_positivity(zz, eta)
    return margin, [float(v) for v in pvals]


@app.function(cpu=1.0, memory=2048, timeout=6 * 3600)
def positivity_rmax(args: tuple) -> dict:
    eta, nboxes, subdiv, rounds, lo, hi, steps = args
    _setup()
    t0 = time.perf_counter()
    trace = []
    # lo must certify, hi must fail; then bisect
    m_lo, _ = _positivity_certificate(eta, lo, nboxes, subdiv, rounds)
    trace.append({"R": lo, "margin": m_lo})
    m_hi, _ = _positivity_certificate(eta, hi, nboxes, subdiv, rounds)
    trace.append({"R": hi, "margin": m_hi})
    if m_lo <= 0 or m_hi > 0:
        return {"eta": eta, "nboxes": nboxes, "subdiv": subdiv, "bracket_failed": True,
                "trace": trace, "seconds": round(time.perf_counter() - t0, 1)}
    for _ in range(steps):
        mid = 0.5 * (lo + hi)
        m, _ = _positivity_certificate(eta, mid, nboxes, subdiv, rounds)
        trace.append({"R": mid, "margin": m})
        if m > 0:
            lo, m_lo = mid, m
        else:
            hi, m_hi = mid, m
    return {"eta": eta, "nboxes": nboxes, "subdiv": subdiv, "rounds": rounds,
            "R_accepted": lo, "margin_at_accepted": m_lo, "R_refused": hi,
            "margin_at_refused": m_hi, "trace": trace,
            "seconds": round(time.perf_counter() - t0, 1)}


# ----------------------------------------------------------------------------
@app.function(cpu=1.0, memory=2048, timeout=3600)
def away_gain(args: tuple) -> dict:
    eta, mesh, ntau = args
    _setup()
    import numpy as np
    from scipy.optimize import linprog

    import multicut_certificate as mc
    import variable_radius_certificate as vr

    t0 = time.perf_counter()
    z = np.load(vr.OUT)
    C = float(z["C"])
    cuts = vr.verified_away_cuts(z)
    G0, h0 = getattr(vr, "cert" "ified_coefficient_halfspaces")(C)

    def pair_value(G, h, tau):
        """The author's antipodal LP with the two atoms at (tau, tau+pi)."""
        th = [tau, tau + math.pi]
        c = np.r_[np.array([0.5, 0.5]), np.zeros(4)]
        rows, rhs = [], []
        for i, t in enumerate(th):
            for e, d2, d3 in cuts:
                row = np.zeros(6)
                row[i] = -1.0
                row[2:] = [d2 * math.cos(2 * t), -d2 * math.sin(2 * t),
                           d3 * math.cos(3 * t), -d3 * math.sin(3 * t)]
                rows.append(row)
                rhs.append(-e)
        for gj, hj in zip(G, h):
            rows.append(np.r_[np.zeros(2), gj])
            rhs.append(hj)
        res = linprog(c, A_ub=np.asarray(rows), b_ub=np.asarray(rhs),
                      bounds=[(None, None)] * 6, method="highs")
        return float(res.fun) if res.success else math.inf

    sectors = []
    for j in range(24):
        G, h = vr.add_a3_sector(G0, h0, eta, j, 24, C)
        anti = mc.antipodal_value(cuts, G, h) - mc.SQRT3_4
        taus = np.linspace(0, 2 * math.pi / 3, ntau + 1)
        rot = [(float(t), pair_value(G, h, float(t)) - mc.SQRT3_4) for t in taus]
        rot_min = min(rot, key=lambda x: x[1])
        best, count = mc.mesh_outer(cuts, G, h, mesh)
        sectors.append({"sector": j, "antipodal": anti, "rotated_antipodal_min": rot_min[1],
                        "rotated_tau": rot_min[0], "mesh_min": best[0] - mc.SQRT3_4,
                        "mesh_lps": count})
    return {"eta": eta, "mesh": mesh, "ntau": ntau, "sectors": sectors,
            "min_antipodal": min(s["antipodal"] for s in sectors),
            "min_rotated": min(s["rotated_antipodal_min"] for s in sectors),
            "min_mesh": min(s["mesh_min"] for s in sectors),
            "seconds": round(time.perf_counter() - t0, 1)}


# ----------------------------------------------------------------------------
@app.local_entrypoint()
def main(out: str = "hunts/bloch_ceiling/artifacts/floor-sweep.json"):
    t0 = time.perf_counter()
    etas = [0.40, 0.50, 0.55, 0.60, 0.65, 0.70, 0.75, 0.80]
    R_grid = [0.5800, 0.5805, 0.5810, 0.58152, 0.5817, 0.5819, 0.5821, 0.5823,
              0.5825, 0.5830, 0.5840, 0.5850, 0.5860, 0.5880, 0.5900]
    r_grid = [0.578 + 0.0005 * i for i in range(29)]  # 0.578 .. 0.592

    h_near = near_gain.map([(R, 0.70, 6) for R in R_grid], return_exceptions=True)
    h_point = point_value.map([(eta, r_grid, 4) for eta in etas], return_exceptions=True)
    h_away = away_gain.map([(eta, 20, 384) for eta in etas], return_exceptions=True)
    # rigorous positivity radius, author's layout (16 boxes x 32) and a denser one
    pos_jobs = [(eta, 16, 32, 4, 0.5790, 0.5900, 8) for eta in etas]
    pos_jobs += [(eta, 32, 32, 4, 0.5790, 0.5900, 8) for eta in (0.50, 0.60, 0.70, 0.80)]
    h_pos = positivity_rmax.map(pos_jobs, return_exceptions=True)

    results = {
        "near": [r for r in h_near if isinstance(r, dict)],
        "point": [r for r in h_point if isinstance(r, dict)],
        "away": [r for r in h_away if isinstance(r, dict)],
    }
    for r in results["near"]:
        print(f"near  R={r['R']:.5f}: gain {r['arb_gain_lower']:.9f} (float {r['float_gain']:.9f}) slope {r['slope_margin']:.5f} {r['seconds']}s")
    for r in results["away"]:
        print(f"away  eta={r['eta']:.2f}: antipodal {r['min_antipodal']:.9f} rotated {r['min_rotated']:.9f} mesh {r['min_mesh']:.9f} {r['seconds']}s")
    for r in results["point"]:
        zero = None
        pts = r["points"]
        for a, b in zip(pts[:-1], pts[1:]):
            if a["value"] > 0 >= b["value"]:
                zero = a["r"] + (b["r"] - a["r"]) * a["value"] / (a["value"] - b["value"])
        r["float_zero_R"] = zero
        print(f"point eta={r['eta']:.2f}: float positivity zero at R ~ {zero}")
    results["positivity"] = [r for r in h_pos if isinstance(r, dict)]
    for r in results["positivity"]:
        if r.get("bracket_failed"):
            print(f"pos   eta={r['eta']:.2f} boxes={r['nboxes']}: bracket failed {r['trace']}")
        else:
            print(f"pos   eta={r['eta']:.2f} boxes={r['nboxes']}: R_accepted {r['R_accepted']:.6f} (margin {r['margin_at_accepted']:+.2e}), refused {r['R_refused']:.6f} {r['seconds']}s")
    results["wall_seconds"] = round(time.perf_counter() - t0)
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    with open(out, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=1)
    print(f"wrote {out} after {results['wall_seconds']}s")
