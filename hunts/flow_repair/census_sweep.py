"""Landing times for every off-line pair of the Davenport-Heilbronn v6 census.

Run from the repo root (about 3 minutes on 16 cores):

    .venv/bin/python hunts/flow_repair/census_sweep.py --procs 16

Writes ``census_sweep.jsonl`` next to this file, one line per v6 pair.

Inputs, read from ``data/dh_v6_replay/receipts.tar.gz`` after checking the
manifest's SHA-256 values (``scripts/dh_v6_replay_audit.load_receipts``):

- the 1,268 off-line pairs of ``dh_zeros_master_v6.csv`` (Nathan Berzai,
  Zenodo 10.5281/zenodo.23585903, data CC-BY-4.0);
- the 25,078 on-line ordinates, the ``online_approx`` lists of the 400 window
  receipts. Each window closes, on-line + 2 x off-line = total
  (``docs/46-davenport-heilbronn-v6-arb-replay.md``), so a +/-40 window built
  from these lists holds every zero the census has there.

The dynamics are this hunt's ODE null control (``probe.ode_null_control``,
NOTES.md section 3): the measured t = 0 zero configuration moved by
dz_k/dt = 2 sum 1/(z_k - z_j) in the collision-safe variable Q, same window
(+/-40), same 800 RK4 steps, same mirror terms and density tail, same t_end
rule (1.25 y0^2/2 when no PDE landing is on record). ``ode_np`` is a numpy
transcription of that function; ``test_census_sweep.py`` holds it equal to the
original on identical inputs. No zero is searched for at run time, which is
what makes the whole census a three-minute job instead of weeks: re-finding
the window zeros per pair by sign scan costs 7 to 12 CPU hours a pair near
height 20,000.

Scope, in this hunt's vocabulary: every number is measured, a float ODE model
of zero motion. The model was compared with the measured PDE flow only up to
height 412 (agreement under 0.04%, NOTES.md section 3). Pairs whose window
runs past the census top (height 20,000) miss zeros above it and are flagged
``edge``.
"""

from __future__ import annotations

import argparse
import csv
import importlib.util
import io
import json
import math
import sys
import time
from bisect import bisect_left, bisect_right
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
OUT = HERE / "census_sweep.jsonl"
W, STEPS = 40.0, 800
CENSUS_TOP = 20000.0


def mean_gap(gamma: float) -> float:
    """Same as probe.mean_gap: 2 pi / log(5 gamma / 2 pi)."""
    return 2 * math.pi / math.log(5 * gamma / (2 * math.pi))


def load_census() -> tuple[list[dict], list[float]]:
    """(pairs, sorted on-line ordinates) from the hash-checked replay tarball."""
    spec = importlib.util.spec_from_file_location(
        "dh_v6_replay_audit", REPO / "scripts" / "dh_v6_replay_audit.py")
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    windows, _rows, _closure, _hashes = audit.load_receipts(
        str(REPO / "data/dh_v6_replay/receipts.tar.gz"),
        str(REPO / "data/dh_v6_replay/manifest.json"))
    import tarfile
    with tarfile.open(REPO / "data/dh_v6_replay/receipts.tar.gz") as tf:
        text = tf.extractfile("dh_zeros_master_v6.csv").read().decode()
    pairs = [{"n": int(r["n_v6"]), "gamma": float(r["t"]), "sigma": float(r["sigma"])}
             for r in csv.DictReader(io.StringIO(text))]
    online = sorted(x for w in windows.values() for x in w["online_approx"])
    return pairs, online


def ode_np(x0: float, y0: float, reals, others, t_end: float,
           n_steps: int = STEPS, window: float = W) -> tuple[float | None, float]:
    """probe.ode_null_control, vectorized. Returns (t*, dDelta/dt at t = 0)."""
    rho = 1.0 / mean_gap(x0)
    px = np.array([x0] + [p["x"] for p in others], float)
    pq = np.array([-y0 * y0] + [-p["y"] ** 2 for p in others], float)
    rw = np.array(reals, float)
    nr, npair = len(rw), len(px)
    # sources: reals, mirrored reals, pair members x +- sqrt(Q), mirrored members
    ns = 2 * nr + 4 * npair
    mask_r = np.ones((nr, ns), bool)
    mask_r[np.arange(nr), np.arange(nr)] = False            # a real zero skips itself
    mask_p = np.ones((npair, ns), bool)
    mask_p[np.arange(npair), 2 * nr + np.arange(npair)] = False          # a pair skips
    mask_p[np.arange(npair), 2 * nr + npair + np.arange(npair)] = False  # its own members

    def rhs(px, pq, rw):
        s = np.sqrt(pq.astype(complex))
        src = np.concatenate([rw, -rw, px + s, px - s, -px + s, -px - s]).astype(complex)
        d = px[:, None] - src[None, :]
        den = np.where(mask_p, d * d - pq[:, None], 1.0)
        sq = ((1.0 / den).real * mask_p).sum(1) + 2 * rho / window + rho / (2 * np.abs(px) - window)
        dpx = ((2 * d / den).real * mask_p).sum(1)
        dpq = 2.0 - 4.0 * pq * sq
        d = rw[:, None] - src[None, :]
        den = np.where(mask_r, d * d, 1.0)
        drw = ((2 * d / den).real * mask_r).sum(1)
        return dpx, dpq, drw

    h = t_end / n_steps
    t, tstar, slope0 = 0.0, None, None
    q_prev, t_prev = pq[0], 0.0
    for _ in range(n_steps):
        k1 = rhs(px, pq, rw)
        if slope0 is None:
            slope0 = 4.0 * k1[1][0]
        k2 = rhs(px + h / 2 * k1[0], pq + h / 2 * k1[1], rw + h / 2 * k1[2])
        k3 = rhs(px + h / 2 * k2[0], pq + h / 2 * k2[1], rw + h / 2 * k2[2])
        k4 = rhs(px + h * k3[0], pq + h * k3[1], rw + h * k3[2])
        px = px + h / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0])
        pq = pq + h / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1])
        rw = rw + h / 6 * (k1[2] + 2 * k2[2] + 2 * k3[2] + k4[2])
        t += h
        q_now = pq[0]
        if tstar is None and q_prev < 0 <= q_now:
            tstar = t_prev + (0.0 - q_prev) * (t - t_prev) / (q_now - q_prev)
        q_prev, t_prev = q_now, t
    return (None if tstar is None else float(tstar)), float(slope0)


_CENSUS: tuple[list[dict], list[float]] | None = None


def census() -> tuple[list[dict], list[float]]:
    global _CENSUS
    if _CENSUS is None:
        _CENSUS = load_census()
    return _CENSUS


def window_config(n: int):
    """(gamma, y0, on-line zeros in the window, other census pairs in the window).
    Same window rule as probe.stage_ode / line_zeros_near."""
    pairs, online = census()
    p = next(q for q in pairs if q["n"] == n)
    g, y0 = p["gamma"], p["sigma"] - 0.5
    reals = online[bisect_left(online, max(1.0, g - W)):bisect_right(online, g + W)]
    others = [{"x": q["gamma"], "y": q["sigma"] - 0.5}
              for q in pairs if q["n"] != n and abs(q["gamma"] - g) < W]
    return g, y0, reals, others


def land(n: int) -> dict:
    g, y0, reals, others = window_config(n)
    tstar, slope0 = ode_np(g, y0, reals, others, 1.25 * 0.5 * y0 * y0)
    return {"n": n, "gamma": g, "y0": y0, "tstar_ode": tstar, "slope0_ode": slope0,
            "isolated_y0sq_half": 0.5 * y0 * y0, "n_reals": len(reals),
            "n_other_pairs": len(others), "edge": g + W > CENSUS_TOP}


def main() -> None:
    from multiprocessing import Pool
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--procs", type=int, default=8)
    args = ap.parse_args()
    ns = sorted(p["n"] for p in census()[0])
    t0 = time.time()
    with Pool(args.procs) as pool:
        recs = pool.map(land, ns, chunksize=4)
    with open(OUT, "w", encoding="utf-8") as f:
        for r in recs:
            f.write(json.dumps(r) + "\n")
    print(f"{len(recs)} pairs, {time.time() - t0:.1f}s wall -> {OUT.name}")


if __name__ == "__main__":
    sys.path.insert(0, str(REPO))
    main()
