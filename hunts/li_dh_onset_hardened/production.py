"""The pre-registered production runs (MISSION.md, "Pre-registration").

One process. In order:
1. the box gates (load, MemAvailable);
2. the controls, whose failure voids the run: the xi positive control with
   both planted faults, and the 20-node mpmath.iv subsample on this run's own
   circle;
3. M(rho) by the ball arc cover;
4. f at the N/2 + 1 upper nodes in chunks of 2^16, each chunk checkpointed
   exactly (mantissa and exponent of midpoint and radius) under
   ``artifacts/ckpt_<tag>/`` so a killed run resumes; log G is recomputed (cheap);
5. tracking, ``acb.dft``, the aliasing bound, lambda_n for n <= n_max;
6. the decision as pre-registered, and the full table written to
   ``artifacts/big/lambda_<tag>.txt`` (gitignored; SHA-256 in the summary),
   one rigorous ``arb`` string per n.

Usage:
  .venv/bin/python hunts/li_dh_onset_hardened/production.py --tag A --c 5000 --log2N 21 --prec 192
  .venv/bin/python hunts/li_dh_onset_hardened/production.py --tag B --c 2500 --log2N 19 --prec 256
Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pickle
import sys
import time
from fractions import Fraction as Q

from flint import acb, arb, fmpz

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import evaluator  # noqa: E402
from balls import HERE, f_ball, logG_ball, prec_guard, q_arb  # noqa: E402
from trapezoid import DHModel, bound_M, li_balls, node, s_of  # noqa: E402

ART = os.path.join(HERE, "artifacts")
CHUNK = 2 ** 16


def log(msg: str) -> None:
    print(time.strftime("%H:%M:%S"), msg, flush=True)


def gates() -> None:
    while float(open("/proc/loadavg").read().split()[0]) > 64:
        log("load above 64, waiting")
        time.sleep(30)
    mem = {l.split(":")[0]: int(l.split()[1]) for l in open("/proc/meminfo")}
    if mem["MemAvailable"] < 20 * 2 ** 20:
        raise SystemExit("MemAvailable below 20 GiB: not starting")


def _pack(x: arb) -> tuple:
    m, e = x.mid().man_exp()
    rm, re = x.rad().man_exp()
    return (int(m), int(e), int(rm), int(re))


def _unpack(t: tuple) -> arb:
    m, e, rm, re = t
    mid = arb(fmpz(m)) * arb(2) ** e
    rad = arb(fmpz(rm)) * arb(2) ** re
    return arb(mid, rad)


def evaluate_with_checkpoints(r: arb, N: int, prec: int, tag: str) -> tuple:
    half = N // 2
    ck = os.path.join(ART, f"ckpt_{tag}")
    os.makedirs(ck, exist_ok=True)
    model = DHModel()
    H = []
    for c0 in range(0, half + 1, CHUNK):
        c1 = min(c0 + CHUNK, half + 1)
        path = os.path.join(ck, f"f_{c0:08d}.pkl")
        if os.path.exists(path):
            with prec_guard(prec):
                rows = pickle.load(open(path, "rb"))
                H += [acb(_unpack(a), _unpack(b)) for a, b in rows]
            log(f"chunk {c0} resumed")
            continue
        t0 = time.time()
        with prec_guard(prec):
            vals = [f_ball(s_of(node(r, k, N)), prec) for k in range(c0, c1)]
            rows = [(_pack(v.real), _pack(v.imag)) for v in vals]
        with open(path + ".tmp", "wb") as fh:
            pickle.dump(rows, fh)
        os.replace(path + ".tmp", path)
        H += vals
        log(f"chunk {c0}..{c1} {time.time() - t0:.1f} s")
        gates()
    t0 = time.time()
    with prec_guard(prec):
        L, P = [], []
        for k in range(half + 1):
            s = s_of(node(r, k, N))
            L.append(logG_ball(s, prec))
            P.append(model.principal(s))
    log(f"log G and principal flags {time.time() - t0:.1f} s")
    return L, H, P


def controls(c: int, N: int) -> dict:
    out = {"xi": evaluator.xi_control()}
    keep = (evaluator.C, evaluator.NPROD)
    try:
        evaluator.C, evaluator.NPROD = c, N
        out["iv"] = evaluator.iv_crosscheck()
    finally:
        evaluator.C, evaluator.NPROD = keep
    out["iv"].pop("nodes", None)
    out["ok"] = bool(out["xi"]["control_ok"] and out["iv"]["all_meet"]
                     and out["iv"]["planted_kappa_fault_caught_at"] > 0)
    return out


def decide(lam: list) -> dict:
    first_neg, undecided = None, []
    min_lower, min_at = None, None
    for i, x in enumerate(lam):
        n = i + 1
        if x < 0:
            first_neg = n
            break
        if not (x > 0):
            undecided.append(n)
        lo = float(x.lower().mid())
        if min_lower is None or lo < min_lower:
            min_lower, min_at = lo, n
    return {"first_ball_negative_n": first_neg, "undecided_before": undecided[:50],
            "undecided_count": len(undecided),
            "smallest_lower_bound_before": min_lower, "at_n": min_at,
            "statement_established": bool(first_neg is not None and not undecided)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tag", required=True)
    ap.add_argument("--c", type=int, required=True)
    ap.add_argument("--log2N", type=int, required=True)
    ap.add_argument("--prec", type=int, required=True)
    ap.add_argument("--rho", default="999954/1000000")
    ap.add_argument("--n-max", type=int, default=500_000)
    a = ap.parse_args()
    N, prec, rho_q = 2 ** a.log2N, a.prec, Q(a.rho)
    t_start = time.time()
    out = {"tag": a.tag, "c": a.c, "N": N, "prec": prec, "rho": str(rho_q),
           "n_max": a.n_max, "started": time.strftime("%Y-%m-%dT%H:%M:%S")}
    gates()
    log("controls")
    out["controls"] = controls(a.c, N)
    log(f"controls ok = {out['controls']['ok']}")
    if not out["controls"]["ok"]:
        raise SystemExit("a control failed: the run is void")
    with prec_guard(prec):
        r = (1 - 1 / q_arb(a.c)).sqrt()
        rho = q_arb(rho_q)
        assert r < rho
    adm = json.load(open(os.path.join(ART, "admissibility.json")))
    assert float(rho_q) < adm["radius"]["R_a_lower"] - 1e-9
    t0 = time.time()
    bm = bound_M(rho, 128)
    out["M"] = {"M_upper": bm["M_upper"], "closure_contains_0": bm["closure_contains_0"],
                "seconds": round(time.time() - t0, 1)}
    log(f"M(rho) <= {bm['M_upper']}")
    t0 = time.time()
    evaluated = evaluate_with_checkpoints(r, N, prec, a.tag)
    out["seconds_evaluation"] = round(time.time() - t0, 1)
    log("tracking, DFT, extraction")
    res = li_balls(DHModel(), r, N, a.n_max, prec, rho, bm["M_upper"], evaluated=evaluated)
    lam, out["stats"] = res["lambda"], res["stats"]
    del evaluated
    out["decision"] = decide(lam)
    log(json.dumps(out["decision"]))
    big = os.path.join(ART, "big")
    os.makedirs(big, exist_ok=True)
    path = os.path.join(big, f"lambda_{a.tag}.txt")
    h = hashlib.sha256()
    with open(path, "w") as fh, prec_guard(prec):
        for i, x in enumerate(lam):
            line = f"{i + 1} {x.str(30, radius=True)}\n"
            fh.write(line)
            h.update(line.encode())
    out["table"] = {"path": os.path.relpath(path, HERE), "sha256": h.hexdigest(),
                    "bytes": os.path.getsize(path)}
    n_star = out["decision"]["first_ball_negative_n"]
    with prec_guard(prec):
        if n_star:
            out["near_n_star"] = {str(n): lam[n - 1].str(30, radius=True)
                                  for n in range(max(1, n_star - 5), min(a.n_max, n_star + 5) + 1)}
        out["samples"] = {str(n): lam[n - 1].str(30, radius=True)
                          for n in (1, 2, 10, 100, 1000, 5000, 10000, 100000, 300000, a.n_max)
                          if n <= a.n_max}
    out["seconds_total"] = round(time.time() - t_start, 1)
    out["finished"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    with open(os.path.join(ART, f"production_{a.tag}.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    log(f"done in {out['seconds_total']} s")


if __name__ == "__main__":
    main()
