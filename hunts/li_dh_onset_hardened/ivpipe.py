"""Run B again with the independent evaluator: every value of f and log G from
mpmath.iv (``iv_fast.py``), none from Arb.

What is shared with run B and what is not:
- **Not shared:** every evaluation of f, log G and S(3/2). That covers the node
  samples, the arc balls of the branch cover, and the arc cover and principal
  bound behind M(rho). All of them go through ``iv_fast``/``iv_route``
  (mpmath.iv Euler-Maclaurin with its own kappa solve, and ``mpmath.iv.loggamma``).
- **Shared, deliberately (the brief says "run the same DFT"):** the node
  geometry (Arb balls around r e^{2 pi i k/N}, converted outward to iv boxes),
  the tracking logic, ``acb.dft``, the aliasing bound arithmetic and the
  decision code.  Arb is used here only to hold and transform numbers, never to
  evaluate f or Gamma.

Conversions are exact and outward: an Arb ball becomes the iv box with
endpoints mid -/+ rad (exact rationals, rounded outward by iv); an iv box becomes
the Arb ball centred at its exact midpoint with radius half its width plus the
rounding of the midpoint.

Phase 1 evaluates the N/2 + 1 upper nodes in ``--procs`` processes, in chunks
checkpointed exactly to the cache directory.  Phase 2 is one process: the
M(rho) cover, tracking, DFT, decision, the comparison with run B, and the
table written to the cache with its SHA-256.

Usage:
  .venv/bin/python hunts/li_dh_onset_hardened/ivpipe.py --procs 4
Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing as mproc
import os
import pickle
import random
import sys
import time
from fractions import Fraction as Q

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import acb, arb  # noqa: E402  (containers only, never evaluators here)
from mpmath import iv  # noqa: E402

import iv_fast  # noqa: E402
from balls import HERE, prec_guard, q_arb  # noqa: E402
from iv_route import _ivprec, _q, bounds  # noqa: E402
from iv_route import hurwitz as hurwitz_iv  # noqa: E402
from production import _pack, _unpack, decide, gates  # noqa: E402
from trapezoid import (SIGMA_P, bound_M, li_balls, node, s_of)  # noqa: E402

ART = os.path.join(HERE, "artifacts")
CACHE = os.path.join(os.environ.get("ZETA_LAB_CACHE",
                                    os.path.expanduser("~/.cache/zeta-lab")),
                     "li_dh_onset_hardened")
C_RUN, LOG2N, PREC, RHO = 2500, 19, 256, Q(999954, 1000000)
CHUNK = 4096

#: Pre-registered (committed before the run): the comparison sample.
SAMPLE_SEED = 1512026
SAMPLE_SIZE = 1000


def sample_indices() -> list[int]:
    return sorted(random.Random(SAMPLE_SEED).sample(range(1, 500_001), SAMPLE_SIZE))


def log(msg: str) -> None:
    print(time.strftime("%H:%M:%S"), msg, flush=True)


# ---------------------------------------------------------------------------
# exact conversions
# ---------------------------------------------------------------------------

def _arb_q(x: arb) -> Q:
    m, e = x.man_exp()
    return Q(int(m)) * Q(2) ** int(e)


def _iv_hull(lo: Q, hi: Q):
    a, b = _q(lo), _q(hi)
    return iv.mpf([a.a, b.b])


def to_iv(z: acb):
    """The iv box containing the Arb ball z (call inside an _ivprec block)."""
    out = []
    for x in (z.real, z.imag):
        m, r = _arb_q(x.mid()), _arb_q(x.rad())
        out.append(_iv_hull(m - r, m + r))
    return iv.mpc(out[0], out[1])


def to_arb(w) -> acb:
    """The Arb ball containing the iv box w (call inside a prec_guard)."""
    lo_r, hi_r, lo_i, hi_i = bounds(w)
    parts = []
    for lo, hi in ((lo_r, hi_r), (lo_i, hi_i)):
        m = q_arb((lo + hi) / 2)
        rad = q_arb((hi - lo) / 2)
        parts.append(arb(m.mid(), arb(rad.upper()) + arb(m.rad())))
    return acb(parts[0], parts[1])


# ---------------------------------------------------------------------------
# the model: same interface as trapezoid.DHModel, every evaluation in iv
# ---------------------------------------------------------------------------

class IVModel:
    name = "dh_iv"

    def __init__(self, prec: int):
        self.C = iv_fast.Ctx(prec)
        self.prec = prec

    def L(self, s: acb, prec: int) -> acb:
        with _ivprec(self.prec):
            w = iv_fast.logG_fast(to_iv(s), self.C)
        with prec_guard(prec):
            return to_arb(w)

    def h(self, s: acb, prec: int) -> acb:
        with _ivprec(self.prec):
            w = iv_fast.f_fast(to_iv(s), self.C)
        with prec_guard(prec):
            return to_arb(w)

    def principal(self, s: acb) -> bool:
        return bool(s.real > q_arb(SIGMA_P))

    def principal_bound(self, prec: int) -> arb:
        """|Log f| <= -log(1 - S) + arcsin S on Re s >= 3/2, with S = S(3/2) in iv."""
        with _ivprec(self.prec):
            sg = iv.mpc(_q(SIGMA_P), 0)
            z = lambda a: hurwitz_iv(sg, a, self.prec).real
            k = self.C.kappa
            S = iv.exp(-_q(SIGMA_P) * iv.log(5)) * (
                z(Q(6, 5)) + k * (z(Q(2, 5)) + z(Q(3, 5))) + z(Q(4, 5)))
            if not S.b < 1:
                raise RuntimeError("iv S(3/2) not below 1")
            B = -iv.log(1 - S) + iv.asin(S) if hasattr(iv, "asin") else None
            if B is None:   # mpmath.iv has no asin: arcsin S <= S / sqrt(1 - S^2)
                B = -iv.log(1 - S) + S / iv.sqrt(1 - S * S)
            up = bounds(iv.mpc(B, 0))[1]
        with prec_guard(prec):
            return arb(q_arb(up).upper())


# ---------------------------------------------------------------------------
# phase 1: the nodes, in parallel, checkpointed
# ---------------------------------------------------------------------------

_W: dict = {}


def _init(prec: int) -> None:
    _W["C"] = iv_fast.Ctx(prec)
    _W["prec"] = prec


def _chunk(args: tuple) -> tuple:
    k0, k1, N, path = args
    if os.path.exists(path):
        return (k0, "cached", 0.0)
    C, prec = _W["C"], _W["prec"]
    t0 = time.time()
    rows = []
    with prec_guard(prec):
        r = (1 - 1 / q_arb(C_RUN)).sqrt()
        for k in range(k0, k1):
            s = s_of(node(r, k, N))
            with _ivprec(prec):
                si = to_iv(s)
                f = iv_fast.f_fast(si, C)
                g = iv_fast.logG_fast(si, C)
            fb, gb = to_arb(f), to_arb(g)
            rows.append(tuple(_pack(x) for x in (fb.real, fb.imag, gb.real, gb.imag)))
    with open(path + ".tmp", "wb") as fh:
        pickle.dump(rows, fh)
    os.replace(path + ".tmp", path)
    return (k0, "done", time.time() - t0)


def phase1(N: int, procs: int) -> tuple:
    half = N // 2
    ck = os.path.join(CACHE, "ckpt_iv")
    os.makedirs(ck, exist_ok=True)
    jobs = [(k0, min(k0 + CHUNK, half + 1), N, os.path.join(ck, f"iv_{k0:08d}.pkl"))
            for k0 in range(0, half + 1, CHUNK)]
    t0 = time.time()
    with mproc.Pool(procs, initializer=_init, initargs=(PREC,)) as pool:
        for i, (k0, state, dt) in enumerate(pool.imap_unordered(_chunk, jobs)):
            if state == "done":
                log(f"chunk {k0} {dt:.0f} s ({i + 1}/{len(jobs)})")
            if i % 8 == 7:
                gates()
    log(f"phase 1 wall {time.time() - t0:.0f} s")
    L, H, P = [], [], []
    model = IVModel(PREC)
    with prec_guard(PREC):
        r = (1 - 1 / q_arb(C_RUN)).sqrt()
        for k0, k1, _, path in jobs:
            for j, row in enumerate(pickle.load(open(path, "rb"))):
                fr, fi, gr, gi = (_unpack(t) for t in row)
                H.append(acb(fr, fi))
                L.append(acb(gr, gi))
                P.append(model.principal(s_of(node(r, k0 + j, N))))
    return L, H, P, model


# ---------------------------------------------------------------------------
# phase 2 and the comparison
# ---------------------------------------------------------------------------

def compare_with_B(lam: list) -> dict:
    tabB = os.path.join(HERE, json.load(open(os.path.join(ART, "production_B.json")))
                        ["table"]["path"])
    with prec_guard(PREC):
        B = [arb(line.split(" ", 1)[1].strip()) for line in open(tabB)]
        n = min(len(B), len(lam))
        sign_disagree, both_decided = [], 0
        for i in range(n):
            a, b = lam[i], B[i]
            sa = 1 if a > 0 else (-1 if a < 0 else 0)
            sb = 1 if b > 0 else (-1 if b < 0 else 0)
            if sa and sb:
                both_decided += 1
                if sa != sb:
                    sign_disagree.append(i + 1)
        named = {str(m): {"iv": lam[m - 1].str(25, radius=True),
                          "arb_B": B[m - 1].str(25, radius=True),
                          "intersect": bool(lam[m - 1].overlaps(B[m - 1]))}
                 for m in (328996, 328997)}
        samp = sample_indices()
        miss = [m for m in samp if not lam[m - 1].overlaps(B[m - 1])]
        worst = max(float(abs(lam[m - 1].mid() - B[m - 1].mid()).mid()) for m in samp)
        all_overlap = sum(1 for i in range(n) if lam[i].overlaps(B[i]))
    return {"n_common": n, "both_signs_decided": both_decided,
            "sign_disagreements": sign_disagree[:50], "sign_disagreement_count": len(sign_disagree),
            "named": named, "sample_seed": SAMPLE_SEED, "sample_size": len(samp),
            "sample_misses": miss[:50], "sample_miss_count": len(miss),
            "sample_max_midpoint_difference": worst,
            "all_n_overlap_count": all_overlap}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--procs", type=int, default=4)
    a = ap.parse_args()
    N = 2 ** LOG2N
    t_start = time.time()
    out = {"started": time.strftime("%Y-%m-%dT%H:%M:%S"), "c": C_RUN, "N": N,
           "prec": PREC, "rho": str(RHO), "evaluator": "mpmath.iv (iv_fast.py)"}
    gates()
    L, H, P, model = phase1(N, a.procs)
    out["seconds_phase1_wall"] = round(time.time() - t_start, 1)
    with prec_guard(PREC):
        r = (1 - 1 / q_arb(C_RUN)).sqrt()
        rho = q_arb(RHO)
    t0 = time.time()
    bm = bound_M(rho, 128, model=model)
    out["M"] = {"M_upper": bm["M_upper"], "closure_contains_0": bm["closure_contains_0"],
                "stats": bm["stats"], "seconds": round(time.time() - t0, 1)}
    log(f"M(rho) <= {bm['M_upper']} (iv), {out['M']['seconds']} s")
    res = li_balls(model, r, N, 500_000, PREC, rho, bm["M_upper"], evaluated=(L, H, P))
    lam = res["lambda"]
    out["stats"] = res["stats"]
    out["decision"] = decide(lam)
    log(json.dumps(out["decision"]))
    os.makedirs(CACHE, exist_ok=True)
    path = os.path.join(CACHE, "lambda_B_iv.txt")
    h = hashlib.sha256()
    with open(path, "w") as fh, prec_guard(PREC):
        for i, x in enumerate(lam):
            line = f"{i + 1} {x.str(30, radius=True)}\n"
            fh.write(line)
            h.update(line.encode())
    out["table"] = {"path": "<cache>/li_dh_onset_hardened/lambda_B_iv.txt",
                    "sha256": h.hexdigest(), "bytes": os.path.getsize(path)}
    out["comparison_with_B"] = compare_with_B(lam)
    log(json.dumps({k: v for k, v in out["comparison_with_B"].items() if k != "named"}))
    out["seconds_total"] = round(time.time() - t_start, 1)
    out["finished"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    with open(os.path.join(ART, "production_B_iv.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    log(f"done in {out['seconds_total']} s")


if __name__ == "__main__":
    main()
