"""assembler/: compose the error bound epsilon on each stored build of R_S,
then count the negatives of the stored R_S by exact inertia.

PREREG.md fixes everything this file does (the composition, the count, the
decision rule and the wording). Read it first. In brief:

  R_ex(c, N)  the Galerkin compression of R_S = Q - T_inf - Delta_T, as the
              construction defines them, to span{U_n : |n| <= N};
  RL(b)       the stored float64 matrix of build b = (c, N, nvec, S), formed as
              checker/run_checker_inertia.stored_R forms it, lower triangle
              mirrored, every entry the exact dyadic rational it is;
  eps(b)      an upper bound on ||R_ex - RL(b)|| (spectral norm), an exact
              rational: eps_trunc + eps_quad (bound folders, JSON eps_upper)
              plus the Q and T_inf terms and the float64 roundings (here).

By Weyl, lambda_k(RL) - eps <= lambda_k(R_ex) <= lambda_k(RL) + eps, so
  L(b) = n_-(RL + eps I) <= n_-(R_ex) <= n_-(RL - eps I) = U(b),
both counted exactly by checker/'s two rational routes (LDL^T and
charpoly + Descartes, imported read-only). The same on the C4 class V_4 by
checker/'s ball elimination, with the class basis written here for any c.

    PYTHONPATH=<worktree root> <venv python> .../assemble.py --synthetic
    PYTHONPATH=<worktree root> <venv python> .../assemble.py --routed
"""

from __future__ import annotations

import argparse
import contextlib
import functools
import hashlib
import json
import math
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
C4S2 = os.path.dirname(HERE)
CHECKER = os.path.join(C4S2, "checker")
KERNEL = os.path.join(C4S2, "kernel")
TWO_ADIC = os.path.join(C4S2, "two_adic")
OUT_DIR = os.path.join(C4S2, "delta_t_bound")
if CHECKER not in sys.path:
    sys.path.insert(0, CHECKER)

import numpy as np  # noqa: E402
from flint import arb, arb_mat, fmpq  # noqa: E402
from mpmath import mp  # noqa: E402

import checker_q as CQ  # noqa: E402
import run_checker_inertia as RI  # noqa: E402
import run_checker_ts as RT  # noqa: E402

CELLS = ("2.2", "2.5", "2.9")
C_EXACT = {"2.2": fmpq(11, 5), "2.5": fmpq(5, 2), "2.9": fmpq(29, 10)}
NS = (8, 16, 32)
# (nvec, S, N): every stored build (BRIEF.md "Stored builds"), the same at each cell
BUILDS = [
    (80, 1200, 8),
    (80, 1200, 16), (80, 1600, 16), (120, 1200, 16), (120, 1600, 16), (160, 1600, 16),
    (200, 2400, 32), (240, 2400, 32), (280, 2266, 32), (319, 2633, 32), (364, 3060, 32),
]
DELIVERED = {8: (80, 1200), 16: (120, 1600), 32: (200, 2400)}
DIGEST = RI.DIGEST  # the snapshot this recount reads (checker/ s7.8, s7.9)

# PREREG (a): the stated sizes of the Q and T_inf errors before float64
# rounding, per entry; spectral norm <= (2N + 1) * entry bound.
E_Q_ENTRY = fmpq(4, 10 ** 39)  # checker/ RESULTS s1: CCM entrywise <= 5.5e-40, pinned at 4e-39; dps drift 3.9e-41
E_TINF_ENTRY = fmpq(1, 10 ** 29)  # kernel/ RESULTS s2: weakest route agreement 1e-30 (kernel), times 2L max|K| < 4.4 < 10
U53 = fmpq(1, 2 ** 53)  # binary64 round to nearest: |fl(x) - x| <= 2^-53 |fl(x)|
DELTA = fmpq(1, 10 ** 9)  # PREREG (b): robustness offset, reported only
BALL_PRECS = RI.BALL_PRECS
CODIM_V4 = RI.CODIM_V4

TRUNC_JSON = os.path.join(C4S2, "bound_trunc", "eps_trunc.json")
QUAD_JSON = os.path.join(C4S2, "bound_quad", "eps_quad.json")
SYNTH_JSON = os.path.join(HERE, "synthetic.json")
ROUTED_JSON = os.path.join(OUT_DIR, "delta_t_bound.json")


def build_key(c, nv, S, N) -> str:
    return f"{c}|{int(nv)}|{int(S)}|{int(N)}"


def cell_str(c) -> str:
    """'2.9' for 2.9, '2.9', '2.90' or 29/10: the cell as the snapshot keys it."""
    return "%.1f" % float(c)


def kmax(nv: int) -> int:
    """two_adic.ta_prolate.kmax_for, imported read-only."""
    if TWO_ADIC not in sys.path:
        sys.path.insert(0, TWO_ADIC)
    import ta_prolate as TP

    return int(TP.kmax_for(int(nv)))


# ------------------------------------------------------------ exact helpers


def q_pair(x: fmpq) -> list:
    return [int(x.p), int(x.q)]


def dec_to_q(s) -> fmpq:
    """A decimal string as the exact rational it names (fractions.Fraction)."""
    if isinstance(s, bool) or not isinstance(s, (str, int)):
        raise TypeError(f"eps_upper must be a decimal string, got {type(s).__name__} {s!r}")
    f = Fraction(str(s).strip())
    if f < 0:
        raise ValueError(f"eps_upper {s!r} is negative")
    return fmpq(f.numerator, f.denominator)


def mpf_to_q(x) -> fmpq:
    """An mpmath mpf as the exact binary rational it is, read from its raw
    (sign, man, exp, bc) tuple (no conversion at the ambient precision;
    ``man_exp`` drops the sign, so it is not used)."""
    sign, man, exp, bc = x._mpf_
    man, exp = int(man), int(exp)
    if man == 0:
        if exp != 0 or bc != 0:
            raise ValueError(f"not a finite number: {x!r}")
        return fmpq(0)
    man = -man if sign else man
    return fmpq(man * 2 ** exp) if exp >= 0 else fmpq(man, 2 ** (-exp))


def sqrt_up(s: fmpq) -> fmpq:
    """A rational r >= sqrt(s), s >= 0 rational, with r - sqrt(s) <= 1/q."""
    p, q = int(s.p), int(s.q)
    if p < 0:
        raise ValueError("negative")
    r = math.isqrt(p * q)
    if r * r != p * q:
        r += 1
    return fmpq(r, q)


def frob_up(rows) -> fmpq:
    """Upper bound on the Frobenius norm (so on the spectral norm) of a
    matrix given as rows of fmpq."""
    s = fmpq(0)
    for row in rows:
        for x in row:
            s += x * x
    return sqrt_up(s)


# ----------------------------------------------------------- the matrices


@functools.lru_cache(maxsize=None)
def q_full(c: str):
    """checker/'s Q at N = 32, dps 40 (mpmath), as run_checker_inertia uses it."""
    return CQ.Q_matrix(c, 32, 40)


def q_mp(c: str, N: int):
    Qf = q_full(c)
    return CQ.central_block(Qf, N) if N < 32 else Qf


@functools.lru_cache(maxsize=None)
def load_snapshot():
    with open(RT.SNAP) as fh:
        snap = json.load(fh)
    if snap["meta"]["ts_inputs_digest"] != DIGEST:
        raise SystemExit(f"refused: snapshot digest {snap['meta']['ts_inputs_digest'][:12]} != {DIGEST[:12]}")
    return snap


def ts_stored(c: str, nv, S, N):
    return np.array(load_snapshot()["T_S"][RT.unit_key(c, N, 40, nv, S)])


def stored_R(c: str, nv, S, N):
    """R = Q - T_S in float64, exactly as run_checker_inertia.stored_R forms it
    (which hardcodes c = 2.9; this is the same lines with c a parameter)."""
    Q = RT.to_np(q_mp(c, N)).real
    return Q - ts_stored(c, nv, S, N)


@functools.lru_cache(maxsize=None)
def t_inf_mp(c: str, N: int):
    """kernel/'s T_inf at dps 40 as mpmath, composed exactly as
    two_adic/ta_ts.KernelProvider.T_inf_matrix composes it before float()."""
    if KERNEL not in sys.path:
        sys.path.insert(0, KERNEL)
    import sonin

    with open(os.path.join(KERNEL, "cells_dps40.json")) as fh:
        m = json.load(fh)["moments"][c]
    with mp.workdps(40):
        s = [mp.mpf(a) + mp.mpf(b) for a, b in zip(m["A_even"]["s"], m["E_even"]["s"])][: N + 1]
        d = [mp.mpf(a) + mp.mpf(b) for a, b in zip(m["A_even"]["d"], m["E_even"]["d"])][: N + 1]
        return sonin.form_from_moments(s, d, N)


def t_inf_float(c: str, N: int):
    T = t_inf_mp(c, N)
    n = 2 * N + 1
    return np.array([[float(T[i, j]) for j in range(n)] for i in range(n)])


# --------------------------------------------------- (a) the fixed terms


def fixed_terms(c: str, nv, S, N) -> dict:
    """PREREG (a): everything in eps(b) that is not eps_trunc or eps_quad, each
    an exact rational upper bound on a spectral norm."""
    n = 2 * N + 1
    Qm = q_mp(c, N)
    Qf = RT.to_np(Qm).real
    Tm = t_inf_mp(c, N)
    Tf = t_inf_float(c, N)
    TS = ts_stored(c, nv, S, N)
    R = Qf - TS
    RL = RI.lower_mirrored(R)
    imag = max(abs(complex(Qm[i, j]).imag) for i in range(n) for j in range(n))
    if imag != 0.0:
        raise ArithmeticError(f"Q has an imaginary part {imag}; PREREG (a) assumes a real Q")
    terms = {
        "e_Q": n * E_Q_ENTRY,
        "e_Tinf": n * E_TINF_ENTRY,
        "r_Q": frob_up([[mpf_to_q(Qm[i, j]) - RI.to_q(Qf[i, j]) for j in range(n)] for i in range(n)]),
        "r_Tinf": frob_up([[mpf_to_q(Tm[i, j]) - RI.to_q(Tf[i, j]) for j in range(n)] for i in range(n)]),
        "r_add": U53 * frob_up([[RI.to_q(x) for x in row] for row in TS]),
        "r_sub": frob_up([[RI.to_q(Qf[i, j]) - RI.to_q(TS[i, j]) - RI.to_q(R[i, j]) for j in range(n)]
                          for i in range(n)]),
        "r_mirror": frob_up([[RI.to_q(R[i, j]) - RI.to_q(RL[i, j]) for j in range(n)] for i in range(n)]),
    }
    total = fmpq(0)
    for v in terms.values():
        total += v
    terms["total"] = total
    return terms


# ------------------------------------------------ the bound folders' JSON


def load_bound(path: str) -> dict:
    """{(cell, N, nvec, S, Kmax): entry} from a bound folder's JSON (BRIEF
    interface: a list of {c, N, nvec, S, Kmax, eps_upper, grade, assumptions}).
    eps is an exact fmpq, or None where eps_upper is null."""
    with open(path) as fh:
        raw = json.load(fh)
    entries = raw["entries"] if isinstance(raw, dict) and "entries" in raw else raw
    if not isinstance(entries, list):
        raise TypeError(f"{path}: expected a list of entries")
    table = {}
    for e in entries:
        key = (cell_str(e["c"]), int(e["N"]), int(e["nvec"]), int(round(float(e["S"]))), int(e["Kmax"]))
        if key in table:
            raise ValueError(f"{path}: duplicate entry {key}")
        eu = e.get("eps_upper")
        table[key] = {"eps": None if eu is None else dec_to_q(eu), "eps_upper": eu,
                      "grade": e.get("grade"), "assumptions": e.get("assumptions"),
                      "why_null": (e.get("why") or e.get("reason")) if eu is None else None,
                      "blocking_step": e.get("blocking_step")}
    return table


def bound_for(table: dict | None, c: str, nv, S, N) -> dict:
    """The entry of one build, or a record of why there is none."""
    if table is None:
        return {"eps": None, "missing": "no bound file"}
    key = (c, int(N), int(nv), int(S), kmax(nv))
    if key not in table:
        return {"eps": None, "missing": f"no entry at {key}"}
    return table[key]


# ---------------------------------------------------------- the C4 class V_4


def class_basis_c(c_exact: fmpq, N: int, prec: int):
    """run_checker_inertia.class_basis with c a parameter (it hardcodes 29/10):
    arb enclosure of the basis Z of V_4, free coordinates |n| >= 2."""
    with RI.arb_prec(prec):
        L = arb(c_exact).log()
        pi = arb.pi()
        L2, P2 = L * L, 16 * pi * pi
        free = [n for n in range(-N, N + 1) if abs(n) >= 2]
        Z = arb_mat(2 * N + 1, len(free))
        for j, n in enumerate(free):
            r = (L2 + P2) / (L2 + P2 * n * n)  # h_n / h_1
            Z[n + N, j] = arb(1)
            Z[1 + N, j] = -(1 + n) * r / 2
            Z[-1 + N, j] = -(1 - n) * r / 2
        return Z, free


def class_constraints_c(c_exact: fmpq, N: int, prec: int):
    """The three real constraint rows of V_4 (h, n h, e_0) at c."""
    with RI.arb_prec(prec):
        L = arb(c_exact).log()
        pi = arb.pi()
        h = [1 / (L * L + 16 * pi * pi * n * n) for n in range(-N, N + 1)]
        nh = [n * h[n + N] for n in range(-N, N + 1)]
        e0 = [arb(1) if n == 0 else arb(0) for n in range(-N, N + 1)]
        return h, nh, e0


def class_inertia_c(RL, shift: fmpq, N: int, c_exact: fmpq) -> dict:
    """run_checker_inertia.class_inertia with c a parameter: In(Z^T (RL + shift I) Z)
    by ball elimination, at the first precision where every pivot excludes 0."""
    n = RL.shape[0]
    for prec in BALL_PRECS:
        with RI.arb_prec(prec):
            Z, _ = class_basis_c(c_exact, N, prec)
            A = arb_mat(n, n)
            s = arb(shift)
            for i in range(n):
                for j in range(n):
                    A[i, j] = arb(float(RL[i, j])) + (s if i == j else 0)
            M = Z.transpose() * A * Z
            m = M.nrows()
            res = RI.inertia_balls([[M[i, j] for j in range(m)] for i in range(m)])
        if res is not None:
            return {"n_minus": res[0], "n_zero": 0, "n_plus": res[2], "dim": m, "prec": prec}
    return {"n_minus": None, "undecided": True, "dim": n - CODIM_V4, "prec": BALL_PRECS[-1]}


# ------------------------------------------------------- (b) the count


def count_build(RL, eps: fmpq, c: str, N: int, v4: bool = True, robust: bool = True) -> dict:
    """L = n_-(RL + eps I), U = n_-(RL - eps I), both exact routes; on V_4 by
    balls, with the min-max fallback where the balls do not decide."""
    A = RI.exact_matrix(RL)
    lo = RI.inertia_both(RI.shifted(A, eps))
    hi = lo if eps == 0 else RI.inertia_both(RI.shifted(A, -eps))
    rec = {"eps": q_pair(eps), "eps_float": float(eps),
           "L": lo[0], "inertia_plus_eps": list(lo), "U": hi[0], "inertia_minus_eps": list(hi)}
    if robust and eps > DELTA:
        rec["L_at_eps_minus_delta"] = RI.inertia_both(RI.shifted(A, eps - DELTA))[0]
        rec["L_at_eps_plus_delta"] = RI.inertia_both(RI.shifted(A, eps + DELTA))[0]
        rec["robust_delta"] = bool(rec["L_at_eps_minus_delta"] == lo[0] == rec["L_at_eps_plus_delta"])
    if v4:
        cp = class_inertia_c(RL, eps, N, C_EXACT[c])
        cm = cp if eps == 0 else class_inertia_c(RL, -eps, N, C_EXACT[c])
        rec["V4"] = {"plus_eps": cp, "minus_eps": cm,
                     "L": cp["n_minus"] if cp["n_minus"] is not None else max(lo[0] - CODIM_V4, 0),
                     "U": cm["n_minus"] if cm["n_minus"] is not None else hi[0],
                     "L_by": "balls" if cp["n_minus"] is not None else "min-max fallback n_- - 3",
                     "U_by": "balls" if cm["n_minus"] is not None else "min-max fallback n_-"}
    return rec


# --------------------------------------------- aggregation and (c) the rule


DIMS = {"full": {N: 2 * N + 1 for N in NS}, "V4": {N: 2 * N + 1 - CODIM_V4 for N in NS}}


def aggregate(per_build: dict, space: str) -> dict:
    """PREREG (b): L*_N = max over builds with a bound, U*_N = min; then the
    interlacing of the nested spans (n_-(R_ex, N) is nondecreasing in N):
    L*_16 >= L*_8, L*_32 >= L*_16, U*_16 <= U*_32, U*_8 <= U*_16. Where no
    build of an N has a bound, L = 0 and U = dim (trivial), flagged.
    per_build: {N: [(L, U) or None per build]}."""
    raw_L, raw_U, has = {}, {}, {}
    for N in NS:
        got = [x for x in per_build.get(N, []) if x is not None]
        has[N] = bool(got)
        raw_L[N] = max((x[0] for x in got), default=0)
        raw_U[N] = min((x[1] for x in got), default=DIMS[space][N])
    L, U = dict(raw_L), dict(raw_U)
    L[16] = max(L[16], L[8])
    L[32] = max(L[32], L[16])
    U[16] = min(U[16], U[32])
    U[8] = min(U[8], U[16])
    consistent = all(L[N] <= U[N] for N in NS) and all(raw_L[N] <= raw_U[N] for N in NS)
    return {"L": L, "U": U, "raw_L": raw_L, "raw_U": raw_U, "has_bound": has, "consistent": consistent}


def decide(agg: dict) -> dict:
    """PREREG (c), fixed before any eps: the outcome at one cell and space."""
    L, U, has = agg["L"], agg["U"], agg["has_bound"]
    if not agg["consistent"]:
        return {"outcome": "inconsistent", "why": "some lower bound exceeds an upper bound: a bound or a stored matrix is wrong"}
    if not (has[16] and has[32]):
        return {"outcome": 4, "why": "no build with a finite eps at " + ", ".join(f"N = {N}" for N in (16, 32) if not has[N])}
    if L[32] > L[16]:
        return {"outcome": 1, "why": "L*_32 > L*_16", "first_step_rises": bool(L[16] > L[8])}
    if U[32] <= L[16]:
        return {"outcome": 2, "why": "L*_32 = L*_16 and U*_32 <= L*_16: n_-(R_ex) is the same at N = 16 and 32",
                "first_step": "rises" if L[16] > L[8] else ("absent" if U[16] <= L[8] else "undecided")}
    return {"outcome": 3, "why": "L*_32 = L*_16 < U*_32: growth neither shown nor excluded at eps",
            "undecided_at_32": U[32] - L[32]}


# ------------------------------------------------------------------ runs


def band(cells: dict, c: str, N: int) -> float:
    """The stored band of checker_ts_cells.json, read, never re-derived."""
    return float(cells[c][str(N)]["band"])


@functools.lru_cache(maxsize=None)
def load_cells():
    with open(RI.CELLS_JSON) as fh:
        return json.load(fh)["cells"]


def _dump(obj, path):
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(obj, fh, indent=1)
    os.replace(tmp, path)


def run_synthetic(out_path: str = SYNTH_JSON, cells=CELLS) -> dict:
    """The harness against synthetic eps (PREREG s6): per build, eps = 0, band,
    2 band as pure shifts, and band plus the fixed terms. Checkpointed per build."""
    C = load_cells()
    out = {"meta": {"kind": "synthetic", "ts_inputs_digest": DIGEST,
                    "snapshot_sha256": hashlib.sha256(open(RT.SNAP, "rb").read()).hexdigest(),
                    "python": sys.executable, "numpy": np.__version__}, "builds": {}}
    if os.path.exists(out_path):
        with open(out_path) as fh:
            old = json.load(fh)
        if old.get("meta", {}).get("ts_inputs_digest") == DIGEST:
            out["builds"] = old.get("builds", {})
    t0 = time.time()
    for c in cells:
        for nv, S, N in BUILDS:
            key = build_key(c, nv, S, N)
            if key in out["builds"]:
                continue
            t = time.time()
            R = stored_R(c, nv, S, N)
            RL = RI.lower_mirrored(R)
            beta = RI.to_q(band(C, c, N))
            fx = fixed_terms(c, nv, S, N)
            rec = {"c": c, "nvec": nv, "S": S, "N": N, "Kmax": kmax(nv),
                   "R_sha256": hashlib.sha256(np.ascontiguousarray(R).tobytes()).hexdigest(),
                   "symmetric_defect": float(np.abs(R - R.T).max()),
                   "band": band(C, c, N),
                   "fixed": {k: {"q": q_pair(v), "float": float(v)} for k, v in fx.items()},
                   "eps0": count_build(RL, fmpq(0), c, N, robust=False),
                   "band_x1": count_build(RL, beta, c, N),
                   "band_x2": count_build(RL, 2 * beta, c, N),
                   "band_x1_plus_fixed": count_build(RL, beta + fx["total"], c, N, v4=False, robust=False)}
            rec["seconds"] = round(time.time() - t, 1)
            out["builds"][key] = rec
            _dump(out, out_path)
            print(key, "eps0", rec["eps0"]["L"], "band", rec["band_x1"]["L"], rec["band_x1"]["U"],
                  "V4", rec["band_x1"]["V4"]["L"], rec["seconds"], "s", flush=True)
    out["meta"]["seconds"] = round(time.time() - t0, 1)
    out["decisions"] = synthetic_decisions(out)
    _dump(out, out_path)
    return out


def synthetic_decisions(out: dict) -> dict:
    """The rule applied to the synthetic shifts (a dry run of PREREG (c))."""
    res = {}
    for shift in ("eps0", "band_x1", "band_x2"):
        for c in CELLS:
            for space in ("full", "V4"):
                pb = {N: [] for N in NS}
                for nv, S, N in BUILDS:
                    b = out["builds"].get(build_key(c, nv, S, N))
                    if b is None:
                        continue
                    r = b[shift]
                    pb[N].append((r["L"], r["U"]) if space == "full" else (r["V4"]["L"], r["V4"]["U"]))
                agg = aggregate(pb, space)
                res[f"{shift}|{c}|{space}"] = {"agg": agg, "decision": decide(agg)}
    return res


def run_routed(out_path: str = ROUTED_JSON, trunc_path: str = TRUNC_JSON, quad_path: str = QUAD_JSON,
               builds=None) -> dict:
    """Phase 2: eps from the two bound folders, the count, the outcome.
    ``builds`` (default: all 33) restricts the run, for the planted test only."""
    trunc = load_bound(trunc_path) if os.path.exists(trunc_path) else None
    quad = load_bound(quad_path) if os.path.exists(quad_path) else None
    todo = [(c, nv, S, N) for c in CELLS for nv, S, N in BUILDS] if builds is None else list(builds)
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    out = {"meta": {"kind": "routed", "ts_inputs_digest": DIGEST,
                    "snapshot_sha256": hashlib.sha256(open(RT.SNAP, "rb").read()).hexdigest(),
                    "trunc_json_sha256": _sha(trunc_path), "quad_json_sha256": _sha(quad_path),
                    "python": sys.executable, "numpy": np.__version__}, "builds": {}}
    if os.path.exists(out_path):  # resume only on the same snapshot and the same two bound files
        with open(out_path) as fh:
            old = json.load(fh)
        same = ("ts_inputs_digest", "trunc_json_sha256", "quad_json_sha256")
        if all(old.get("meta", {}).get(k) == out["meta"][k] for k in same):
            out["builds"] = old.get("builds", {})
    t0 = time.time()
    for c, nv, S, N in todo:
        key = build_key(c, nv, S, N)
        if key in out["builds"]:
            continue
        t = time.time()
        bt, bq = bound_for(trunc, c, nv, S, N), bound_for(quad, c, nv, S, N)
        fx = fixed_terms(c, nv, S, N)
        rec = {"c": c, "nvec": nv, "S": S, "N": N, "Kmax": kmax(nv),
               "trunc": _bound_rec(bt), "quad": _bound_rec(bq),
               "fixed": {k: {"q": q_pair(v), "float": float(v)} for k, v in fx.items()}}
        if bt["eps"] is None or bq["eps"] is None:
            rec["eps"] = None
            rec["count"] = None
        else:
            eps = bt["eps"] + bq["eps"] + fx["total"]
            rec["eps"] = {"q": q_pair(eps), "float": float(eps)}
            RL = RI.lower_mirrored(stored_R(c, nv, S, N))
            rec["count"] = count_build(RL, eps, c, N)
        rec["seconds"] = round(time.time() - t, 1)
        out["builds"][key] = rec
        _dump(out, out_path)
        cnt = rec["count"]
        print(key, "eps", None if rec["eps"] is None else "%.3e" % rec["eps"]["float"],
              "L/U", None if cnt is None else (cnt["L"], cnt["U"]), rec["seconds"], "s", flush=True)
    out["decisions"] = routed_decisions(out)
    m = out["decisions"]["2.9|full"]["agg"]["L"][16]
    out["eps_grow_2.9_full"] = {"m": m, "builds": {build_key(c, nv, S, N): eps_grow(c, nv, S, N, m)
                                                    for c, nv, S, N in todo if c == "2.9" and N == 32}}
    out["meta"]["seconds"] = round(time.time() - t0, 1)
    _dump(out, out_path)
    return out


def routed_decisions(out: dict) -> dict:
    res = {}
    for c in CELLS:
        for space in ("full", "V4"):
            pb = {N: [] for N in NS}
            for nv, S, N in BUILDS:
                b = out["builds"].get(build_key(c, nv, S, N))
                cnt = None if b is None else b["count"]
                if cnt is None:
                    pb[N].append(None)
                else:
                    pb[N].append((cnt["L"], cnt["U"]) if space == "full" else (cnt["V4"]["L"], cnt["V4"]["U"]))
            agg = aggregate(pb, space)
            res[f"{c}|{space}"] = {"agg": agg, "decision": decide(agg)}
    return res


def eps_grow(c: str, nv, S, N, m: int) -> dict:
    """PREREG (b), reported only: the exact bracket [lo, hi) of lambda_{m+1}(RL)
    (run_checker_inertia.bracket, exact counts). This build alone shows more
    than m negatives below -eps for every eps < -hi, and does not for eps >= -lo."""
    R = stored_R(c, nv, S, N)
    A = RI.exact_matrix(RI.lower_mirrored(R))
    w = np.linalg.eigvalsh(R)
    b = RI.bracket(A, m + 1, w[m])
    return {"k": m + 1, "lo": q_pair(b["lo"]), "hi": q_pair(b["hi"]),
            "grows_for_eps_below": float(-b["hi"]), "no_growth_for_eps_at_least": float(-b["lo"]),
            "float_eig": float(w[m])}


def _bound_rec(b: dict) -> dict:
    r = {k: v for k, v in b.items() if k != "eps"}
    r["eps_q"] = None if b.get("eps") is None else q_pair(b["eps"])
    return r


def _sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest() if os.path.exists(path) else None


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--synthetic", action="store_true")
    ap.add_argument("--routed", action="store_true")
    ap.add_argument("--cells", default=",".join(CELLS))
    a = ap.parse_args()
    if a.synthetic:
        run_synthetic(cells=tuple(a.cells.split(",")))
    if a.routed:
        run_routed()
