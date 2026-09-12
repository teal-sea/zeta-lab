#!/usr/bin/env python3
"""Ceiling procedure on the *lower* side of Erdos's minimum overlap constant.

The upper side of this constant has been fought over by four systems in a
year. The lower side is a convex program that has moved twice since 1959, and
its author wrote down a guess about his own method's limit without measuring
it. This probe measures it.

Fronts
------
A  `--front simplified` : White's section 4 linear program, swept in `N` and
   `R`. White reports `0.375169005340707` at `N,R = 80000,20` and asserts
   "the limit of this approach is less than 0.3755" without a sweep. This
   front is the sweep.

B  `--front full` : White's section 5 program (the one that produces the
   published `0.379005`), swept in `N`, `T` and `R` at his own binding box
   cell. `R` is the parameter he never varied in this program: it is 10 in
   every table.

C  `--front box` : the same program over a grid of `(h, p, q)` cells covering
   his residual region, which is where the published number is a *minimum*
   rather than a single solve.

D  `--front certificate` : an exact rational dual-feasible point for the
   section 4 program, with every irrational coefficient replaced by a
   directed-rounded rational in the direction that can only weaken the bound.
   No floating point survives into the reported value.

E  `--front guard` : planted faults in this probe's own program builder, and
   which of them the checker catches.

Grades used in RESULTS.md: VERIFIED = exact arithmetic or exhaustive
enumeration; MEASURED = one floating-point route; INFERRED = from the
literature or argued rather than computed here.
"""

from __future__ import annotations

import argparse
import json
import math
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))

import program  # noqa: E402

BINDING_BOX = program.Box(h1=0.015, h2=0.015, p1=0.381, p2=0.381, q1=-0.02, q2=0.02)


# ---------------------------------------------------------------------------
# front A -- the section 4 simplified linear program
# ---------------------------------------------------------------------------


def front_simplified(ns: list[int], rs: list[int]) -> dict:
    rows = []
    for R in rs:
        for N in ns:
            t0 = time.time()
            out = program.simplified_lp(N, R)
            out["seconds"] = round(time.time() - t0, 2)
            rows.append(out)
            print(f"  simplified N={N} R={R} -> {out['value']} ({out['seconds']}s)",
                  flush=True)
    return {"rows": rows, "white_reference": {"N": 80000, "R": 20,
                                              "value": 0.375169005340707}}


# ---------------------------------------------------------------------------
# front B -- the section 5 program
# ---------------------------------------------------------------------------


def _solve_full(N: int, T: int, R: int, box: program.Box, rounds: int,
                sine_factor: float = 4.0) -> dict:
    t0 = time.time()
    prog = program.WhiteProgram(N, T, R, box, sine_factor=sine_factor)
    res = prog.solve(cut_rounds=rounds)
    return {
        "N": N,
        "T": T,
        "R": R,
        "sine_factor": sine_factor,
        "value": res["value"],
        "status": res["status"],
        "cut_rounds": len(res["trace"]),
        "cuts": res["cuts"],
        "converged": res.get("converged"),
        "final_residual": (res.get("residuals") or [None])[-1],
        "seconds": round(time.time() - t0, 2),
    }


def front_full(sweep: list[tuple[int, int, int]], rounds: int,
               out_path: str | None = None) -> dict:
    """Sweep the section 5 program, writing after every point.

    Writing incrementally is not tidiness: the large end of this sweep is
    minutes per point and the budget that kills a run kills it mid-sweep, so
    a run that only writes at the end reports nothing at all.
    """
    rows = []
    payload = {"rows": rows, "box": vars(BINDING_BOX),
               "white_reference": {"N": 25000, "T": 7000, "R": 10,
                                   "value": 0.37905}}
    for N, T, R in sweep:
        out = _solve_full(N, T, R, BINDING_BOX, rounds)
        rows.append(out)
        print(f"  full N={N} T={T} R={R} -> {out['value']} "
              f"conv={out['converged']} ({out['seconds']}s)", flush=True)
        if out_path:
            Path(out_path).write_text(json.dumps(payload, indent=2, sort_keys=True),
                                      encoding="utf-8")
    return payload


def front_sine_factor(N: int, T: int, R: int, rounds: int) -> dict:
    """The 4-vs-8 discrepancy in White's displayed (5.6)/(5.7), as a number."""
    rows = [_solve_full(N, T, R, BINDING_BOX, rounds, sine_factor=s)
            for s in (4.0, 8.0)]
    for r in rows:
        print(f"  sine_factor={r['sine_factor']} -> {r['value']}", flush=True)
    return {"rows": rows}


# ---------------------------------------------------------------------------
# front C -- the box grid
# ---------------------------------------------------------------------------


def front_box(N: int, T: int, R: int, rounds: int, nh: int, npp: int) -> dict:
    """White's residual region (5.16): 0 <= E(M) <= 0.06, 0.35 <= c_1 <= 0.45.

    A *grid of cells* is a covering; White's tables use degenerate points and
    lean on his Lemma 10 to spread each certificate over an ellipse. This
    front does the plain thing instead, so the minimum over the grid is a
    bound for the whole region without any reuse argument.
    """
    h_edges = np.linspace(0.0, 0.06, nh + 1)
    p_edges = np.linspace(0.35, 0.45, npp + 1)
    rows = []
    for a, b in zip(h_edges[:-1], h_edges[1:]):
        for c, d in zip(p_edges[:-1], p_edges[1:]):
            box = program.Box(h1=float(a), h2=float(b), p1=float(c), p2=float(d),
                              q1=-0.02, q2=0.02)
            t0 = time.time()
            prog = program.WhiteProgram(N, T, R, box)
            res = prog.solve(cut_rounds=rounds)
            rows.append({"h": [float(a), float(b)], "p": [float(c), float(d)],
                         "value": res["value"], "seconds": round(time.time() - t0, 2)})
            print(f"  box h={a:.3f}-{b:.3f} p={c:.3f}-{d:.3f} -> {res['value']}",
                  flush=True)
    vals = [r["value"] for r in rows if r["value"] is not None]
    return {"rows": rows, "N": N, "T": T, "R": R,
            "min_over_grid": min(vals) if vals else None}


# ---------------------------------------------------------------------------
# front D -- exact rational dual certificate for the section 4 program
# ---------------------------------------------------------------------------


def _alpha_minus_rational(N: int, m: int, j: int, denom: int) -> Fraction:
    """A rational lower bound on White's `alpha^-_{j,2m}`.

    `alpha^-` multiplies `w_j >= 0` on the left of a `<= 0` constraint, so
    lowering it can only *enlarge* the primal feasible set. Rounding down is
    therefore the safe direction, and it is the only place an irrational
    enters the section 4 program.
    """
    L = Fraction(2, N)
    exact = math.cos(math.pi * (2 * m) * float(L) * (j - 0.5) / 2.0)
    lipschitz = Fraction(math.pi.as_integer_ratio()[0], math.pi.as_integer_ratio()[1])
    # cos is computed in float; drop 1 ulp-scale slack plus the Lipschitz term,
    # both downward, so the result is provably <= the real alpha^-.
    floor_cos = Fraction(math.floor(exact * denom) - 1, denom)
    return floor_cos - (lipschitz * (2 * m) * L) / 4


def front_certificate(N: int, R: int, denom: int) -> dict:
    """Exact rational dual-feasible point for White (4.1)-(4.4).

    Dual of `min Omega  s.t.  w_j - Omega <= 0`, `sum_m a_{m,j} w_j <= 0`,
    `L^3 sum (j-1)^2 w_j <= 1/3`, `sum w_j = N/4`, `w >= 0`:

        maximize   (N/4) lam - z/3
        subject to sum_j y_j <= 1
                   lam <= y_j + sum_m a_{m,j} u_m + s_j z    for all j
                   y, u, z >= 0,  lam free.

    Given any `u, z >= 0`, put `theta_j = sum_m a_{m,j} u_m + s_j z` and
    `y_j = max(0, lam - theta_j)`. The dual is then feasible exactly when
    `sum_j max(0, lam - theta_j) <= 1`, and the largest such `lam` is found
    exactly by sorting `theta`. So the float solver is used only to *propose*
    `(u, z)`; the value returned below is computed from that proposal in
    `fractions.Fraction` with no floating point in it.
    """
    from scipy import sparse
    from scipy.optimize import linprog

    L = 2.0 / N
    j = np.arange(1, N + 1, dtype=float)
    nv = N + 1
    rows, rhs = [], []
    for m in range(1, R + 1):
        mm = 2 * m
        r = np.zeros(nv)
        r[1:] = np.cos(math.pi * mm * L * (j - 0.5) / 2.0) - math.pi * mm * L / 4.0
        rows.append(r)
        rhs.append(0.0)
    r = np.zeros(nv)
    r[1:] = (L**3) * (j - 1.0) ** 2
    rows.append(r)
    rhs.append(1.0 / 3.0)
    idx = np.arange(N)
    omega_block = sparse.coo_matrix(
        (np.concatenate([np.ones(N), -np.ones(N)]),
         (np.concatenate([idx, idx]),
          np.concatenate([1 + idx, np.zeros(N, dtype=int)]))),
        shape=(N, nv))
    A = sparse.vstack([omega_block, sparse.csr_matrix(np.array(rows))]).tocsc()
    b = np.concatenate([np.zeros(N), np.array(rhs)])
    eq = np.zeros(nv)
    eq[1:] = 1.0
    obj = np.zeros(nv)
    obj[0] = 1.0
    res = linprog(obj, A_ub=A, b_ub=b, A_eq=sparse.csr_matrix(eq.reshape(1, -1)),
                  b_eq=np.array([N / 4.0]), bounds=[(0.0, 1.0)] + [(0.0, None)] * N,
                  method="highs-ipm")
    if not res.success:
        return {"N": N, "R": R, "status": res.message}
    float_value = float(res.fun)
    marg = res.ineqlin.marginals
    u_float = np.maximum(0.0, -marg[N : N + R])
    z_float = max(0.0, -marg[N + R])

    # -- everything below is exact ----------------------------------------
    u = [Fraction(int(round(v * denom)), denom) for v in u_float]
    z = Fraction(int(round(z_float * denom)), denom)
    Lf = Fraction(2, N)
    theta = []
    for jj in range(1, N + 1):
        acc = Fraction(0)
        for m in range(1, R + 1):
            if u[m - 1] != 0:
                acc += _alpha_minus_rational(N, m, jj, denom) * u[m - 1]
        acc += (Lf**3) * (jj - 1) ** 2 * z
        theta.append(acc)
    order = sorted(range(N), key=lambda i: theta[i])
    # largest lam with sum_j max(0, lam - theta_j) <= 1
    best_lam = Fraction(min(theta))
    running = Fraction(0)
    for k in range(1, N + 1):
        i = order[k - 1]
        if k > 1:
            running += (theta[i] - theta[order[k - 2]]) * (k - 1)
        if running > 1:
            break
        remaining = Fraction(1) - running
        cand = theta[i] + remaining / k
        upper = theta[order[k]] if k < N else None
        if upper is None or cand <= upper:
            best_lam = cand
            break
        best_lam = upper
    check = sum((best_lam - t for t in theta if t < best_lam), Fraction(0))
    value = Fraction(N, 4) * best_lam - z / 3
    return {
        "N": N,
        "R": R,
        "denom": denom,
        "float_lp_value": float_value,
        "exact_value_num": int(value.numerator),
        "exact_value_den": int(value.denominator),
        "exact_value_float": float(value),
        "dual_feasible": bool(check <= 1),
        "sum_y_num": int(check.numerator),
        "sum_y_den": int(check.denominator),
        "gap_to_float_lp": float(value) - float_value,
    }


# ---------------------------------------------------------------------------
# front E -- planted faults
# ---------------------------------------------------------------------------


def front_guard(N: int, R: int) -> dict:
    """Faults planted in the section 4 builder, and whether a check catches them.

    The check available without a second implementation is *monotonicity in
    the parameters*: the section 4 optimum is provably non-decreasing in both
    `N` (a cell splits into two feasible cells) and `R` (a constraint is
    added). A builder defect that drops or mis-strides constraints breaks
    monotonicity in `R`; one that mis-scales the grid breaks it in `N`.
    """
    from scipy import sparse
    from scipy.optimize import linprog

    def value(N_: int, R_: int, fault: str) -> float | None:
        L = 2.0 / N_
        j = np.arange(1, N_ + 1, dtype=float)
        nv = N_ + 1
        rows, rhs = [], []
        ms = range(1, R_ + 1)
        if fault == "every_other_mode":
            ms = range(1, R_ + 1, 2)
        for m in ms:
            mm = 2 * m
            if fault == "odd_modes":  # constrain cos(pi m x) with m odd: not (2.4)
                mm = 2 * m - 1
            width = math.pi * mm * L / 4.0
            if fault == "no_envelope":
                width = 0.0
            r = np.zeros(nv)
            r[1:] = np.cos(math.pi * mm * L * (j - 0.5) / 2.0) - width
            rows.append(r)
            rhs.append(0.0)
        r = np.zeros(nv)
        r[1:] = (L**3) * (j - 1.0) ** 2
        rows.append(r)
        rhs.append(1.0 / 3.0)
        idx = np.arange(N_)
        omega = sparse.coo_matrix(
            (np.concatenate([np.ones(N_), -np.ones(N_)]),
             (np.concatenate([idx, idx]),
              np.concatenate([1 + idx, np.zeros(N_, dtype=int)]))),
            shape=(N_, nv))
        A = sparse.vstack([omega, sparse.csr_matrix(np.array(rows))]).tocsc()
        b = np.concatenate([np.zeros(N_), np.array(rhs)])
        eq = np.zeros(nv)
        eq[1:] = 1.0
        obj = np.zeros(nv)
        obj[0] = 1.0
        res = linprog(obj, A_ub=A, b_ub=b,
                      A_eq=sparse.csr_matrix(eq.reshape(1, -1)),
                      b_eq=np.array([N_ / 4.0]),
                      bounds=[(0.0, 1.0)] + [(0.0, None)] * N_, method="highs-ipm")
        return float(res.fun) if res.success else None

    out = []
    for fault in ("none", "no_envelope", "every_other_mode", "odd_modes"):
        vals = {}
        for R_ in (R, 2 * R):
            for N_ in (N, 2 * N):
                vals[f"N{N_}_R{R_}"] = value(N_, R_, fault)
        mono_R = (vals[f"N{N}_R{2*R}"] is not None
                  and vals[f"N{N}_R{R}"] is not None
                  and vals[f"N{N}_R{2*R}"] >= vals[f"N{N}_R{R}"] - 1e-9)
        mono_N = (vals[f"N{2*N}_R{R}"] is not None
                  and vals[f"N{N}_R{R}"] is not None
                  and vals[f"N{2*N}_R{R}"] >= vals[f"N{N}_R{R}"] - 1e-9)
        out.append({"fault": fault, "values": vals,
                    "monotone_in_R": mono_R, "monotone_in_N": mono_N})
        print(f"  guard {fault}: monoR={mono_R} monoN={mono_N} "
              f"v={vals[f'N{N}_R{R}']}", flush=True)

    # The direction test, which is the one that matters. A fault that lowers
    # the value is merely wasteful; a fault that raises it manufactures a
    # bound that is not there. `no_envelope` is deliberately of the second
    # kind, so the table records which check sees it.
    sound = out[0]["values"][f"N{N}_R{R}"]
    for row in out[1:]:
        v = row["values"][f"N{N}_R{R}"]
        row["delta_vs_sound"] = None if v is None else v - sound
        row["unsafe_direction"] = bool(v is not None and v > sound + 1e-9)
        row["caught_by_monotonicity"] = not (row["monotone_in_R"]
                                             and row["monotone_in_N"])
    return {"rows": out, "sound_value": sound}


# ---------------------------------------------------------------------------


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--front", required=True,
                    choices=["simplified", "full", "box", "certificate", "guard",
                             "sine", "quick"])
    ap.add_argument("--out", default=None)
    ap.add_argument("--rounds", type=int, default=30)
    ap.add_argument("--ns", default="")
    ap.add_argument("--rs", default="")
    ap.add_argument("--sweep", default="")
    ap.add_argument("--N", type=int, default=4000)
    ap.add_argument("--T", type=int, default=1000)
    ap.add_argument("--R", type=int, default=10)
    ap.add_argument("--denom", type=int, default=10**7)
    ap.add_argument("--nh", type=int, default=3)
    ap.add_argument("--np", dest="npp", type=int, default=4)
    args = ap.parse_args()

    t0 = time.time()
    if args.front == "quick":
        payload = {
            "simplified": front_simplified([200, 400], [5]),
            "full": front_full([(200, 100, 5), (400, 200, 5)], args.rounds),
        }
    elif args.front == "simplified":
        ns = [int(x) for x in args.ns.split(",")] if args.ns else [1000, 5000, 20000]
        rs = [int(x) for x in args.rs.split(",")] if args.rs else [10, 20]
        payload = front_simplified(ns, rs)
    elif args.front == "full":
        sweep = ([tuple(int(v) for v in s.split(":")) for s in args.sweep.split(",")]
                 if args.sweep else [(500, 300, 10), (1000, 300, 10), (2000, 300, 10)])
        payload = front_full(sweep, args.rounds, args.out)
    elif args.front == "sine":
        payload = front_sine_factor(args.N, args.T, args.R, args.rounds)
    elif args.front == "box":
        payload = front_box(args.N, args.T, args.R, args.rounds, args.nh, args.npp)
    elif args.front == "certificate":
        payload = front_certificate(args.N, args.R, args.denom)
    else:
        payload = front_guard(args.N, args.R)

    payload["front"] = args.front
    payload["seconds_total"] = round(time.time() - t0, 2)
    payload["environment"] = {
        "python": platform.python_version(),
        "numpy": np.__version__,
        "platform": platform.system(),
    }
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.out:
        Path(args.out).write_text(text, encoding="utf-8")
        print(f"wrote {args.out} in {payload['seconds_total']}s")
    else:
        print(text)


if __name__ == "__main__":
    main()
