"""The rebuilt rows read as PREREG s2 to s4 fix them, after the full run (RUNS.md s11.4).

    python read_rows.py OUTDIR > rows.json      # OUTDIR: every shard's checkpoints, from the run's artifacts
    python read_rows.py OUTDIR CENTRES.json > rows.json   # also the exact centre(Delta_T) of every cell

assemble() (rebuild.py) sums the 34 shards and gives Delta_T per (c, N) in balls with eps_q; here
R_centre = Q_mp - T_inf_mp - centre(Delta_T) in exact rationals, eps = eps_q + eps_aux (+ the two
terms below, each an exact upper bound), and C_N(eps) = n_-(R_centre + eps I) by exact inertia on
the full space, on C4's class V_4 (assembler/'s basis, balls) and on H = {sum v_n = 0}. eps_t is
null, so the row is D0, D1 or D2 (PREREG s3), never D3.

Two terms PREREG s1 does not list, because they are zero in exact arithmetic, are bounded and added
to eps instead of assumed: the imaginary part of Delta_T (real by the s <-> -s symmetry; its
balls are about 1e-42) and any asymmetry of R_centre."""
from __future__ import annotations

import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
C4S2 = os.path.dirname(HERE)
for p in (HERE, os.path.join(C4S2, "assembler"), os.path.join(C4S2, "checker")):
    if p not in sys.path:
        sys.path.insert(0, p)

from flint import arb, arb_mat, fmpq  # noqa: E402
from mpmath import mp  # noqa: E402

SCALE = fmpq(118, 10 ** 4)  # PREREG s3: the record's 1.18e-2
BAND_29_32 = fmpq(82, 10 ** 4)  # PREREG s4 item 2: band(2.9, 32) = 8.2e-3


def arb_mid_q(x) -> fmpq:
    m, e = x.mid().man_exp()
    m, e = int(m), int(e)
    return fmpq(m * 2 ** e) if e >= 0 else fmpq(m, 2 ** -e)


def arb_up_q(x) -> fmpq:
    """An exact rational >= every point of the ball x (x finite)."""
    if not x.is_finite():
        raise ArithmeticError("not finite")
    return arb_mid_q(x.upper())


def h_basis(n: int) -> list:
    """Columns e_k - e_0 (k = 1 .. n-1): a rational basis of H = {sum v = 0} in Q^n."""
    return [[fmpq(1) if i == k else (fmpq(-1) if i == 0 else fmpq(0)) for i in range(n)] for k in range(1, n)]


def compress(A: list, cols: list) -> list:
    """B^T A B for B with the given columns, exactly."""
    AB = [[sum((A[i][k] * c[k] for k in range(len(c)) if c[k] != 0), fmpq(0)) for c in cols] for i in range(len(A))]
    return [[sum((c[i] * AB[i][j] for i in range(len(c)) if c[i] != 0), fmpq(0)) for j in range(len(cols))] for c in cols]


def v4_inertia(A: list, shift: fmpq, N: int, c: str) -> dict:
    """assemble.class_inertia_c on an exact rational matrix (it reads float64): In(Z^T (A + shift I) Z)
    by ball elimination at the first precision where every pivot excludes 0, else None."""
    import assemble as AS
    import run_checker_inertia as RI

    n = len(A)
    for prec in AS.BALL_PRECS:
        with RI.arb_prec(prec):
            Z, _ = AS.class_basis_c(AS.C_EXACT[c], N, prec)
            M0 = arb_mat(n, n)
            for i in range(n):
                for j in range(n):
                    M0[i, j] = arb(A[i][j] + (shift if i == j else 0))
            M = Z.transpose() * M0 * Z
            m = M.nrows()
            res = RI.inertia_balls([[M[i, j] for j in range(m)] for i in range(m)])
        if res is not None:
            return {"n_minus": res[0], "dim": m, "prec": prec}
    return {"n_minus": None, "dim": n - AS.CODIM_V4, "prec": AS.BALL_PRECS[-1]}


def counts(R: list, eps: fmpq, N: int, c: str) -> dict:
    """C_N(eps) on the three spaces, and n_-(R_centre) for context (not a PREREG count)."""
    import run_checker_inertia as RI

    n = len(R)
    full = RI.inertia_both(RI.shifted(R, eps))
    H = compress(RI.shifted(R, eps), h_basis(n))
    hin = RI.inertia_both(H)
    v4 = v4_inertia(R, eps, N, c)
    return {"full": full[0], "full_inertia": list(full), "H": hin[0], "H_dim": n - 1,
            "V4": v4["n_minus"], "V4_by": "balls" if v4["n_minus"] is not None else
            f"undecided at {v4['prec']} bits; min-max: C_N on V4 >= {max(full[0] - 3, 0)}",
            "V4_dim": v4["dim"], "centre_full": RI.inertia_both(R)[0]}


def row(eps_q, eps_finite: bool, is_bound: bool) -> str:
    """PREREG s3 with eps_t null: D0, D1 or D2 (D3 needs a finite eps_t)."""
    if not (eps_finite and is_bound):
        return "D0"
    return "D1" if eps_q < SCALE else "D2"


def r_centre(D, c: str, N: int):
    """(R_centre exact and symmetric, the bound on |Im Delta_T|_F, the bound on the asymmetry)."""
    import assemble as AS

    n = 2 * N + 1
    Q, T = AS.q_mp(c, N), AS.t_inf_mp(c, N)
    with mp.workdps(40):
        imq = max(abs(mp.im(mp.mpc(Q[i, j]))) for i in range(n) for j in range(n))
    if imq != 0:
        raise ArithmeticError("Q has an imaginary part; PREREG s2.1 reads a real Q")
    R = [[AS.mpf_to_q(mp.re(mp.mpc(Q[i, j]))) - AS.mpf_to_q(mp.re(mp.mpc(T[i, j]))) - arb_mid_q(D[i, j].real)
          for j in range(n)] for i in range(n)]
    e_im = AS.frob_up([[arb_up_q(abs(D[i, j].imag)) for j in range(n)] for i in range(n)])
    S = [[(R[i][j] + R[j][i]) / 2 for j in range(n)] for i in range(n)]
    e_asym = AS.frob_up([[R[i][j] - S[i][j] for j in range(n)] for i in range(n)])
    return S, e_im, e_asym


def stored_comparison(D, eps_q: fmpq) -> dict:
    """PREREG s4 item 2: ||centre(Delta_T_rb(2.9, 32)) - Delta_T_stored(280, 2266)||_2, float64 (measured)."""
    import numpy as np

    import assemble as AS

    nv, S = 280, 2266
    stored = AS.ts_stored("2.9", nv, S, 32) - AS.t_inf_float("2.9", 32)
    n = 65
    ours = np.array([[float(D[i, j].real.mid()) for j in range(n)] for i in range(n)])
    d = float(np.linalg.norm(ours - stored, 2))
    lim = float(BAND_29_32 + eps_q)
    return {"norm2": d, "band_plus_eps_q": lim, "exceeds": d > lim,
            "stored_norm2": float(np.linalg.norm(stored, 2)), "rebuilt_norm2": float(np.linalg.norm(ours, 2))}


def dyadic(x) -> list:
    """The ball midpoint of x as [m, e] with x.mid() = m 2^e exactly."""
    m, e = x.mid().man_exp()
    return [int(m), int(e)]


def centres_from(cells: dict):
    """{cell: acb_mat} from a centres file's {cell: rows of [m, e]}: exact midpoints, radius 0."""
    from flint import acb, acb_mat

    out = {}
    for kk, rows in cells.items():
        n = len(rows)
        D = acb_mat(n, n)
        for i in range(n):
            for j in range(n):
                m, e = rows[i][j]
                D[i, j] = acb(arb(m) * arb(2) ** e)
        out[kk] = D
    return out


def read(req: dict, outdir: str, key_fn, centres: dict | None = None) -> dict:
    """The rows; if `centres` is a dict, it is filled with every cell's centre(Delta_T) as dyadics."""
    import assemble as AS

    import rebuild as RB

    res = RB.assemble(req, req["shards"], outdir, key_fn)
    if centres is not None:
        for kk, r in res.items():
            if not kk.startswith("_"):
                D = r["delta_T"]
                centres[kk] = [[dyadic(D[i, j].real) for j in range(D.ncols())] for i in range(D.nrows())]
    is_bound = "_reading" not in res
    out = {"cells": {}, "is_bound": is_bound, "rows": {}}
    for c in req["cells"]:
        eqs = []
        for N in req["Ns"]:
            r = res[f"{c}|{N}"]
            D = r["delta_T"]
            fin = r["eps_q"].is_finite()
            eq = arb_up_q(r["eps_q"]) if fin else None
            eqs.append(eq)
            rec = {"radius_F": float(r["radius_F"].upper()), "p3_alias": float(r["p3_alias"].upper()),
                   "e1_aposteriori": float(r["e1_aposteriori"].upper()),
                   "tail_mass": [float(t.upper()) for t in r["tail_mass"]],
                   "eps_q": float(eq) if fin else None}
            if fin:
                R, e_im, e_asym = r_centre(D, c, N)
                aux = (2 * N + 1) * (AS.E_Q_ENTRY + AS.E_TINF_ENTRY)
                eps = eq + aux + e_im + e_asym
                rec.update({"eps_aux": float(aux), "e_im": float(e_im), "e_asym": float(e_asym),
                            "eps": [int(eps.p), int(eps.q)], "eps_float": float(eps), "C": counts(R, eps, N, c)})
                if (c, N) == ("2.9", 32):
                    out["stored_comparison"] = stored_comparison(D, eq)
            out["cells"][f"{c}|{N}"] = rec
        # the row at c reads the largest eps_q over N = 8, 16, 32 (conservative: D1 needs all three below)
        fin = all(e is not None for e in eqs)
        worst = max(eqs) if fin else None
        out["rows"][c] = {"row": row(worst, fin, is_bound), "eps_q_max": float(worst) if fin else None}
    return out


def checkpoint_digests(outdir: str, req: dict) -> dict:
    import rebuild as RB

    bl = RB.blocks(req)
    out = {}
    for sh in range(req["shards"]):
        r = RB.shard_range(len(bl), sh, req["shards"])
        if len(r):
            f = os.path.join(outdir, f"shard{sh:02d}of{req['shards']:02d}_block{r[-1]:05d}.json")
            out[str(sh)] = hashlib.sha256(open(f, "rb").read()).hexdigest()
    return out


if __name__ == "__main__":
    import guard as GD

    req = json.load(open(os.path.join(HERE, "RUN_REQUEST.json")))
    od = sys.argv[1]
    cen = {} if len(sys.argv) > 2 else None
    body = read(req, od, GD.key, cen)
    body["checkpoints_sha256"] = checkpoint_digests(od, req)
    print(json.dumps(body, indent=1))
    if cen is not None:  # python read_rows.py OUTDIR CENTRES.json: also the exact centres
        json.dump(cen, open(sys.argv[2], "w"), separators=(",", ":"))
