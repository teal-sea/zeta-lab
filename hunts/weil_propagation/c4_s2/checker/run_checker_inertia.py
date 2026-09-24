"""Follow-up 3 (checker/, RESULTS s7.9): exact inertia of the stored c = 2.9 matrices.

The count n_-(R_S) below -band at c = 2.9 (4, 10, 20 at N = 8, 16, 32) was
read off numpy eigenvalues of a float64 matrix. That matrix is a finite
table of float64 numbers, each an exact dyadic rational, so its inertia is a
question with an exact answer. This script answers it for the eight c = 2.9
builds of the snapshot (digest b2e7787bce7a) and writes checker_inertia.json.
It reads checker_ts_snapshot.json and checker_ts_cells.json and changes
neither.

The matrix. R = Q - T_S formed in numpy exactly as run_checker_ts.analyse
forms it (Q = the checker's Q at dps 40 rounded to float64, its central
block for N < 32; T_S = the snapshot row), then the lower triangle mirrored,
because numpy's eigh and eigvalsh read the lower triangle (UPLO = 'L').
Every entry is converted with float.as_integer_ratio, without rounding. The
shift is the band stored in checker_ts_cells.json, never re-derived.

Two exact routes over the rationals (python-flint fmpq), which must agree:
  (a) symmetric elimination, A = L D L^T with diagonal pivoting, counting
      the signs of D (Sylvester's law of inertia). If every remaining
      diagonal entry is 0 while an off-diagonal one is not, the congruence
      e_i -> e_i + e_j makes the diagonal 2 A_ij, which is not 0;
  (b) the characteristic polynomial (fmpq_mat.charpoly) and Descartes' rule
      of signs, which is exact for a polynomial whose roots are all real,
      as the characteristic polynomial of a symmetric matrix's is.
By Sylvester, n_-(R + band I) is the number of eigenvalues of R strictly
below -band. count_below(t) = n_-(R - t I) is the number strictly below t.

Brackets. The k-th smallest eigenvalue lambda_k lies in [a, b) exactly when
count_below(a) <= k - 1 and count_below(b) >= k. Seeds are the float64
eigenvalues plus and minus 2^-41; each end is widened by doubling until the
exact counts confirm it, then the shift is bisected until b - a <= 2^-40.
Both routes evaluate every end. The seeds only save work: every bracket is
decided by exact counts.

The C4 function class (theory s7.2: g-hat vanishing at +i/2, -i/2 and 0).
By checker_q.transform_rows, "plus" is proportional to 1/(1/2 + i w_n) and
"minus" to its complex conjugate, with w_n = 2 pi n / L. So both vanish
exactly when v is orthogonal to the real vectors h_n = 1/(L^2 + 16 pi^2 n^2)
and n h_n, and "zero" is v_0. V_4 is therefore the complexification of a
real subspace of codimension 3, and a real symmetric form has the same
inertia on both. Its basis Z keeps the coordinates |n| >= 2 free and solves
for v_1, v_{-1} (v_0 = 0); its entries involve pi and L = log(29/10), so Z
is enclosed in arb balls and In(Z^T A Z) is computed by ball elimination,
every pivot required to exclude 0 (at 256 bits, then 512; otherwise the
class count is reported as undecided). By min-max, for a subspace of
codimension 3: n_-(A) - 3 <= n_-(A on V_4) <= n_-(A).

    PYTHONPATH=<worktree root> <venv python> .../run_checker_inertia.py
"""

from __future__ import annotations

import contextlib
import hashlib
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import numpy as np  # noqa: E402
from flint import arb, arb_mat, ctx, fmpq, fmpq_mat  # noqa: E402

import checker_q as CQ  # noqa: E402
import run_checker_ts as RT  # noqa: E402

CELL = "2.9"
C_EXACT = fmpq(29, 10)
DIGEST = "b2e7787bce7a77db4a1a81b9311fc75a2b9326649b88a49883bd4d737ca70eaa"
READING_COMMIT = None  # the pre-registration commit, filled in by the analysis commit
OUT = os.path.join(HERE, "checker_inertia.json")
CELLS_JSON = os.path.join(HERE, "checker_ts_cells.json")
WIDTH = fmpq(1, 2 ** 40)
SEED_HALF = fmpq(1, 2 ** 41)
MULTIPLES = (1, 2, 5, 10)  # 1 is the criterion; 2, 5, 10 are a sensitivity row
BALL_PRECS = (256, 512)
CODIM_V4 = 3

# (nvec, S as keyed, N): every c = 2.9 build of the snapshot, and where the
# stored band and the stored float count of each are read (s7.9 clauses 2, 7).
BUILDS = [
    (80, 1200, 8, ("8", "band"), ("8", "full", "n_minus")),
    (120, 1600, 16, ("16", "band"), ("16", "full", "n_minus")),
    (160, 1600, 16, ("16", "band"), ("modes_N16_S1600", "160", "N16_n_minus")),
    (200, 2400, 32, ("modes_N32", "band"), ("modes_N32", "builds", "200", "n_minus")),
    (240, 2400, 32, ("modes_N32", "band"), ("modes_N32", "builds", "240", "n_minus")),
    (280, 2266, 32, ("modes_N32", "band"), ("modes_N32", "builds", "280", "n_minus")),
    (319, 2633, 32, ("modes_N32", "band"), ("modes_N32", "builds", "319", "n_minus")),
    (364, 3060, 32, ("modes_N32", "band"), ("modes_N32", "builds", "364", "n_minus")),
]


def build_key(nv, S, N):
    return f"{int(nv)}|{int(S)}|{int(N)}"


def dig(d, path):
    for p in path:
        d = d[p]
    return d


# ------------------------------------------------------------ exact routes


def to_q(x) -> fmpq:
    """A float64 as the exact rational it is."""
    return fmpq(*float(x).as_integer_ratio())


def exact_matrix(A) -> list:
    """A symmetric float64 array as a list of rows of fmpq, entry by entry, exactly."""
    n = A.shape[0]
    return [[to_q(A[i, j]) for j in range(n)] for i in range(n)]


def lower_mirrored(R):
    """The symmetric matrix numpy's eigh reads from R (UPLO = 'L')."""
    return np.tril(R) + np.tril(R, -1).T


def shifted(A, s) -> list:
    """A + s I, exactly (s an fmpq)."""
    return [[a + s if i == j else a for j, a in enumerate(row)] for i, row in enumerate(A)]


def inertia_ldl(A) -> tuple:
    """(n_minus, n_zero, n_plus) of a symmetric rational matrix, by symmetric
    elimination with diagonal pivoting (Sylvester's law of inertia)."""
    M = [list(r) for r in A]
    idx = list(range(len(M)))
    neg = pos = 0
    while idx:
        p = next((i for i in idx if M[i][i] != 0), None)
        if p is None:
            pair = next(((i, j) for a, i in enumerate(idx) for j in idx[a + 1:] if M[i][j] != 0), None)
            if pair is None:
                break  # the remaining block is 0: that many zero eigenvalues
            i, j = pair  # congruence e_i -> e_i + e_j; the new diagonal entry is 2 M_ij
            new_row = {k: M[i][k] + M[j][k] for k in idx if k != i}
            dii = M[i][i] + 2 * M[i][j] + M[j][j]
            for k, v in new_row.items():
                M[i][k] = v
                M[k][i] = v
            M[i][i] = dii
            p = i
        d = M[p][p]
        if d < 0:
            neg += 1
        else:
            pos += 1
        idx.remove(p)
        col = [M[i][p] for i in idx]
        for a, i in enumerate(idx):
            if col[a] == 0:
                continue
            f = col[a] / d
            Mi = M[i]
            for b in range(a, len(idx)):
                j = idx[b]
                v = Mi[j] - f * col[b]
                Mi[j] = v
                M[j][i] = v
    return neg, len(idx), pos


def _sign_changes(cs) -> int:
    s = [c for c in cs if c != 0]
    return sum(1 for x, y in zip(s, s[1:]) if (x > 0) != (y > 0))


def inertia_charpoly(A) -> tuple:
    """(n_minus, n_zero, n_plus) of a symmetric rational matrix, from its
    characteristic polynomial by Descartes' rule of signs (exact when every
    root is real). The three must add up to the dimension; they would not if
    a root were not real, so that sum is checked."""
    n = len(A)
    co = fmpq_mat(A).charpoly().coeffs()  # ascending, monic, degree n
    z = next(k for k, c in enumerate(co) if c != 0)
    co = co[z:]
    pos = _sign_changes(co)
    neg = _sign_changes([c if k % 2 == 0 else -c for k, c in enumerate(co)])
    if neg + z + pos != n:
        raise ArithmeticError(f"Descartes counts {neg} + {z} + {pos} != {n}: a non-real root")
    return neg, z, pos


def inertia_both(A) -> tuple:
    a, b = inertia_ldl(A), inertia_charpoly(A)
    if a != b:
        raise ArithmeticError(f"exact routes disagree: LDL^T {a}, charpoly {b}")
    return a


def count_below(A, t, both=True) -> int:
    """Number of eigenvalues of A strictly below t (t an fmpq), exactly."""
    M = shifted(A, -t)
    return (inertia_both(M) if both else inertia_charpoly(M))[0]


def bracket(A, k, seed, width=WIDTH, both=True, split=None) -> dict:
    """[lo, hi) containing lambda_k (1-based, ascending), decided by exact
    counts. If ``split`` lies strictly inside the bracket, it is tested once
    and becomes an end, so a bracket never straddles the threshold."""
    evals = 0

    def below(t):
        nonlocal evals
        evals += 1
        return count_below(A, t, both)

    s = to_q(seed)
    step = SEED_HALF
    lo = s - step
    while below(lo) > k - 1:
        step *= 2
        lo = s - step
    step = SEED_HALF
    hi = s + step
    while below(hi) < k:
        step *= 2
        hi = s + step
    while hi - lo > width:
        m = (lo + hi) / 2
        if below(m) >= k:
            hi = m
        else:
            lo = m
    if split is not None and lo < split < hi:
        if below(split) >= k:
            hi = split
        else:
            lo = split
    return {"k": k, "lo": lo, "hi": hi, "evals": evals}


# --------------------------------------------------------- the C4 class V_4


@contextlib.contextmanager
def arb_prec(bits: int):
    """python-flint's working precision, restored on exit."""
    old = ctx.prec
    ctx.prec = bits
    try:
        yield
    finally:
        ctx.prec = old


def class_basis(N: int, prec: int):
    """arb enclosure of the basis Z of V_4 at c = 29/10: columns indexed by the
    free coordinates |n| >= 2, rows by n = -N..N (index 0 is n = -N)."""
    with arb_prec(prec):
        L = arb(C_EXACT).log()
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


def class_constraints(N: int, prec: int):
    """The three real constraint rows of V_4, as arb vectors: h, n h, e_0."""
    with arb_prec(prec):
        L = arb(C_EXACT).log()
        pi = arb.pi()
        h = [1 / (L * L + 16 * pi * pi * n * n) for n in range(-N, N + 1)]
        nh = [n * h[n + N] for n in range(-N, N + 1)]
        e0 = [arb(1) if n == 0 else arb(0) for n in range(-N, N + 1)]
        return h, nh, e0


def inertia_balls(M) -> tuple | None:
    """(n_minus, 0, n_plus) of every symmetric matrix inside the arb ball
    matrix M (list of rows of arb), by elimination with diagonal pivoting in
    ball arithmetic; None when some pivot ball contains 0 (undecided)."""
    M = [list(r) for r in M]
    idx = list(range(len(M)))
    neg = pos = 0
    while idx:
        p = max(idx, key=lambda i: abs(float(M[i][i].mid())))
        d = M[p][p]
        if d < 0:
            neg += 1
        elif d > 0:
            pos += 1
        else:
            return None
        idx.remove(p)
        col = [M[i][p] for i in idx]
        for a, i in enumerate(idx):
            f = col[a] / d
            Mi = M[i]
            for b in range(a, len(idx)):
                j = idx[b]
                v = Mi[j] - f * col[b]
                Mi[j] = v
                M[j][i] = v
    return neg, 0, pos


def class_inertia(RL, shift, N: int) -> dict:
    """In(Z^T (RL + shift I) Z) on V_4, at the first precision where every
    pivot excludes 0."""
    n = RL.shape[0]
    for prec in BALL_PRECS:
        with arb_prec(prec):
            Z, _ = class_basis(N, prec)
            A = arb_mat(n, n)
            s = arb(shift)  # exact: a dyadic of at most 53 bits times an integer
            for i in range(n):
                for j in range(n):
                    A[i, j] = arb(float(RL[i, j])) + (s if i == j else 0)
            M = Z.transpose() * A * Z
            m = M.nrows()
            res = inertia_balls([[M[i, j] for j in range(m)] for i in range(m)])
        if res is not None:
            return {"n_minus": res[0], "n_zero": 0, "n_plus": res[2], "dim": m, "prec": prec}
    return {"n_minus": None, "undecided": True, "dim": n - CODIM_V4, "prec": BALL_PRECS[-1]}


def class_float_count(RL, band, N: int) -> int:
    """The same count in float64 (measured): orthonormalise Z's midpoints by QR."""
    Z, _ = class_basis(N, 64)
    Zf = np.array([[float(Z[i, j].mid()) for j in range(Z.ncols())] for i in range(Z.nrows())])
    B, _ = np.linalg.qr(Zf)
    return int((np.linalg.eigvalsh(B.T @ RL @ B) < -band).sum())


# ------------------------------------------------------------------ the run


def stored_R(snap, Qfull, nv, S, N):
    """R = Q - T_S as run_checker_ts.analyse forms it (float64)."""
    Q = RT.to_np(CQ.central_block(Qfull, N) if N < 32 else Qfull).real
    TS = np.array(snap["T_S"][RT.unit_key(CELL, N, 40, nv, S)])
    return Q - TS


def q_pair(x: fmpq) -> list:
    return [int(x.p), int(x.q)]


def analyse_build(snap, cells, Qfull, nv, S, N, band_path, count_path) -> dict:
    t0 = time.time()
    R = stored_R(snap, Qfull, nv, S, N)
    RL = lower_mirrored(R)
    band = float(dig(cells, band_path))
    float_count = int(dig(cells, count_path))
    beta = to_q(band)
    A = exact_matrix(RL)
    w = np.linalg.eigvalsh(R)
    rec = {"nvec": nv, "S": S, "N": N, "dim": int(R.shape[0]),
           "band": band, "band_source": "cells['2.9']" + "".join(f"['{p}']" for p in band_path),
           "band_exact": q_pair(beta),
           "float_count": float_count,
           "float_count_source": "cells['2.9']" + "".join(f"['{p}']" for p in count_path),
           "float_count_here": int((w < -band).sum()),
           "R_sha256": hashlib.sha256(np.ascontiguousarray(R).tobytes()).hexdigest(),
           "RL_sha256": hashlib.sha256(np.ascontiguousarray(RL).tobytes()).hexdigest(),
           "symmetric_defect": float(np.abs(R - R.T).max())}
    # clause 3: exact inertia at the band, and clause 5: the sensitivity row
    rec["exact"] = {}
    for m in MULTIPLES:
        rec["exact"][f"x{m}"] = list(inertia_both(shifted(A, m * beta)))
    if rec["symmetric_defect"] != 0.0:  # clause 1: the upper mirror too
        RU = np.triu(R) + np.triu(R, 1).T
        rec["exact_upper_mirror_at_band"] = list(inertia_both(shifted(exact_matrix(RU), beta)))
    k = rec["exact"]["x1"][0]
    # clause 4: brackets of lambda_1 .. lambda_{k+1}
    brs = []
    for j in range(1, k + 2):
        b = bracket(A, j, w[j - 1], split=-beta)
        brs.append({"k": j, "lo": q_pair(b["lo"]), "hi": q_pair(b["hi"]),
                    "lo_float": float(b["lo"]), "hi_float": float(b["hi"]),
                    "float_eig": float(w[j - 1]),
                    # lambda_k < hi, so hi <= -band means lambda_k < -band
                    "strictly_below_band": bool(b["hi"] <= -beta),
                    "at_or_above_band": bool(b["lo"] >= -beta),
                    # margin below -band = -band - lambda_k, in (-band - hi, -band - lo]
                    "margin_low": float(-beta - b["hi"]), "margin_high": float(-beta - b["lo"]),
                    "evals": b["evals"]})
    rec["brackets"] = brs[:k]
    rec["first_not_counted"] = brs[k]
    # clause 7: what "holds" means
    fails = [b["k"] for b in rec["brackets"] if not b["strictly_below_band"]]
    fails += list(range(k + 1, float_count + 1))  # counted in float64, not below -band exactly
    rec["float_counted_not_below_band"] = fails
    rec["holds"] = bool(rec["exact"]["x1"][1] == 0 and k == float_count and not fails)
    # clause 6: the C4 class V_4
    cls = {}
    for m in MULTIPLES:
        cls[f"x{m}"] = class_inertia(RL, m * beta, N)
    cls["float_count_at_band"] = class_float_count(RL, band, N)
    kc = cls["x1"]["n_minus"]
    cls["codim_bound"] = [k - CODIM_V4, k]
    cls["within_codim_bound"] = None if kc is None else bool(k - CODIM_V4 <= kc <= k)
    rec["class_V4"] = cls
    rec["seconds"] = round(time.time() - t0, 1)
    print(build_key(nv, S, N), "exact", rec["exact"], "holds", rec["holds"],
          "class", kc, rec["seconds"], "s", flush=True)
    return rec


def main():
    with open(RT.SNAP) as fh:
        snap = json.load(fh)
    if snap["meta"]["ts_inputs_digest"] != DIGEST:
        raise SystemExit(f"refused: snapshot digest {snap['meta']['ts_inputs_digest'][:12]} != {DIGEST[:12]}")
    with open(CELLS_JSON) as fh:
        cells_all = json.load(fh)
    cells = cells_all["cells"][CELL]
    Qfull = CQ.Q_matrix(CELL, 32, 40)
    out = {"meta": {
        "cell": CELL, "ts_inputs_digest": DIGEST, "reading_commit": READING_COMMIT,
        "snapshot_sha256": hashlib.sha256(open(RT.SNAP, "rb").read()).hexdigest(),
        "cells_json_sha256": hashlib.sha256(open(CELLS_JSON, "rb").read()).hexdigest(),
        "matrix": "R = Q - T_S in float64 as run_checker_ts.analyse forms it; lower triangle mirrored "
                  "(what numpy eigh reads); entries converted by float.as_integer_ratio",
        "routes": "(a) LDL^T over Q with diagonal pivoting (Sylvester); (b) fmpq_mat.charpoly and "
                  "Descartes' rule of signs; both at every shift, required to agree",
        "bracket": "lambda_k in [lo, hi) iff count_below(lo) <= k - 1 and count_below(hi) >= k; "
                   "seeds float eigenvalue +- 2^-41, widened by doubling, bisected to width <= 2^-40",
        "class_V4": "g-hat(+i/2) = g-hat(-i/2) = g-hat(0) = 0: v_0 = 0, sum h_n v_n = 0, sum n h_n v_n = 0, "
                    "h_n = 1/(L^2 + 16 pi^2 n^2), L = log(29/10); basis Z in arb balls, "
                    "ball elimination with every pivot excluding 0",
        "multiples": list(MULTIPLES), "width": q_pair(WIDTH), "ball_precs": list(BALL_PRECS),
        "python": sys.executable, "numpy": np.__version__}, "builds": {}}
    t0 = time.time()
    for nv, S, N, band_path, count_path in BUILDS:
        out["builds"][build_key(nv, S, N)] = analyse_build(snap, cells, Qfull, nv, S, N, band_path, count_path)
        with open(OUT, "w") as fh:  # checkpoint per build
            json.dump(out, fh, indent=1)
    out["meta"]["seconds"] = round(time.time() - t0, 1)
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    return out


if __name__ == "__main__":
    main()
