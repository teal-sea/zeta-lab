"""Prime-location rigidity: window positivity is fine-tuned, capture is not.

Move one prime-power atom of zeta's truncated Weil form from y = log q to
y = log q + eps (weight fixed) and follow, at one window (c, N):

* lambda_1(eps): Hellmann-Feynman predicts lambda_1 + eps * dlam/dy with
  dlam/dy = v^T (dA/dy) v; positivity is lost at |eps| ~ lambda_1 / |dlam/dy|;
* capture of the perturbed ground state by the radical subspace R_4 (zeta's
  Xi times even polynomials of degree <= 8), which should survive until eps
  reaches the spectral gap scale (lambda_2 - lambda_1) / ||dA/dy||;
* the Sturm count (extra real zeros of F_v1 on [0, 40] beyond Xi's).

For the sign statements, ball LDL^T inertia of the perturbed matrix at
shift 0 (Arb, conclusive or reported inconclusive).

Usage: .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/rigidity.py [c N q]
writes data/rigidity_<c>_<N>_<q>.json.
"""

from __future__ import annotations

import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ccm_common as C  # noqa: E402
from flint import arb, arb_mat, ctx, fmpq  # noqa: E402
from mpmath import mp  # noqa: E402

import enclosures as EN  # noqa: E402
import wp_common as WP  # noqa: E402

DATA = os.path.join(HERE, "data")


def perturbed_matrix(c, N, prec, q, eps):
    """zeta's even matrix with the atom at log q moved to log q + eps."""
    bt = EN.BallTruncation(WP.cq(c), N, kind="zeta", prec=prec)
    ctx.prec = prec
    coeffs = []
    for y, w, n in WP._coeffs(bt):
        if n == q:
            y = y + eps
        coeffs.append((y, w, n))
    P, R = WP._prime_seqs(bt, coeffs)
    ctx.prec = prec
    return WP.sector_matrix(bt, "even", S=bt._S, archdiag=bt._archdiag, pole=True) + WP.sector_matrix(
        bt, "even", P=P, R=R
    )


def atom_derivative(c, N, prec, q):
    """dA/dy for the atom at y = log q (even sector)."""
    bt = EN.BallTruncation(WP.cq(c), N, kind="zeta", prec=prec)
    ctx.prec = prec
    L = bt.L
    pi = arb.pi()
    dP = [arb(0)] * (N + 1)
    dR = [arb(0)] * (N + 1)
    for y, w, n in WP._coeffs(bt):
        if n != q:
            continue
        for k in range(N + 1):
            om = 2 * pi * k / L
            dP[k] = w * om * (om * y).cos()
            dR[k] = w * 2 * (-(om * y).cos() / L - (1 - y / L) * om * (om * y).sin())
    return WP.sector_matrix(bt, "even", P=dP, R=dR)


def main(argv):
    c = int(argv[1]) if len(argv) > 1 else 13
    N = int(argv[2]) if len(argv) > 2 else 32
    q = int(argv[3]) if len(argv) > 3 else 2
    prec = C.prec_for("zeta", c, N)
    t0 = time.time()
    A = C.matrix("zeta", c, N, prec)
    pairs = C.lowest_pairs(A, k=3)
    ctx.prec = prec
    lam1 = pairs[0][0]
    lam2 = pairs[1][0]
    v = pairs[0][1]
    dA = atom_derivative(c, N, prec, q)
    dlam = C._dot(v, dA * v)
    # operator-norm proxy for dA: Frobenius norm (an upper bound)
    fro = sum((dA[i, j] ** 2 for i in range(N + 1) for j in range(N + 1)), arb(0)).sqrt()
    out = {
        "c": c,
        "N": N,
        "q": q,
        "prec": prec,
        "lambda1": lam1.str(10, radius=True),
        "lambda2": lam2.str(10, radius=True),
        "dlam_dy": dlam.str(10, radius=True),
        "frobenius_dA": fro.str(6),
        "eps_positivity_scale": (abs(lam1) / abs(dlam)).str(6),
        "eps_gap_scale": ((lam2 - lam1) / fro).str(6),
        "runs": [],
    }
    with mp.workdps(130):
        L = C.L_mp(c)
        rs = []
        for j in range(5):
            rs.append(
                [
                    (C.xi_real("zeta", 0, 40) / mp.sqrt(L) if j == 0 else mp.mpf(0))
                    if k == 0
                    else mp.sqrt(2 / L) * (-1) ** k * (2 * mp.pi * k / L) ** (2 * j) * C.xi_real("zeta", 2 * mp.pi * k / L, 40)
                    for k in range(N + 1)
                ]
            )
        gam40 = []
        k = 1
        while True:
            g = mp.im(mp.zetazero(k))
            if g > 40:
                break
            gam40.append(g)
            k += 1
    # eps = sign * 10^-e, sign chosen so that eps * dlam < 0 (the destabilising side)
    sgn = -1 if dlam > 0 else 1
    exps = sorted({int(e) for e in argv[4].split(",")}) if len(argv) > 4 else [60, 55, 50, 48, 46, 44, 42, 40, 36, 30, 20, 10]
    for e in exps:
        for s in (sgn, -sgn):
            eps = fmpq(s, 10**e)
            Ap = perturbed_matrix(c, N, prec, q, arb(eps))
            pp = C.lowest_pairs(Ap, k=2)
            ctx.prec = prec
            M = [[Ap[i, j] for j in range(N + 1)] for i in range(N + 1)]
            npos, nneg, concl = EN.ldlt_inertia(M, arb(0))
            rec = {
                "eps": f"{'-' if s < 0 else '+'}1e-{e}",
                "lambda1": pp[0][0].str(8, radius=True),
                "lambda2": pp[1][0].str(8, radius=True),
                "predicted_lambda1": (lam1 + arb(eps) * dlam).str(8, radius=True),
                "ldl_inertia_at_0": [npos, nneg, bool(concl)],
            }
            with mp.workdps(130):
                vp = C.to_mp(pp[0][1])
                res4, _ = C.project_residual(vp, rs)
                rec["proj_residual_R4"] = mp.nstr(res4, 6)
                rec["misfit0"] = mp.nstr(C.overlap_misfit(vp, rs[0]), 6)
                zz = C.real_zeros(lambda t, vv=vp: mp.re(C.F_mp(vv, L, t)), mp.mpf("0.3"), mp.mpf(40), mp.mpf("0.05"))
                rec["sturm_extra_zeros"] = len(zz) - len(gam40)
            out["runs"].append(rec)
            print(rec, flush=True)
    out["elapsed_s"] = round(time.time() - t0, 1)
    os.makedirs(DATA, exist_ok=True)
    WP.save(os.path.join(DATA, f"rigidity_{c}_{N}_{q}.json"), out)
    print({k: v for k, v in out.items() if k != "runs"})


if __name__ == "__main__":
    main(sys.argv)
