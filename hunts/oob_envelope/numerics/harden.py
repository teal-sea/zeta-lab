"""Enclosure-carrying lower bound for Zhu's reduced form R_H(T#) on a window.

Inputs: L, T#, envelope (kernel:D from envelope.json), N even Legendre modes,
GL order q on panels of width h. Steps, all in Arb:

 1. Leading block A (orders 0..2N-2) of R = beta* I + 2 p p^T + C,
    C_nm = (1/pi) int_0^{T#} (Psi_L + H - beta*) That_n That_m dt, by the GL
    rule at nodes snapped to exact dyadic Bessel arguments (assemble.py).
 2. Quadrature radius added to every entry of C: Trefethen (ATAP Thm 19.3),
    |I - I_q| <= (h/2) 64 M / (15 (rho^2 - 1) rho^{2q}) per panel, rho = 1 + sqrt 2,
    M a bound for |integrand| on the Bernstein ellipse, which lies in the
    rectangle |Re z - c| <= a_e = h/sqrt 2 / 2, |Im z| <= b_e = h/2. There:
      |That_n(z)| <= 2 sqrt(L nu_n) e^{L b_e}        (Poisson integral for j_n),
      |cos(lambda z)| <= cosh(lambda b_e),
      digamma half-sum bounded by acb evaluation on the rectangle.
    Plus the node-shift term h * |f'| * shift with |f'| <= M / 0.1 (Cauchy).
 3. Tail (orders >= 2N): with x = T# L, a_n = 2 sqrt(L nu_n) x^n / (2n+1)!!
    bounds |That_n| on [0, T#] (Zhu (12)); b_m = 2 sqrt(L nu_m) bounds all;
    |p_n| <= 2 sqrt(L nu_n) (L/2)^n / (2n+1)!! e^{L/2}; K = (T#/pi) sup|Psi+H-beta*|.
    eps_D (Gershgorin on the tail block) and eps_B (Schur test on the
    coupling), as in Zhu section 4.
 4. LDL^T of A - lambda0 I in Arb with the quadrature radii included: all
    pivots positive proves every symmetric matrix in the box is > lambda0 I.
 5. lambda_min(R) >= min(lambda0, beta* - eps_D) - eps_B   (Zhu (13)).

What this does NOT cover: the analytic step Q >= R_H (Zhu Thm 1.1 with
A_L -> S, H out of band) is an ordinary derivation (theory lane), and S is
the enclosure-carrying constant from envelope.py. The composite claim takes
the weakest grade among these.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

from flint import acb, arb, arb_mat, ctx

sys.path.insert(0, str(Path(__file__).resolve().parent))
from assemble import Symbol, ldl_inertia, load_envelope, sph_j_all, to_arb  # noqa: E402

HERE = Path(__file__).resolve().parent


def dfact_log(n: int) -> arb:
    """log (2n+1)!! = lgamma(2n+2) - n log 2 - lgamma(n+1)."""
    return arb(2 * n + 2).lgamma() - n * arb(2).log() - arb(n + 1).lgamma()


def digamma_rect_bound(u0: arb, u1: arb, v: arb) -> arb:
    """Upper bound of |psi(1/4 + i z / 2)| over Re z in [u0, u1], |Im z| <= v.
    With z = u + i y, w = 1/4 - y/2 + i u/2 lies in the box
    Re w in [1/4 - v/2, 1/4 + v/2], Im w in [u0/2, u1/2]; the conjugate branch
    psi(1/4 - i z/2) has the same modulus bound. acb's digamma returns nan on
    wide balls, so: |psi(w)| <= |psi(w_c)| + r sup |psi'| with r the half
    diagonal and |psi'(w)| <= sum_k 1/|w+k|^2 <= 1/(a^2+b^2) + int_0^inf dx/((a+x)^2+b^2),
    a = min Re w > 0, b = min |Im w| over the box."""
    ra, rb = v / 2, (u1 - u0) / 4
    wc = acb(arb(1) / 4, (u0 + u1) / 4)
    r = (ra * ra + rb * rb).sqrt()
    amin = arb(1) / 4 - v / 2
    if not bool(amin > 0):
        raise ValueError("box reaches Re w <= 0")
    lo, hi = u0 / 2, u1 / 2
    bmin = arb(0) if (bool(lo <= 0) and bool(hi >= 0)) or not (bool(lo > 0) or bool(hi < 0)) \
        else (lo if bool(lo > 0) else -hi)
    if bool(bmin > 0):
        dpsi = 1 / (amin ** 2 + bmin ** 2) + (arb.pi() / 2 - (amin / bmin).atan()) / bmin
    else:
        dpsi = 1 / amin ** 2 + 1 / amin
    return (abs(wc.digamma()) + r * dpsi).upper()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", default="4/5")
    ap.add_argument("--T", default="100")
    ap.add_argument("--env", default="sine:16", help="kernel:D, or 'none' for H = 0 (S = A_L)")
    ap.add_argument("--N", type=int, default=96)
    ap.add_argument("--h", default="1/2")
    ap.add_argument("--q", type=int, default=64)
    ap.add_argument("--prec", type=int, default=256)
    ap.add_argument("--lam0", nargs="*", default=["1e-17", "1.1e-17", "1.15e-17"])
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    ctx.prec = args.prec
    t0 = time.time()
    L, T, h = Fraction(args.L), Fraction(args.T), Fraction(args.h)
    La, Ta, ha = to_arb(L), to_arb(T), to_arb(h)
    npan = int(T / h)
    assert npan * h == T
    if args.env == "none":
        envs = {}
    else:
        kind, D = args.env.split(":")
        envs = {args.env: load_envelope(L, kind, int(D))}
    sym = Symbol(L, envs)
    S = sym.envs[args.env][0] if envs else sym.A_L
    beta = (Ta / (2 * arb.pi())).log() - 1 / Ta - S
    if not bool(beta > 0):
        raise SystemExit(f"beta* not positive: {beta}")
    N, K = args.N, 2 * args.N - 1
    nus = [arb(2 * i) + arb(1) / 2 for i in range(N)]
    sc = [(-1) ** i * 2 * (La * nu).sqrt() for i, nu in enumerate(nus)]
    a = La / 2
    pvec = [2 * (La * nu).sqrt() * a.bessel_i(nu) * (arb.pi() / (2 * a)).sqrt() for nu in nus]

    # ---- 1. leading block, GL rule
    gl = [arb.legendre_p_root(args.q, k, weight=True) for k in range(args.q)]
    C = arb_mat(N, N)
    shift = arb(0)
    for k in range(npan):
        a0 = ha * k
        cols, wts = [], []
        for x, w in gl:
            t_gl = a0 + ha * (1 + x) / 2
            xl = arb((t_gl * La).mid())
            t = xl / La
            shift = shift.max(abs(t - t_gl))
            j = sph_j_all(K, xl)
            cols.append([sc[i] * j[2 * i] for i in range(N)])
            s = sym.psi(t) - beta
            if envs:
                s += sym.H(args.env, t)
            wts.append(w * ha / 2 / arb.pi() * s)
        V = arb_mat(N, args.q, [cols[c][r] for r in range(N) for c in range(args.q)])
        Vw = arb_mat(N, args.q, [cols[c][r] * wts[c] for r in range(N) for c in range(args.q)])
        C += Vw * V.transpose()
    t_asm = time.time() - t0

    # ---- 2. quadrature error bound
    rho = 1 + arb(2).sqrt()
    b_e = ha / 2                      # ellipse semi-minor: (h/2)(rho - 1/rho)/2

    a_e = ha / arb(2).sqrt()
    comb_bound = sum((c * (b_e * ln).cosh() for _, c, ln in sym.pp), arb(0))
    H_bound = arb(0)
    b_l1 = arb(0)
    if envs:
        for lp, bs in sym.envs[args.env][1]:
            for kk, b in bs:
                H_bound += abs(b) * (b_e * kk * lp).cosh()
                b_l1 += abs(b)
    logpi = arb.pi().log()
    E_per_unit = arb(0)   # sum over panels of the per-panel bound divided by sqrt(nu_n nu_m)
    shift_term = arb(0)
    for k in range(npan):
        c0 = ha * k + ha / 2
        dg = digamma_rect_bound(c0 - a_e, c0 + a_e, b_e)
        sym_b = dg + logpi + comb_bound + H_bound + abs(beta)
        M = sym_b * 4 * La * (2 * La * b_e).exp()
        E_per_unit += ha / 2 * 64 * M / (15 * (rho ** 2 - 1) * rho ** (2 * args.q))
        shift_term += ha * M / arb("0.1") * shift
    E_unit = (E_per_unit + shift_term) / arb.pi()
    eps_Q = [[(E_unit * (nus[i] * nus[j]).sqrt()).upper() for j in range(N)] for i in range(N)]

    # ---- 3. tail bounds
    xT = Ta * La
    sup_dg = arb(0)
    for k in range(int(T) + 1):   # |Re psi(1/4 + it/2)| on [k, k+1]
        sup_dg = sup_dg.max(digamma_rect_bound(arb(k), arb(k + 1), arb(0)))
    Sup = sup_dg + logpi + sym.A_L + b_l1 + abs(beta)
    Kc = Ta / arb.pi() * Sup

    def a_n(n):
        return 2 * (La * (n + arb(1) / 2)).sqrt() * (n * xT.log() - dfact_log(n)).exp()

    def pi_n(n):
        return 2 * (La * (n + arb(1) / 2)).sqrt() * (n * (La / 2).log() - dfact_log(n)).exp() * (La / 2).exp()

    n0 = 2 * N
    r_a = xT ** 2 / ((2 * n0 + 3) * (2 * n0 + 5)) * ((n0 + arb(5) / 2) / (n0 + arb(1) / 2)).sqrt()
    r_p = (La / 2) ** 2 / ((2 * n0 + 3) * (2 * n0 + 5)) * ((n0 + arb(5) / 2) / (n0 + arb(1) / 2)).sqrt()
    if not (bool(r_a < 1) and bool(r_p < 1)):
        raise SystemExit("tail ratio not < 1; increase N")
    alpha = a_n(n0) / (1 - r_a)
    pis = pi_n(n0) / (1 - r_p)
    eps_D = Kc * a_n(n0) * alpha + 2 * pi_n(n0) * pis
    b_max = 2 * (La * nus[-1]).sqrt()
    b_sum = sum((2 * (La * nu).sqrt() for nu in nus), arb(0))
    p_max = max((abs(p) for p in pvec), key=lambda z: float(z.mid()))
    p_sum = sum((abs(p) for p in pvec), arb(0))
    B1 = Kc * b_max * alpha + 2 * p_max * pis
    Binf = Kc * a_n(n0) * b_sum + 2 * pi_n(n0) * p_sum
    eps_B = (B1 * Binf).sqrt()

    # ---- 4. LDL of A - lambda0 I with quadrature radii
    rows = []
    for i in range(N):
        row = []
        for j in range(N):
            v = C[i, j] + 2 * pvec[i] * pvec[j] + (beta if i == j else 0)
            row.append(v + arb(0, eps_Q[i][j]))
        rows.append(row)
    # the quadrature radius must actually be inside every LDL input entry
    assert all(bool(rows[i][j].rad() >= eps_Q[i][j]) for i in range(N) for j in range(N))
    out = {"L": str(L), "T": str(T), "env": args.env, "N": N, "q": args.q, "h": str(h), "prec": args.prec,
           "S": str(S.mid()) + " +/- " + str(S.rad()), "beta": float(beta.mid()),
           "eps_Q_max": float(max(max(r) for r in eps_Q)), "node_shift": float(shift.upper()),
           "eps_D": float(eps_D.upper()), "eps_B": float(eps_B.upper()), "K": float(Kc.upper()),
           "assembly_s": t_asm, "lam0": {}}
    print(json.dumps({k: v for k, v in out.items() if k != "lam0"}))
    best = None
    for s0 in args.lam0:
        lam0 = arb(s0)
        shifted = [[rows[i][j] - (lam0 if i == j else 0) for j in range(N)] for i in range(N)]
        neg, pos, und, piv = ldl_inertia(shifted)
        ok = (neg == 0 and und == 0)
        out["lam0"][s0] = {"pd": ok, "min_pivot": float(min(piv, key=lambda z: float(z.mid())).mid()) if ok else None,
                           "n_neg": neg, "undecided": und}
        print(s0, out["lam0"][s0])
        if ok:
            best = lam0 if best is None or bool(lam0 > best) else best
    if best is not None:
        bound = best.min(beta - eps_D) - eps_B
        out["lower_bound"] = float(bound.lower().mid())
        out["lower_bound_arb"] = bound.str(10)
        print("lambda_min(R_H) >=", bound.str(10))
    out["elapsed"] = time.time() - t0
    if args.out:
        Path(args.out).write_text(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
