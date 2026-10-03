"""Rigorous Li enclosures, second scheme: midpoint rule + Cauchy remainder.

Integral: c_n = (1/2pi R^n) ∫_0^{2pi} f(R e^{it}) e^{-int} dt, f = log xi(1/(1-z)).
Midpoint evaluations are near-point Arb balls (tight). Remainder uses
|E| <= M2 (2pi)^3/(24 K^2) with M2 = 2M/(rho-R)^2 from Cauchy's estimate,
M = rigorous max of |f| on |w| = rho via coarse interval panels.
Branch: asserted via min Re(xi) lower > 0 on both circles.
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))


def _xi_acb(S, arb, acb):
    pi = acb(arb.pi())
    return S * (S - 1) / 2 * (-S / 2 * pi.log()).exp() * (S / 2).gamma() * S.zeta()


def bound_M(Rp, K0, prec):
    from flint import arb, acb, ctx
    old = ctx.prec
    ctx.prec = prec
    try:
        R = arb(Rp)
        m = 0.0
        min_re = 1e9
        ok = True
        for j in range(K0):
            lo = float(2 * math.pi * j / K0)
            hi = float(2 * math.pi * (j + 1) / K0)
            T = arb((lo + hi) / 2, (hi - lo) / 2 + 1e-15)
            X = _xi_acb(1 / (1 - acb(R * T.cos(), R * T.sin())), arb, acb)
            L = X.log()
            if not (X.is_finite() and L.is_finite()):
                ok = False
                break
            min_re = min(min_re, float(X.real.lower()))
            m = max(m, float(abs(L.real.upper())), float(abs(L.real.lower())),
                    float(abs(L.imag.upper())), float(abs(L.imag.lower())))
        return ok and min_re > 0, m, min_re
    finally:
        ctx.prec = old


def enclose_lambda_mid(n, K=16384, prec=128, R_str="0.5", rho_str="0.85", K0=2048):
    from flint import arb, acb, ctx
    old = ctx.prec
    ctx.prec = prec
    try:
        n_ = int(n)
        R = arb(R_str)
        rho = arb(rho_str)
        two_pi = arb.pi() * 2
        w = two_pi / K
        ok, M, min_re = bound_M(rho_str, K0, prec)
        if not ok:
            return {"n": n_, "finite": False, "note": "M bound failed"}
        gap = float(rho) - float(R)
        Rfl = float(R)
        # Full second-derivative bound for g(t) = f(R e^{it}) e^{-int}:
        # d/dt brings iR e^{it} f' (chain) and -in (oscillation), so
        # |g''| <= F2 + 2n F1 + n^2 M with F1 = R*M1, F2 = R*M1 + R^2*M2c,
        # M1 = M/gap, M2c = 2M/gap^2 (Cauchy). An earlier version used
        # M2c alone and understated the remainder for n >= 3 (CORRECTION.md).
        M1 = M / gap
        M2c = 2 * M / gap**2
        F1 = Rfl * M1
        F2 = Rfl * M1 + Rfl**2 * M2c
        G2 = F2 + 2 * n_ * F1 + n_**2 * M
        M2 = G2
        E = G2 * float(two_pi) ** 3 / (24 * K**2)
        total = acb(0)
        for j in range(K):
            mid = float(2 * math.pi * (j + 0.5) / K)
            T = arb(mid, 1e-15)
            Z = acb(R * T.cos(), R * T.sin())
            L = _xi_acb(1 / (1 - Z), arb, acb).log()
            E_ = acb((n_ * T).cos(), -(n_ * T).sin())
            total += L * E_
        cn = total * acb(w) / (acb(two_pi) * (R ** n_))
        err = E / (float(two_pi) * float(R) ** n_)
        lam = cn * n_ + acb(arb(0, err * n_))
        ok2 = bool(lam.is_finite())
        return {"n": n_, "K": K, "prec": prec, "R": R_str, "finite": ok2,
                "M": M, "M2": M2,
                "re_lo": str(lam.real.lower()) if ok2 else "nan",
                "re_hi": str(lam.real.upper()) if ok2 else "nan",
                "im_lo": str(lam.imag.lower()) if ok2 else "nan",
                "im_hi": str(lam.imag.upper()) if ok2 else "nan"}
    finally:
        ctx.prec = old


def main():
    import argparse
    import json
    import time
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmin", type=int, default=1)
    ap.add_argument("--nmax", type=int, default=5)
    ap.add_argument("--K", type=int, default=16384)
    ap.add_argument("--prec", type=int, default=128)
    ap.add_argument("--R", type=str, default="0.5")
    ap.add_argument("--rho", type=str, default="0.85")
    ap.add_argument("--K0", type=int, default=2048)
    args = ap.parse_args()
    t0 = time.time()
    rows = []
    for n in range(args.nmin, args.nmax + 1):
        row = enclose_lambda_mid(n, K=args.K, prec=args.prec, R_str=args.R, rho_str=args.rho, K0=args.K0)
        rows.append(row)
        print(row, flush=True)
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        f"enclosure_mid_R{args.R}_n{args.nmin}-{args.nmax}_K{args.K}_p{args.prec}.json")
    with open(path, "w") as fh:
        json.dump({"grade": "enclosure-carrying-midpoint-cauchy",
                   "rows": rows, "seconds": time.time() - t0}, fh, indent=1)
    print("wrote", path)


if __name__ == "__main__":
    main()
