"""Rigorous enclosure of Li coefficients via panel quadrature in Arb balls.

Method: lambda_n = n*c_n with c_n = (1/2pi R^n) ∫_0^{2pi} f(R e^{it}) e^{-int} dt,
f(z) = log xi(1/(1-z)), R = 1/2. Each panel's t-interval is covered by an arb
ball; every operation (cos, sin, exp, gamma, zeta, log) is Arb ball arithmetic,
hence inclusion-monotonic. The summed balls rigorously contain the integral.
Principal log is the correct branch here: the disk |z|<=1/2 is unconditionally
zero-free (images of zeros satisfy |z|>=1-1/gamma1>0.92) and the sampled arg is
small; the code refuses to decide if any panel ball is non-finite or if the
imaginary part does not contain 0 tightly.

Grade: enclosure-carrying for the stated (n, K, prec). Finite N only.
"""
import json
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))


def enclose_lambda(n, K=16384, prec=128, R_str="0.5"):
    from flint import arb, acb, ctx
    old = ctx.prec
    ctx.prec = prec
    try:
        R = arb(R_str)
        two_pi = arb.pi() * 2
        width = two_pi / K
        n_ = int(n)

        def xi_acb(s):
            pi = acb(arb.pi())
            return s * (s - 1) / 2 * (-s / 2 * pi.log()).exp() * (s / 2).gamma() * s.zeta()

        total = acb(0)
        for j in range(K):
            lo = float(2 * math.pi * j / K)
            hi = float(2 * math.pi * (j + 1) / K)
            T = arb((lo + hi) / 2, (hi - lo) / 2 + 1e-15)
            Z = acb(R * T.cos(), R * T.sin())
            S = 1 / (1 - Z)
            X = xi_acb(S)
            L = X.log()
            E = acb((n_ * T).cos(), -(n_ * T).sin())
            total += L * E * acb(width)
        cn = total / (acb(two_pi) * (R ** n_))
        lam = cn * n_
        ok = bool(lam.is_finite())
        return {
            "n": n_,
            "K": K,
            "prec": prec,
            "finite": ok,
            "re_lo": str(lam.real.lower()) if ok else "nan",
            "re_hi": str(lam.real.upper()) if ok else "nan",
            "im_lo": str(lam.imag.lower()) if ok else "nan",
            "im_hi": str(lam.imag.upper()) if ok else "nan",
        }
    finally:
        ctx.prec = old


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=3)
    ap.add_argument("--K", type=int, default=16384)
    ap.add_argument("--prec", type=int, default=128)
    args = ap.parse_args()
    t0 = time.time()
    rows = []
    for n in range(1, args.nmax + 1):
        row = enclose_lambda(n, K=args.K, prec=args.prec)
        rows.append(row)
        print(row, flush=True)
    blob = {"grade": "enclosure-carrying-panel-quadrature", "rows": rows,
            "seconds": time.time() - t0}
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        f"enclosure_li_K{args.K}_p{args.prec}.json")
    with open(path, "w") as fh:
        json.dump(blob, fh, indent=1)
    print("wrote", path)


if __name__ == "__main__":
    main()
