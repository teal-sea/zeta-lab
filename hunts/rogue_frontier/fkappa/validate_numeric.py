"""Independent numerical validation of the C(v,w) constants.

C(v,w) is DEFINED (thesis Theorem 3 / eq. 7.7) by the asymptotic

    S(v,w;x) = sum_{n<=x} B(v,n) B(w,n)
             = (-1)^{|v|+|w|} theta(v,w) C(v,w) x (log x)^{|v|+|w|+1}
               + O(x (log x)^{|v|+|w|}),

where B((v_1..v_j), n) = b_{v_1} * ... * b_{v_{j-1}} * (b_{v_j} log)(n)
and the b_j are given by the recursion (3.6): b_1 = -Lambda,
b_{j+1}(n) = -( (b_j * Lambda)(n) + b_j(n) log n ).

This script computes S(v,w;x) directly from that recursion by sieve
(numpy, float64), fits S(x)/x as a polynomial in L = log x over a wide
range of x, and compares the leading coefficient against the two candidate
readings of Bian's machinery (see bian_engine.py, READING):

    pair          skip (Bian's code)   zero (literal (6.23))
    ((1),(1))     1                    1        (control, readings agree)
    ((2),(2))     7/3                  7/3      (control, readings agree)
    ((3),(1))     6/5                  1        (analytic value: 1)
    ((3),(3))     1577/252 ~ 6.258     293/60 ~ 4.883
    ((3),(1,1,1)) 4/35 ~ 0.1143        1/10

For ((3),(1)) no fit is needed: b_1 = -Lambda is supported on prime
powers, b_j(p) = (-1)^j log^j p, so S((j),(1);x) = sum_{p<=x} log^{j+3} p
+ O(sqrt(x) polylog) and C((j),(1)) = 1 exactly, for every j.  The sieve
fit is still reported as a sanity check of the fitting procedure itself.

Run:  .venv/bin/python hunts/rogue_frontier/fkappa/validate_numeric.py [X]
"""

import sys
import numpy as np

X = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**7


def sieve_lambda(X):
    """von Mangoldt Lambda[0..X] and log[0..X] (float64)."""
    lam = np.zeros(X + 1)
    is_comp = np.zeros(X + 1, dtype=bool)
    for p in range(2, int(X**0.5) + 1):
        if not is_comp[p]:
            is_comp[p * p::p] = True
    primes = np.nonzero(~is_comp)[0][2:]  # skip 0,1
    for p in primes:
        lp = np.log(float(p))
        q = p
        while q <= X:
            lam[q] = lp
            q *= p
    n = np.arange(X + 1, dtype=np.float64)
    n[0] = 1.0
    logn = np.log(n)
    return lam, logn, primes


def conv_lambda(b, lam_support, lam_vals, X):
    """(b * Lambda)(n) for n <= X.  lam_support: prime powers q,
    lam_vals: log p for each q."""
    out = np.zeros(X + 1)
    for q, lp in zip(lam_support, lam_vals):
        m = X // q
        out[q::q] += lp * b[1:m + 1]
    return out


def fit_leading(xs, Ss, deg):
    """Fit S(x)/x = sum_{j<=deg} a_j L^j; return leading coefficient a_deg
    plus a crude stability estimate (refit on the upper half of the range)."""
    L = np.log(xs)
    y = Ss / xs
    Ln = L / L.max()
    A = np.vander(Ln, deg + 1, increasing=True)
    coef, *_ = np.linalg.lstsq(A, y, rcond=None)
    a_top = coef[deg] / L.max() ** deg
    half = len(xs) // 2
    coef2, *_ = np.linalg.lstsq(A[half:], y[half:], rcond=None)
    a_top2 = coef2[deg] / L.max() ** deg
    return a_top, a_top2


def main():
    print(f"sieving to X = {X:.0e} ...")
    lam, logn, primes = sieve_lambda(X)
    qs = np.nonzero(lam)[0]
    qvals = lam[qs]

    b = {1: -lam}
    for j in range(1, 5):
        b[j + 1] = -(conv_lambda(b[j], qs, qvals, X) + b[j] * logn)

    # B vectors
    B = {}
    B[(1,)] = b[1] * logn
    B[(2,)] = b[2] * logn
    B[(3,)] = b[3] * logn
    # B((1,1,1),n) = b1 * b1 * (b1 log)(n)
    t = conv_lambda(b[1] * logn, qs, qvals, X)   # b1 * (b1 log): note b1=-Lam
    t = -t                                        # b1 * f = -(Lam * f)
    t2 = -conv_lambda(t, qs, qvals, X)
    B[(1, 1, 1)] = t2

    checkpoints = np.unique(np.geomspace(10**4, X, 220).astype(np.int64))
    pairs = [
        (((1,), (1,)), 1.0, 1.0),
        (((2,), (2,)), 7 / 3, 7 / 3),
        (((3,), (1,)), 6 / 5, 1.0),
        (((3,), (3,)), 1577 / 252, 293 / 60),
        (((3,), (1, 1, 1)), 4 / 35, 1 / 10),
    ]
    print(f"{'pair':22s} {'fit C':>10s} {'fit(hi)':>10s} "
          f"{'skip':>9s} {'zero':>9s}  verdict")
    for (v, w), skipC, zeroC in pairs:
        prod = B[v] * B[w]
        csum = np.cumsum(prod)
        Ss = csum[checkpoints]
        deg = sum(v) + sum(w) + 1
        a, a2 = fit_leading(checkpoints.astype(float), Ss, deg)
        dskip = abs(a - skipC) / abs(skipC)
        dzero = abs(a - zeroC) / abs(zeroC)
        if abs(skipC - zeroC) < 1e-12:
            verdict = "control"
        else:
            verdict = ("ZERO" if dzero < dskip else "SKIP") + \
                f"  (rel err zero {dzero:.1%}, skip {dskip:.1%})"
        print(f"{str(v)+' '+str(w):22s} {a:10.4f} {a2:10.4f} "
              f"{skipC:9.4f} {zeroC:9.4f}  {verdict}")


if __name__ == "__main__":
    main()
