"""Sieve-based numerical corroboration of the corrected C(v,w) constants.

C(v,w) is defined (thesis eq (7.7)) as the leading constant of

    S(v,w;x) = sum_{n<=x} B(v,n) B(w,n)
             = C(v,w) x (log x)^{|v|+|w|+1} (1 + o(1)),

with B built from the recursion (3.6): b_1 = -Lambda,
b_{j+1}(n) = -((b_j * Lambda)(n) + b_j(n) log n),
B((v_1..v_l), n) = b_{v_1} * ... * (b_{v_l} log)(n).

Method: compute the b_j and B by sieve to x = X (numpy), slice the sums
by omega(n) on squarefree n (each slice's summand is an exactly known
homogeneous polynomial in the log p_i, so this is a per-n identity), and
compare each slice against its exact smoothed prime integral
(sympy-exact polynomial integration of the same polynomial against
prod dt_i / log t_i). The smoothed integral carries the full polynomial
asymptotic; the residual deviation is the O(1/log x) corner deficit of
the prime-density approximation, which shrinks with x.

Discrimination: the corrected slice constants match within the corner
deficit (ratios ~0.75-1.00 at x = 1e7, rising with x); the published
(skip-mode) constants are off by factors up to ~6 and are excluded.
The pairs and slice integrands below:

    ((2),(2)):  omega=1: log^6 p;      omega=2: 4 s^2 t^2 (s+t)^2
    ((3),(3)):  omega=1: log^8 p;      omega=2: 9 (st)^2 (s+t)^4;
                omega=3: 36 (stu)^2 (s+t+u)^2
    ((3),(1,1,1)): omega=3: 12 (stu)^2 (s+t+u)^2

corrected slice constants: ((2),(2)): 1 + 1/3 (total 4/3, published 7/3);
((3),(3)): 1 + 3/4 + 1/20 (total 9/5, published skip 1577/252);
((3),(1,1,1)): 1/60 (published skip 4/35).

Run:  .venv/bin/python hunts/rogue_frontier/fkappa/validate_numeric.py [X]
"""

import sys
import numpy as np
import sympy as sp

X = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**7


def build():
    lam = np.zeros(X + 1)
    is_comp = np.zeros(X + 1, dtype=bool)
    for p in range(2, int(X**0.5) + 1):
        if not is_comp[p]:
            is_comp[p * p::p] = True
    primes = np.nonzero(~is_comp)[0][2:]
    for p in primes:
        lp = np.log(float(p))
        q = p
        while q <= X:
            lam[q] = lp
            q *= p
    n = np.arange(X + 1, dtype=np.float64)
    n[0] = 1.0
    logn = np.log(n)
    qs = np.nonzero(lam)[0]
    qv = lam[qs]

    def convL(b):
        out = np.zeros(X + 1)
        for q, lp in zip(qs, qv):
            out[q::q] += lp * b[1:X // q + 1]
        return out

    b1 = -lam
    b2 = -(convL(b1) + b1 * logn)
    b3 = -(convL(b2) + b2 * logn)
    B2 = b2 * logn
    B3 = b3 * logn
    t = -convL(b1 * logn)
    B111 = -convL(t)
    om = np.zeros(X + 1, dtype=np.int8)
    for p in primes:
        om[p::p] += 1
    sqf = np.ones(X + 1, dtype=bool)
    for p in primes[primes <= int(X**0.5)]:
        sqf[p * p::p * p] = False
    isprime = np.zeros(X + 1, dtype=bool)
    isprime[primes] = True
    return B2, B3, B111, om, sqf, isprime


def main():
    print(f"sieving to X = {X:.0e} ...")
    B2, B3, B111, om, sqf, isprime = build()
    s, t_, A, L = sp.symbols("s t_ A L", positive=True)
    l2 = sp.log(2)

    def IA(polyA, lo):
        return sp.lambdify(L, sp.integrate(polyA * sp.exp(A), (A, lo, L)),
                           "numpy")

    def I2(integrand_st, div):
        F = sp.integrate(integrand_st.subs(t_, A - s), (s, l2, A - l2))
        return IA(sp.expand(F) / div, 2 * l2)

    def I3(integrand_stu, u, div):
        inner = sp.integrate(integrand_stu.subs(u, A - s - t_),
                             (t_, l2, A - s - l2))
        F = sp.integrate(sp.expand(inner), (s, l2, A - 2 * l2))
        return IA(sp.expand(F) / div, 3 * l2)

    u = sp.symbols("u", positive=True)
    Lx = np.log(X)
    checks = [
        ("((2),(2)) om=1 [const 1]",
         np.where(isprime, B2 * B2, 0), IA(A**5, l2)),
        ("((2),(2)) om=2 [const 1/3]",
         np.where(sqf & (om == 2), B2 * B2, 0),
         I2(4 * s * t_ * (s + t_)**2, 2)),
        ("((3),(3)) om=1 [const 1]",
         np.where(isprime, B3 * B3, 0), IA(A**7, l2)),
        ("((3),(3)) om=2 [const 3/4]",
         np.where(sqf & (om == 2), B3 * B3, 0),
         I2(9 * s * t_ * (s + t_)**4, 2)),
        ("((3),(3)) om=3 [const 1/20]",
         np.where(sqf & (om == 3), B3 * B3, 0),
         I3(36 * s * t_ * u * (s + t_ + u)**2, u, 6)),
        ("((3),(1,1,1)) om=3 [const 1/60]",
         np.where(sqf & (om == 3), B3 * B111, 0),
         I3(12 * s * t_ * u * (s + t_ + u)**2, u, 6)),
    ]
    print(f"{'slice':36s} {'sieve/integral at X':>20s}")
    for name, arr, P in checks:
        ratio = arr.cumsum()[X] / P(Lx)
        print(f"{name:36s} {ratio:20.4f}")
    print("\nratios below 1 by O(1/log x) corner deficits are expected;")
    print("the published constants would put these ratios at ~0.2-6.")


if __name__ == "__main__":
    main()
