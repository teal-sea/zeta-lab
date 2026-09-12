"""The bandwidth landscape for both kernels, and the price of the band edge.

Nothing here is a result. Four measurements, each of which changed a
recommendation in ``MISSION.md``, and each of which is calibrated against a
published number or a known limit rather than trusted on its own.

1. **The window functional in the form that makes the trade visible.**
   Substituting ``v(u) = phi(u/lambda)`` into the laboratory's functional
   (`hunts/wide_search/xiprime.py`, generalized from the source paper's
   eq. 7.3) gives, for the zeta kernel,

       R(lambda, phi) = A(phi)/lambda + lambda * B(phi),
       A = int phi^2 / (int phi)^2,    B = int int |u-v| phi phi / (int phi)^2

   with the bound ``2 - R``. ``A >= 1`` by Cauchy-Schwarz with equality iff
   ``phi`` is constant, so the ``1/lambda`` cost is an L2-against-L1 defect of
   the window and the only way to cheapen it is to be flat. The flat window
   gives ``R = 1/lambda + lambda/3`` exactly.

2. **Window-shape optimization is worth almost nothing.** Measured below: the
   optimal window beats the flat one by about ``lambda^3/180``, and at the
   vacuity threshold the entire advantage is ``3.2e-4``. The flat window's
   threshold is the root of ``theta^2 - 6 theta + 3``, namely ``3 - sqrt 6``.
   This is why ``MISSION.md`` does not recommend re-optimizing the certificate
   window at each bandwidth: there is no room there.

3. **The xi-prime landscape sits 0.11 to 0.20 above the zeta one at every
   bandwidth**, and stays non-vacuous down to ``0.5133`` where the zeta one
   dies at ``0.5502``. Calibrated against two published numbers, see below.

4. **The band edge has a finite price.** The laboratory's own reason for
   bandwidth one is recorded at `hunts/outband_certificate/RESULTS.md`:
   "``F`` has no unconditional upper bound outside the band, so bandwidth one
   is forced". That names the missing input. It does not price it. Priced
   below, the answer is that an upper bound of *any* finite size on an
   arbitrarily thin sliver beyond the band is worth more than the whole
   remaining bandwidth-one headroom. Note the direction: hunts #110 and #118
   priced out-of-band *positivity*, a lower bound, which is the wrong-signed
   information for this method. **A literature search on 2026-09-12 then
   closed the door** (``MISSION.md`` section 8, ``RESULTS.md`` section 4.2):
   no such upper bound exists unconditionally, and under RH the best
   integrated bound tends to 7/8 rather than to zero as the sliver shrinks.
   The price stands as a measured fact about an input that is not available.

House rule: run with the repository virtualenv.

    .venv/bin/python hunts/short_interval/landscape.py

Stdlib only. The linear solves are pure Python Gaussian elimination at
``n = 160`` to ``200``, so every value carries a discretization error of order
``1e-5``; the zeta control is included at every step precisely so that error
is visible rather than assumed. Anything that needs more than four digits
should be re-run with the repository's numpy path or with ball arithmetic.
"""

from __future__ import annotations

from math import fabs, sqrt, tan

# ---------------------------------------------------------------------------
# linear algebra, stdlib
# ---------------------------------------------------------------------------


def _solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    aug = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: fabs(aug[r][col]))
        aug[col], aug[piv] = aug[piv], aug[col]
        inv = 1.0 / aug[col][col]
        pivot_row = aug[col]
        for r in range(col + 1, n):
            factor = aug[r][col] * inv
            if factor:
                row = aug[r]
                for k in range(col, n + 1):
                    row[k] -= factor * pivot_row[k]
    out = [0.0] * n
    for r in range(n - 1, -1, -1):
        out[r] = (aug[r][n] - sum(aug[r][k] * out[k] for k in range(r + 1, n))) / aug[r][r]
    return out


# ---------------------------------------------------------------------------
# the two form factors the machinery accepts unconditionally
# ---------------------------------------------------------------------------


def F_zeta(x: float) -> float:
    """Montgomery's form factor on the band, minus its Dirac spike."""
    return fabs(x)


def F_xiprime(x: float, kmax: int = 30) -> float:
    """Farmer-Gonek-Lee's ``F_1``, minus its Dirac spike.

    ``F_1(x) = |x| - 4x^2 + sum_{k>=1} ((k-1)!/(2k)!) (2|x|)^(2k+1)``,
    accumulated by ratio exactly as `hunts/wide_search/xiprime.py` does.
    Farmer-Gonek Theorem 1.1 (arXiv:0803.0425), with Lee, JLMS 90 (2014).
    """
    a = fabs(x)
    out = a - 4.0 * a * a
    term = 0.5 * (2.0 * a) ** 3          # k = 1: (0!/2!) (2a)^3
    out += term
    for k in range(2, kmax + 1):
        term = term * (k - 1) / ((2 * k) * (2 * k - 1)) * (2.0 * a) ** 2
        out += term
    return out


# ---------------------------------------------------------------------------
# the landscape
# ---------------------------------------------------------------------------


def _lags(lam: float, F, n: int, width: float = 1.0) -> list[float]:
    h = width / n
    return [lam * F(lam * k * h) for k in range(n)]


def R_optimal(lam: float, F, n: int = 160) -> float:
    """``min R`` over windows, by the Rayleigh quotient's linear solve.

    Minimizing ``<A v, v>`` subject to ``<1, v> = 1`` gives
    ``1/<1, A^-1 1>``, so the optimal window is never formed explicitly and
    this route shares no trigonometry with the closed form it checks.
    """
    h = 1.0 / n
    lag = _lags(lam, F, n)
    M = [
        [(h if i == j else 0.0) + lag[abs(i - j)] * h * h for j in range(n)]
        for i in range(n)
    ]
    w = _solve(M, [h] * n)
    return 1.0 / (lam * h * sum(w))


def R_flat(lam: float, F, n: int = 2000) -> float:
    """``R`` for the flat window, by exact lag multiplicities."""
    h = 1.0 / n
    lag = _lags(lam, F, n)
    total = n * lag[0] + 2.0 * sum((n - k) * lag[k] for k in range(1, n))
    return (1.0 + total * h * h) / lam


def C_wang(lam: float) -> float:
    """Wang (4.2), the optimal ``R`` for the zeta kernel in closed form."""
    return lam / 2 + (1 / sqrt(2)) / tan(lam / sqrt(2))


# ---------------------------------------------------------------------------
# the price of the band edge
# ---------------------------------------------------------------------------


def bound_with_outband_cap(L: float, B: float, n: int = 200) -> tuple[float, bool]:
    """``2 - min C_B`` for a window of length ``L``, capping ``F <= B`` out of band.

    The window ``f`` lives on ``[-L/2, L/2]``, so ``f`` correlated with itself
    reaches out to ``|alpha| = L``. In band the weight is ``|alpha|``; beyond
    it the honest statement is that ``F`` is bounded by some constant ``B``,
    which this replaces it with:

        C_B(f) = int f^2
                 + int int_{|u-v| <= 1} |u-v| f f
                 + B int int_{|u-v| > 1} f f

    Returns the bound and whether the minimizer is nonnegative. **The sign
    matters and is not cosmetic.** Lamzouri's Proposition 2.1 takes the window
    density as ``f = eta^2``, so ``f >= 0``, and the autocorrelation of a
    nonnegative function is nonnegative, which is what licenses replacing
    ``F`` by an upper bound out of band at all. A minimizer that changes sign
    is outside the class and its value is not a bound.
    """
    h = L / n
    lag = [(k * h if k * h <= 1.0 else B) for k in range(n)]
    M = [
        [(h if i == j else 0.0) + lag[abs(i - j)] * h * h for j in range(n)]
        for i in range(n)
    ]
    w = _solve(M, [h] * n)
    return 2.0 - 1.0 / (h * sum(w)), min(w) >= -1e-9


# ---------------------------------------------------------------------------

H = 0.6725007036794116
#: Alpoge-Furman Remark 7.1, the two published xi-prime figures at bandwidth 1
#: for the FLAT window. They are the calibration for `F_xiprime` above: a
#: landscape computed from a mis-transcribed series would miss them.
AF_REMARK_71 = (0.85838, 0.92919)
#: hunts/wide_search, the laboratory's own quartic-certificate xi-prime value.
LAB_H_STAR = 0.8686415005


def _bisect(f, lo: float, hi: float, iters: int = 28) -> float:
    sign_lo = f(lo) < 0
    for _ in range(iters):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if (f(mid) < 0) == sign_lo else (lo, mid)
    return (lo + hi) / 2


def main() -> None:
    print("1. The flat window, zeta kernel: is R_flat = 1/lambda + lambda/3?")
    print()
    for lam in (0.6, 1.0):
        print(f"   lambda {lam}: measured {R_flat(lam, F_zeta):.9f}   "
              f"formula {1 / lam + lam / 3:.9f}")
    flat_threshold = 3 - sqrt(6)
    print()
    print(f"   flat window's threshold, root of t^2 - 6t + 3 = 3 - sqrt 6 = {flat_threshold:.10f}")
    print(f"   Wang's optimal-window threshold theta_0             = 0.5501939647441547")
    print(f"   so the entire optimal-window advantage is worth       {flat_threshold - 0.5501939647441547:.2e}")
    print()
    print("   Read that before proposing to re-optimize a window.")

    print()
    print("2. Optimal window, zeta: Rayleigh solve against Wang's closed form")
    print("   (the discretization error visible here is the error in every")
    print("    xi-prime value below, where no closed form exists)")
    print()
    for lam in (0.6, 0.8, 1.0):
        solved, closed = R_optimal(lam, F_zeta), C_wang(lam)
        print(f"   lambda {lam}: solve {solved:.8f}   closed {closed:.8f}   "
              f"error {abs(solved - closed):.1e}")

    print()
    print("3. Flat minus optimal, against the predicted lambda^3/180")
    print()
    for lam in (0.6, 1.0):
        print(f"   lambda {lam}: gap {R_flat(lam, F_zeta) - C_wang(lam):.8f}   "
              f"lambda^3/180 {lam ** 3 / 180:.8f}")

    print()
    print("4. CALIBRATION of the xi-prime kernel against Alpoge-Furman Remark 7.1")
    print("   (flat window at bandwidth 1; a mis-transcribed series misses these)")
    print()
    r = R_flat(1.0, F_xiprime)
    print(f"   2 - R     = {2 - r:.6f}   published {AF_REMARK_71[0]}")
    print(f"   (3 - R)/2 = {(3 - r) / 2:.6f}   published {AF_REMARK_71[1]}")

    print()
    print("5. The landscape, optimal window, both kernels")
    print()
    print("   lambda    zeta           xi-prime       difference")
    for lam in (1.00, 0.80, 0.60, 0.55, 0.50):
        z, x = 2 - R_optimal(lam, F_zeta), 2 - R_optimal(lam, F_xiprime)
        print(f"   {lam:5.2f}    {z:+.6f}      {x:+.6f}      {x - z:+.4f}")
    print()
    x1 = 2 - R_optimal(1.0, F_xiprime)
    z1 = 2 - R_optimal(1.0, F_zeta)
    print(f"   at bandwidth 1 the xi-prime solve gives {x1:.6f} against the")
    print(f"   laboratory's quartic-certificate {LAB_H_STAR}, a gap of {x1 - LAB_H_STAR:+.1e}.")
    print(f"   The zeta control at the same settings is off by {z1 - H:+.1e} from a")
    print(f"   value known exactly, so that gap is method error and NOT a free gain.")

    print()
    print("6. Vacuity thresholds")
    print()
    zt = _bisect(lambda t: 2 - R_optimal(t, F_zeta, 120), 0.40, 0.70)
    xt = _bisect(lambda t: 2 - R_optimal(t, F_xiprime, 120), 0.40, 0.70)
    print(f"   zeta     {zt:.5f}   (Wang prints 0.55019)")
    print(f"   xi-prime {xt:.5f}   (no published counterpart)")

    print()
    print("7. THE PRICE OF THE BAND EDGE")
    print("   'F has no unconditional upper bound outside the band, so bandwidth")
    print("    one is forced' names the input. This prices it. Cells marked")
    print("    'signed' have a sign-changing minimizer and are NOT bounds.")
    print()
    base, _ = bound_with_outband_cap(1.0, 0.0)
    print(f"   baseline at L = 1: {base:.6f}   (true {H})")
    print()
    print("   F <= B     L = 1.05        L = 1.10        L = 1.20")
    for B in (2.0, 3.0, 6.0, 20.0):
        cells = []
        for L in (1.05, 1.10, 1.20):
            v, ok = bound_with_outband_cap(L, B)
            cells.append(f"{v:.6f}" + ("     " if ok else " sgn "))
        print(f"   {B:6.0f}     " + "  ".join(cells))
    print()
    print("   The bandwidth-one configuration ceiling headroom is 0.6818286874638")
    print(f"   minus {H} = {0.6818286874638 - H:.5f}. Every admissible cell above")
    print("   with B <= 6 exceeds it.")
    print()
    print("   Shadow price of bandwidth at 1, in closed form:")
    print(f"     c'(1) = (1/2) cot^2(1/sqrt 2) = {0.5 / tan(1 / sqrt(2)) ** 2:.13f}")
    print(f"     (3/2 - H)^2                   = {(1.5 - H) ** 2:.13f}")
    print("   Linear gain in band width against quadratic out-of-band mass is")
    print("   why the optimum extends at all. What is NOT established is that a")
    print("   constant B exists unconditionally: positive-definiteness gives only")
    print("   F(alpha) <= F(0), which grows like log T and is not a constant.")
    print("   That is the whole open question and MISSION.md section 8 states it.")


if __name__ == "__main__":
    main()
