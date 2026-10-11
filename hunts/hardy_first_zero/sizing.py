"""Measured constants for the Lean route to the first zero of zeta on the critical line.

Run from the repository root:

    .venv/bin/python hunts/hardy_first_zero/sizing.py            # print, write artifacts/sizing.json
    .venv/bin/python hunts/hardy_first_zero/sizing.py --no-write # print only

Everything here sizes the four pieces of the Lean plan in `RESULTS.md` before any
of them is formalized:

1. **The Euler-Maclaurin representation** of zeta on `Re s = 1/2`, at two orders:

       zeta(s) = sum_{n<N} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 + s N^{-s-1}/12 - E4,
       |E4| <= |s(s+1)(s+2)(s+3)| (N-1)^{-sigma-3} / (720 (sigma+3))          (order 4)

   and the order-2 (trapezoid) form, whose remainder constant is the one the
   lab's `norm_trapezoid_sub_integral_le` delivers:

       zeta(s) = sum_{n<N} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 - E2,
       |E2| <= |s(s+1)| N^{-sigma-1} / (8 (sigma+1)).

2. **The sign test that needs no value of the Riemann-Siegel theta**:

       Z(a) Z(b) < 0  <=  Re(zeta(s_a) conj zeta(s_b)) < 0  and  cos(theta(b) - theta(a)) > 0,

   so only a crude bound on the increment of theta is needed, not theta itself.
3. **That crude bound**, derived from Euler's limit `GammaSeq -> Gamma`: the
   partial phases `phi_n` of `pi^{i delta} GammaSeq(z_a, n) GammaSeq(conj z_b, n)`
   stay inside an explicit window for every `n >= 1`.
4. **The box arithmetic**: the lab's bit-exact `Fraction` mirror of the Lean
   interval layer (`scripts/61_rung3_mirror.py`) evaluates the order-4 main term
   at both endpoints, and the sign test is run on the resulting rational boxes.

Grades (`CLAUDE.md`, the certainty ladder): the endpoint values of Z are
enclosure-carrying (Arb) and cross-checked against `mpmath.iv`, so *hardened*;
the remainder bounds are formulas evaluated in floating point and checked against
Arb enclosures of zeta at the two endpoints, *hardened* at those points; the
mirror result is one route (the Lean kernel would be the second), so *measured*;
the phase window is an ordinary derivation written out in `RESULTS.md`, not yet
reviewed and not yet kernel-checked. Nothing here is a theorem.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path

import mpmath
from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(ROOT))

from zeta import rigor  # noqa: E402

#: The planned endpoints, as exact rationals: (14.13, 14.14) contains gamma_1.
A = Fraction(1413, 100)
B = Fraction(707, 50)
#: `CLAUDE.md`, ground truth.
GAMMA_1 = 14.134725141734694
#: The truncation the Lean certificate is planned at (margin x14 at the endpoints).
N_PLAN = 30


# ---------------------------------------------------------------------------
# 1. Euler-Maclaurin main terms and remainder bounds
# ---------------------------------------------------------------------------


def s_of(t) -> mpmath.mpc:
    """The critical-line point 1/2 + i t, from an exact rational when given one."""
    tt = mpmath.mpf(t.numerator) / t.denominator if isinstance(t, Fraction) else mpmath.mpf(t)
    return mpmath.mpc(mpmath.mpf(1) / 2, tt)


def em4_main(s, N: int, b2_sign: int = 1, half_term: bool = True):
    """Order-4 main term. `b2_sign` and `half_term` exist only to plant faults."""
    total = mpmath.fsum(mpmath.power(n, -s) for n in range(1, N))
    total += mpmath.power(N, 1 - s) / (s - 1)
    if half_term:
        total += mpmath.power(N, -s) / 2
    total += b2_sign * s * mpmath.power(N, -s - 1) / 12
    return total


def em2_main(s, N: int):
    total = mpmath.fsum(mpmath.power(n, -s) for n in range(1, N))
    return total + mpmath.power(N, 1 - s) / (s - 1) + mpmath.power(N, -s) / 2


def em4_bound(s, N: int):
    sig = mpmath.re(s)
    num = abs(s) * abs(s + 1) * abs(s + 2) * abs(s + 3)
    return num * mpmath.power(N - 1, -sig - 3) / (720 * (sig + 3))


def em2_bound(s, N: int):
    sig = mpmath.re(s)
    return abs(s) * abs(s + 1) * mpmath.power(N, -sig - 1) / (8 * (sig + 1))


def zeta_arb(t: Fraction, prec: int = 200):
    """Arb ball for zeta(1/2 + i t) at the exact rational t: (re_lo, re_hi, im_lo, im_hi)."""
    return rigor._FlintBackend.zeta_box(Fraction(1, 2), Fraction(1, 2), Fraction(t), prec)


def em_error_upper(t: Fraction, N: int, order: int = 4, prec: int = 200, **fault):
    """Rigorous-side upper bound on |zeta(s) - main term|, from the Arb ball of zeta.

    The main term is evaluated in mpmath at 60 digits; its own rounding error is
    below 1e-50 and is added explicitly, so the returned number bounds the true
    defect provided Arb's ball is correct.
    """
    with mp.workdps(60):
        s = s_of(t)
        M = em4_main(s, N, **fault) if order == 4 else em2_main(s, N)
        rlo, rhi, ilo, ihi = zeta_arb(t, prec)
        dre = max(abs(rlo - mpmath.re(M)), abs(rhi - mpmath.re(M)))
        dim = max(abs(ilo - mpmath.im(M)), abs(ihi - mpmath.im(M)))
        return mpmath.sqrt(dre**2 + dim**2) + mpmath.mpf(10) ** -50


def decision(a: Fraction, b: Fraction, N: int, order: int = 4) -> dict:
    """The sign test with the truncation error as slack.

    Re(zeta_a conj zeta_b) <= Re(M_a conj M_b) + |M_a| E_b + |M_b| E_a + E_a E_b,
    so the test passes when the right side is negative. `margin` is
    -Re(M_a conj M_b) / slack: the factor by which the remainder could grow
    before the test fails.
    """
    with mp.workdps(40):
        sa, sb = s_of(a), s_of(b)
        main, bound = (em4_main, em4_bound) if order == 4 else (em2_main, em2_bound)
        Ma, Mb = main(sa, N), main(sb, N)
        Ea, Eb = bound(sa, N), bound(sb, N)
        reX = mpmath.re(Ma * mpmath.conj(Mb))
        slack = abs(Ma) * Eb + abs(Mb) * Ea + Ea * Eb
        return {
            "N": N,
            "order": order,
            "re_main_product": float(reX),
            "slack": float(slack),
            "bound_a": float(Ea),
            "bound_b": float(Eb),
            "passes": bool(reX + slack < 0),
            "margin": float(-reX / slack) if reX < 0 else 0.0,
        }


def min_N(a: Fraction, b: Fraction, order: int = 4, margin: float = 1.0, n_max: int = 4000) -> int:
    """Smallest truncation at which the sign test passes with the given margin.

    The same test as :func:`decision`, with the partial sums carried forward so the
    scan is linear in ``n_max`` rather than quadratic.
    """
    with mp.workdps(40):
        sa, sb = s_of(a), s_of(b)
        bound = em4_bound if order == 4 else em2_bound
        Pa = Pb = mpmath.mpf(0)
        for N in range(1, n_max + 1):
            if N >= 3:
                Ma = Pa + mpmath.power(N, 1 - sa) / (sa - 1) + mpmath.power(N, -sa) / 2
                Mb = Pb + mpmath.power(N, 1 - sb) / (sb - 1) + mpmath.power(N, -sb) / 2
                if order == 4:
                    Ma += sa * mpmath.power(N, -sa - 1) / 12
                    Mb += sb * mpmath.power(N, -sb - 1) / 12
                Ea, Eb = bound(sa, N), bound(sb, N)
                reX = mpmath.re(Ma * mpmath.conj(Mb))
                slack = abs(Ma) * Eb + abs(Mb) * Ea + Ea * Eb
                if reX + slack < 0 and -reX / slack >= margin:
                    return N
            Pa += mpmath.power(N, -sa)
            Pb += mpmath.power(N, -sb)
    raise ValueError("no truncation up to n_max decides the sign")


def trade_table(digits=(2, 3, 4, 5, 6), margins=(1, 2, 4, 10)) -> list[dict]:
    """Decimals of gamma_1 pinned versus terms needed (order 4)."""
    rows = []
    with mp.workdps(40):
        g1 = mpmath.findroot(mpmath.siegelz, mpmath.mpf(GAMMA_1))
        for k in digits:
            lo = Fraction(int(mpmath.floor(g1 * 10**k)), 10**k)
            hi = lo + Fraction(1, 10**k)
            rows.append({
                "digits": k,
                "a": str(lo),
                "b": str(hi),
                "Z_a": float(mpmath.siegelz(mpmath.mpf(lo.numerator) / lo.denominator)),
                "Z_b": float(mpmath.siegelz(mpmath.mpf(hi.numerator) / hi.denominator)),
                "N_for_margin": {str(m): min_N(lo, hi, 4, m) for m in margins},
            })
    return rows


# ---------------------------------------------------------------------------
# 2. Endpoint values of Z, two backends
# ---------------------------------------------------------------------------


def z_enclosure(t: Fraction, backend: str, prec_bits: int = 128) -> tuple:
    lo, hi = rigor.enclose_Z(t, prec_bits, backend=backend)
    return float(lo), float(hi)


def theta_increment(a: Fraction, b: Fraction) -> float:
    with mp.workdps(30):
        fa = mpmath.mpf(a.numerator) / a.denominator
        fb = mpmath.mpf(b.numerator) / b.denominator
        return float(mpmath.siegeltheta(fb) - mpmath.siegeltheta(fa))


# ---------------------------------------------------------------------------
# 3. The phase window from Euler's limit
# ---------------------------------------------------------------------------


def phase_partial(a: Fraction, b: Fraction, n: int) -> float:
    """phi_n = delta log pi - delta log n + sum_{j=0}^{n} arctan(delta c_j / (c_j^2 + alpha beta)).

    This is the argument of pi^{i delta} GammaSeq(1/4 + i a/2, n) GammaSeq(1/4 - i b/2, n),
    with alpha = a/2, beta = b/2, delta = beta - alpha, c_j = j + 1/4.
    """
    with mp.workdps(30):
        al = mpmath.mpf(a.numerator) / a.denominator / 2
        be = mpmath.mpf(b.numerator) / b.denominator / 2
        d = be - al
        K = al * be
        acc = d * mpmath.log(mpmath.pi) - d * mpmath.log(n)
        for j in range(n + 1):
            c = j + mpmath.mpf(1) / 4
            acc += mpmath.atan(d * c / (c * c + K))
        return float(acc)


def phase_window(a: Fraction, b: Fraction) -> dict:
    """The window [lower, upper] that every phi_n (n >= 1) lies in, by the derivation.

    upper = delta (log pi + 5): arctan x <= x, c_j/(c_j^2+K) <= 1/c_j, and
            sum_{j=0}^{n} 1/c_j <= 4 + H_n <= 5 + log n.
    lower = delta (log pi - 1 - 2K) - 66 delta^3: arctan x >= x - x^3,
            c/(c^2+K) >= 1/c - K/c^3, sum_{j=1}^{n} 1/c_j >= H_{n+1} - 1 >= log n - 1,
            sum_{j>=1} 1/c_j^3 <= sum 1/j^2 <= 2, and sum_j x_j^3 <= delta^3 (64 + 2).
    The crude Lean-friendly forms replace log pi by its bounds 0 <= log pi <= pi - 1.
    """
    with mp.workdps(30):
        al = mpmath.mpf(a.numerator) / a.denominator / 2
        be = mpmath.mpf(b.numerator) / b.denominator / 2
        d = be - al
        K = al * be
        lp = mpmath.log(mpmath.pi)
        upper = d * (lp + 5)
        lower = d * (lp - 1 - 2 * K) - 66 * d**3
        upper_crude = d * (mpmath.pi - 1 + 5)
        lower_crude = d * (-1 - 2 * K) - 66 * d**3
        return {
            "delta": float(d),
            "K": float(K),
            "upper": float(upper),
            "lower": float(lower),
            "upper_crude": float(upper_crude),
            "lower_crude": float(lower_crude),
            "half_pi": float(mpmath.pi / 2),
            "cos_floor": float(mpmath.cos(max(abs(lower_crude), abs(upper_crude)))),
        }


# ---------------------------------------------------------------------------
# 4. The box arithmetic, through the lab's bit-exact mirror
# ---------------------------------------------------------------------------


def load_mirror():
    """`scripts/61_rung3_mirror.py`, imported read-only (its name starts with a digit)."""
    path = ROOT / "scripts" / "61_rung3_mirror.py"
    spec = importlib.util.spec_from_file_location("rung3_mirror_for_hardy", path)
    mod = importlib.util.module_from_spec(spec)
    old = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.dont_write_bytecode = old
    return mod


def mirror_main_box(t: Fraction, N: int, nLog=40, nExp=24, p=96, kE=8, mirror=None):
    """Rectangle box for the order-4 main term at s = 1/2 + i t, mirror arithmetic.

    The main term is sum_{m<N} m^{-s} + N^{-s} * c_N with the exact Gaussian
    rational c_N = N/(s-1) + 1/2 + s/(12N), since N^{1-s} = N * N^{-s} and
    N^{-s-1} = N^{-s} / N. Every m^{-s} is the mirror's `dirichletTermBox2`
    (one log/exp tower per m, no composite chains: N is small).
    """
    M = mirror or load_mirror()
    S = M.cexact(Fraction(1, 2), t)
    acc = M.cexact(0, 0)
    boxes = {}
    for m in range(1, N + 1):
        if m == 1:
            box = M.cexact(1, 0)
        else:
            box = M.dirichletTermBox2(nLog, nExp, p, m.bit_length(), kE, m, S)
        boxes[m] = box
        if m < N:
            acc = M.cadd(acc, box)
    # c_N = N/(s-1) + 1/2 + s/(12 N), exactly
    sre, sim = Fraction(1, 2), Fraction(t)
    den = (sre - 1) ** 2 + sim**2
    inv_re, inv_im = (sre - 1) / den, -sim / den
    c_re = N * inv_re + Fraction(1, 2) + sre / (12 * N)
    c_im = N * inv_im + sim / (12 * N)
    acc = M.cadd(acc, M.cmul(boxes[N], M.cexact(c_re, c_im)))
    return acc, boxes


def mirror_sizing(a: Fraction = A, b: Fraction = B, N: int = N_PLAN, **params) -> dict:
    """Run the sign test on mirror boxes, inflated by the order-4 remainder bound."""
    M = load_mirror()
    Ba, ta = mirror_main_box(a, N, mirror=M, **params)
    Bb, tb = mirror_main_box(b, N, mirror=M, **params)
    with mp.workdps(40):
        Ea = em4_bound(s_of(a), N)
        Eb = em4_bound(s_of(b), N)
    # a rational upper bound on each remainder, rounded up at 1e-12
    ra = Fraction(int(mpmath.ceil(Ea * 10**12)), 10**12)
    rb = Fraction(int(mpmath.ceil(Eb * 10**12)), 10**12)
    Ia, Ib = M.cinflate(Ba, ra), M.cinflate(Bb, rb)
    # upper end of Re(z_a conj z_b) = x_a x_b + y_a y_b over the boxes
    prod = M.iadd(M.imul(Ia.re, Ib.re), M.imul(Ia.im, Ib.im))
    width = lambda B_: max(B_.re.hi - B_.re.lo, B_.im.hi - B_.im.lo)  # noqa: E731
    bits = max(
        max(x.numerator.bit_length(), x.denominator.bit_length())
        for box in list(ta.values()) + list(tb.values())
        for x in (box.re.lo, box.re.hi, box.im.lo, box.im.hi)
    )
    return {
        "N": N,
        "params": {"nLog": 40, "nExp": 24, "p": 96, "kE": 8, **params},
        "box_width_a": float(width(Ba)),
        "box_width_b": float(width(Bb)),
        "max_term_width": float(max(width(x) for x in list(ta.values()) + list(tb.values()))),
        "remainder_a": float(ra),
        "remainder_b": float(rb),
        "re_product_upper": float(prod.hi),
        "re_product_lower": float(prod.lo),
        "passes": bool(prod.hi < 0),
        "max_endpoint_bits": int(bits),
    }


# ---------------------------------------------------------------------------
# 5. The scales behind two dead routes (MISSION.md)
# ---------------------------------------------------------------------------


def dead_route_scales(t: Fraction = A) -> dict:
    """|Gamma(1/4 + it/2)|, Lambda(1/2 + it) and the size of Riemann's theta integral.

    The integral-for-Gamma-prime route compares an absolute bound of order one with
    |Gamma|; the quadrature route must resolve Lambda from an integrand whose
    absolute integral, int_1^inf psi(x) x^(-3/4) dx with psi(x) = sum_n exp(-pi n^2 x),
    is five orders of magnitude larger.
    """
    with mp.workdps(20):
        tt = mpmath.mpf(t.numerator) / t.denominator
        s = mpmath.mpc(mpmath.mpf(1) / 2, tt)
        lam = mpmath.pi ** (-s / 2) * mpmath.gamma(s / 2) * mpmath.zeta(s)
        psi = lambda x: mpmath.nsum(lambda n: mpmath.exp(-mpmath.pi * n * n * x), [1, mpmath.inf])  # noqa: E731
        return {
            "abs_gamma_quarter": float(abs(mpmath.gamma(mpmath.mpc(mpmath.mpf(1) / 4, tt / 2)))),
            "lambda_real": float(mpmath.re(lam)),
            "lambda_imag_abs": float(abs(mpmath.im(lam))),
            "theta_integral_scale": float(mpmath.quad(lambda x: psi(x) * x ** (-0.75), [1, mpmath.inf])),
        }


# ---------------------------------------------------------------------------


def collect() -> dict:
    with mp.workdps(30):
        za = z_enclosure(A, "python-flint")
        zb = z_enclosure(B, "python-flint")
        za_iv = z_enclosure(A, "mpmath.iv")
        zb_iv = z_enclosure(B, "mpmath.iv")
        out = {
            "a": str(A),
            "b": str(B),
            "Z_a_arb": za,
            "Z_b_arb": zb,
            "Z_a_iv": za_iv,
            "Z_b_iv": zb_iv,
            "Zprime_gamma1": float(mpmath.diff(mpmath.siegelz, mpmath.findroot(mpmath.siegelz, GAMMA_1))),
            "theta_increment": theta_increment(A, B),
            "decision_order4": {str(n): decision(A, B, n, 4) for n in (15, 21, 27, N_PLAN)},
            "decision_order2": {str(n): decision(A, B, n, 2) for n in (30, 500)},
            "min_N_order4": {str(m): min_N(A, B, 4, m) for m in (1, 2, 4, 10)},
            "min_N_order2": {str(m): min_N(A, B, 2, m) for m in (1,)},
            "em4_defect_vs_bound": {
                str(n): {
                    "defect_upper_a": float(em_error_upper(A, n)),
                    "bound_a": float(em4_bound(s_of(A), n)),
                    "defect_upper_b": float(em_error_upper(B, n)),
                    "bound_b": float(em4_bound(s_of(B), n)),
                }
                for n in (10, 20, N_PLAN)
            },
            "phase_window": phase_window(A, B),
            "phase_partials": {str(n): phase_partial(A, B, n) for n in (1, 10, 100, 1000)},
            "trade_table": trade_table(),
            "mirror": mirror_sizing(),
            "dead_route_scales": dead_route_scales(),
        }
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--no-write", action="store_true")
    args = ap.parse_args(argv)
    out = collect()
    print(json.dumps(out, indent=2))
    if not args.no_write:
        (HERE / "artifacts").mkdir(exist_ok=True)
        (HERE / "artifacts" / "sizing.json").write_text(json.dumps(out, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
