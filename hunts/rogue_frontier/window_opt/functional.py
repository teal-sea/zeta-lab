"""Closed forms for the windowed sine-kernel Gram moments m2(1,v), m3(1,v).

Context. The source paper (10 Aug 2026, "More than two thirds of the zeros of
the Riemann zeta function lie on the critical line", section 7.5(g)) runs its
distinct-zeros count under RH with a windowed Gram matrix whose limiting
moments are m_k(1, v), the k-th spectral moments of the sine-kernel Gram
matrix over the sine process shaped by an even window v >= 0 on [-1/2, 1/2].
The RH-conditional bound is

    Nd/N >= 1/2 + (2 m2 - m3)/18 + (4/9)(19/27),

so any admissible window increasing F(v) := 2 m2 - m3 lifts the constant by
delta F / 18.  The paper's window is v(s) = cos(8s/5), for which it prints
2 m2 - m3 = 0.68524...

Derivation (re-derived here from the determinantal structure; independently
validated three ways, see below).  Points x_j are the unit-density sine
process, S(x) = sin(pi x)/(pi x), correlations rho_2 = 1 - S^2 and
rho_3 = 1 - S12^2 - S13^2 - S23^2 + 2 S12 S13 S23.  The Gram kernel is
H_{jj'} = K_v(x_j - x_{j'}) with K_v(x) = int_{-1/2}^{1/2} v(xi)
e^{2 pi i x xi} d xi, and m_k = lim E tr H^k / (N l1^k), l1 = K_v(0) = int v.

Splitting E tr H^k over coincidence patterns of the index tuple and passing
every distinct-point integral to the Fourier side (Parseval; the transform of
the product S * K_v is the convolution 1_B * v, B = [-1/2, 1/2]):

    E tr H^2 / N = l1^2 + [ int v^2 - int W^2 ],           W := 1_B * v,
    E tr H^3 / N = l1^3 + 3 l1 [ int v^2 - int W^2 ]
                   + [ int v^3 - 3 int (tri * v) v^2 + 2 int W^3 ],

with tri := 1_B * 1_B the unit triangle.  Hence, with
    D2 := (int v^2 - int W^2) / l1^2,
    D3 := (int v^3 - 3 int (tri*v) v^2 + 2 int W^3) / l1^3,

    m2 = 1 + D2,      m3 = 1 + 3 D2 + D3,      F = 2 m2 - m3 = 1 - D2 - D3.

Sanity anchor v = 1: D2 = 1 - 2/3 = 1/3 and D3 = 1 - 2 + 1 = 0, giving
m2 = 4/3 and m3 = 2, the published sine-Gram values.  Every routine below is
additionally validated at the paper's window (all printed digits of 0.68524
reproduced) and against the exact finite-N windowed CUE lattice count
(crosscheck_finiteN.py in this directory).

Practical reductions used by the evaluators (v even):
    V0(x) = int_0^x v,  P0(x) = int_0^x t v(t) dt,
    W(eta) = V0(1/2) + V0(1/2 - eta)              for eta in [0, 1],
    (tri*v)(s) = l1 - A(s),  A(s) = 2 s V0(s) - 2 P0(s) + 2 P0(1/2),
valid on the stated ranges because |s - xi| <= 1 there.  For a polynomial v
these make every integrand a polynomial, so the Fraction route below is exact
rational arithmetic, and the Gauss-Legendre route is exact up to rounding.

Run `.venv/bin/python hunts/rogue_frontier/window_opt/functional.py` for the
validation battery.  Grades per the repo ladder: the closed forms are
hardened (two independent routes agree: continuum derivation and the exact
CUE lattice engine); individual numbers printed by the float engine are
measured; the Fraction route outputs are exact rational arithmetic.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache

import numpy as np

# ---------------------------------------------------------------------------
# reference windows
# ---------------------------------------------------------------------------

#: the paper's window v(s) = cos(C_PAPER * s)
C_PAPER = Fraction(8, 5)

#: the clean rational-coefficient window found by the optimization here:
#: v(s) = 1 + q1 s^2 + q2 s^4  (even, positive, nonincreasing on [0, 1/2])
OPT_Q = (Fraction(-1467, 1000), Fraction(1159, 1000))

#: 30-digit symbolic references (sympy exact closed forms, see _selftest)
PAPER_M2_30 = "1.32801844899962925344205522171"
PAPER_M3_30 = "1.97079302246194031086568955921"
PAPER_F_30 = "0.685243875537318196018420884208"


# ---------------------------------------------------------------------------
# float engine: composite Gauss-Legendre, vectorized, for even v >= 0
# ---------------------------------------------------------------------------

@lru_cache(maxsize=8)
def _gl01(n: int):
    x, w = np.polynomial.legendre.leggauss(n)
    return 0.5 * (x + 1.0), 0.5 * w


def moments_quad(v, ng: int = 64) -> dict:
    """m2, m3, F for a vectorized even callable v on [-1/2, 1/2].

    Exact up to rounding when v is a polynomial of degree < 2*ng - 1;
    superalgebraically convergent for analytic v.  Not reliable for windows
    with interior kinks (use moments_pwlinear_exact for those).
    """
    t, w01 = _gl01(ng)
    s = 0.5 * t
    ws = 0.5 * w01
    vs = v(s)
    l1 = 2.0 * np.dot(ws, vs)
    iv2 = 2.0 * np.dot(ws, vs ** 2)
    iv3 = 2.0 * np.dot(ws, vs ** 3)

    def _int0(f, x):
        x = np.atleast_1d(x)
        nod = np.outer(x, t)
        return (f(nod) @ w01) * x

    V0 = lambda x: _int0(v, x)
    P0 = lambda x: _int0(lambda u: u * v(u), x)
    V0h = V0(0.5)[0]
    P0h = P0(0.5)[0]

    def W(eta):
        arg = 0.5 - np.atleast_1d(eta)
        return V0h + np.sign(arg) * V0(np.abs(arg))

    Weta = W(t)
    iW2 = 2.0 * np.dot(w01, Weta ** 2)
    iW3 = 2.0 * np.dot(w01, Weta ** 3)

    A = 2.0 * s * V0(s) - 2.0 * P0(s) + 2.0 * P0h
    T = l1 - A
    iTv2 = 2.0 * np.dot(ws, T * vs ** 2)

    Q2 = iv2 - iW2
    Q3 = iv3 - 3.0 * iTv2 + 2.0 * iW3
    m2 = 1.0 + Q2 / l1 ** 2
    m3 = 1.0 + 3.0 * Q2 / l1 ** 2 + Q3 / l1 ** 3
    return {"l1": l1, "m2": m2, "m3": m3, "F": 2.0 * m2 - m3}


def gradient_field(v, ng: int = 64) -> dict:
    """First variation g(s) = delta F / delta v(s) on the half-grid.

    F is homogeneous of degree 0 in v, so int g v = 0 identically (returned
    as `euler`, a discretization check) and a critical point of F over
    {v >= 0} has g = 0 on the support of v, g <= 0 elsewhere.
    """
    t, w01 = _gl01(ng)
    s = 0.5 * t
    ws = 0.5 * w01
    vs = v(s)
    l1 = 2.0 * np.dot(ws, vs)
    iv2 = 2.0 * np.dot(ws, vs ** 2)
    iv3 = 2.0 * np.dot(ws, vs ** 3)

    def _int0(f, x):
        x = np.atleast_1d(x)
        nod = np.outer(x, t)
        return (f(nod) @ w01) * x

    V0 = lambda x: _int0(v, x)
    P0 = lambda x: _int0(lambda u: u * v(u), x)
    V20 = lambda x: _int0(lambda u: v(u) ** 2, x)
    P20 = lambda x: _int0(lambda u: u * v(u) ** 2, x)
    V0h, P0h = V0(0.5)[0], P0(0.5)[0]
    P20h = P20(0.5)[0]

    def W(eta):
        arg = 0.5 - np.atleast_1d(eta)
        return V0h + np.sign(arg) * V0(np.abs(arg))

    Weta = W(t)
    iW2 = 2.0 * np.dot(w01, Weta ** 2)
    iW3 = 2.0 * np.dot(w01, Weta ** 3)

    A = 2.0 * s * V0(s) - 2.0 * P0(s) + 2.0 * P0h
    T = l1 - A                                   # (tri * v)(s)
    A2 = 2.0 * s * V20(s) - 2.0 * P20(s) + 2.0 * P20h
    T2 = iv2 - A2                                # (tri * v^2)(s)
    iTv2 = 2.0 * np.dot(ws, T * vs ** 2)
    Q2 = iv2 - iW2
    Q3 = iv3 - 3.0 * iTv2 + 2.0 * iW3

    def U(x):                                    # int_0^x W^2
        x = np.atleast_1d(x)
        nod = np.outer(x, t)
        return (W(nod.ravel()).reshape(nod.shape) ** 2 @ w01) * x

    BW2 = U(s + 0.5) + U(0.5 - s)                # (1_B * W^2)(s)

    g = (-(2.0 * vs - 2.0 * T) / l1 ** 2 + 2.0 * Q2 / l1 ** 3
         - (3.0 * vs ** 2 - 3.0 * T2 - 6.0 * vs * T + 6.0 * BW2) / l1 ** 3
         + 3.0 * Q3 / l1 ** 4)
    euler = 2.0 * np.dot(ws, g * vs)
    m2 = 1.0 + Q2 / l1 ** 2
    m3 = 1.0 + 3.0 * Q2 / l1 ** 2 + Q3 / l1 ** 3
    return {"s": s, "w": ws, "g": g, "euler": euler,
            "m2": m2, "m3": m3, "F": 2.0 * m2 - m3, "l1": l1}


# ---------------------------------------------------------------------------
# exact evaluator for even piecewise-linear v (lattice-aligned panels)
# ---------------------------------------------------------------------------

def moments_pwlinear_exact(y) -> tuple:
    """(m2, m3, F) for the even pw-linear window with knot values y on the
    uniform grid s_i = i * h, h = 0.5/(len(y)-1), i = 0..len(y)-1.

    Every integrand is piecewise polynomial of degree <= 6 with breakpoints
    on the h-lattice, so per-cell 8-point Gauss-Legendre is exact up to
    rounding.  Antiderivatives V0 (pw quadratic) and P0 (pw cubic) are
    evaluated in closed form per cell.
    """
    y = np.asarray(y, dtype=float)
    n = len(y)
    h = 0.5 / (n - 1)
    s_kn = h * np.arange(n)
    slope = np.diff(y) / h
    Vk = np.concatenate([[0.0], np.cumsum(0.5 * (y[:-1] + y[1:]) * h)])
    Pk = np.zeros(n)
    for j in range(n - 1):
        a, b = s_kn[j], s_kn[j + 1]
        m = slope[j]
        Pk[j + 1] = Pk[j] + y[j] * (b * b - a * a) / 2 \
            + m * ((b ** 3 - a ** 3) / 3 - a * (b * b - a * a) / 2)

    def V0(x):
        x = np.atleast_1d(x)
        j = np.clip(((x - 1e-15) / h).astype(int), 0, n - 2)
        d = x - s_kn[j]
        return Vk[j] + y[j] * d + slope[j] * d * d / 2

    def P0(x):
        x = np.atleast_1d(x)
        j = np.clip(((x - 1e-15) / h).astype(int), 0, n - 2)
        a = s_kn[j]
        m = slope[j]
        return Pk[j] + y[j] * (x * x - a * a) / 2 \
            + m * ((x ** 3 - a ** 3) / 3 - a * (x * x - a * a) / 2)

    def vv(x):
        x = np.abs(np.atleast_1d(x))
        j = np.clip(((x - 1e-15) / h).astype(int), 0, n - 2)
        return y[j] + slope[j] * (x - s_kn[j])

    gx, gw = np.polynomial.legendre.leggauss(8)
    t8, w8 = 0.5 * (gx + 1.0), 0.5 * gw
    wc = h * w8

    l1h = Vk[-1]
    l1 = 2.0 * l1h
    cells0 = s_kn[:-1][:, None] + h * t8[None, :]
    vc = vv(cells0.ravel()).reshape(cells0.shape)
    iv2 = 2.0 * np.sum((vc ** 2) @ wc)
    iv3 = 2.0 * np.sum((vc ** 3) @ wc)
    x0 = cells0.ravel()
    Ac = (2 * x0 * V0(x0) - 2 * P0(x0) + 2 * Pk[-1]).reshape(cells0.shape)
    Tc = l1 - Ac
    iTv2 = 2.0 * np.sum((Tc * vc ** 2) @ wc)

    eta_kn = h * np.arange(2 * (n - 1) + 1)
    cells1 = eta_kn[:-1][:, None] + h * t8[None, :]
    arg = 0.5 - cells1.ravel()
    Wc = (l1h + np.sign(arg) * V0(np.abs(arg))).reshape(cells1.shape)
    iW2 = 2.0 * np.sum((Wc ** 2) @ wc)
    iW3 = 2.0 * np.sum((Wc ** 3) @ wc)

    Q2 = iv2 - iW2
    Q3 = iv3 - 3.0 * iTv2 + 2.0 * iW3
    m2 = 1.0 + Q2 / l1 ** 2
    m3 = 1.0 + 3.0 * Q2 / l1 ** 2 + Q3 / l1 ** 3
    return m2, m3, 2.0 * m2 - m3


# ---------------------------------------------------------------------------
# exact rational route for even polynomial windows (Fraction arithmetic,
# no sympy: an independent implementation of the same closed forms)
# ---------------------------------------------------------------------------

def _padd(p, q):
    n = max(len(p), len(q))
    p = list(p) + [Fraction(0)] * (n - len(p))
    q = list(q) + [Fraction(0)] * (n - len(q))
    return [a + b for a, b in zip(p, q)]


def _pscale(p, c):
    return [c * a for a in p]


def _pmul(p, q):
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return out


def _pint(p):
    """antiderivative with zero constant term"""
    return [Fraction(0)] + [a / (i + 1) for i, a in enumerate(p)]


def _peval(p, x: Fraction) -> Fraction:
    acc = Fraction(0)
    for a in reversed(p):
        acc = acc * x + a
    return acc


def _pcompose_affine(p, a: Fraction, b: Fraction):
    """p(a + b*x) as a polynomial in x (Horner in the affine argument)."""
    out = [Fraction(0)]
    for coef in reversed(p):
        out = _padd(_pmul(out, [a, b]), [coef])
    return out


def moments_polyeven_exact(qs) -> tuple:
    """Exact rational (m2, m3, F) for v(s) = 1 + sum_i qs[i] s^(2i+2)."""
    qs = [Fraction(q) for q in qs]
    v = [Fraction(1)]
    for i, q in enumerate(qs):
        v = _padd(v, [Fraction(0)] * (2 * i + 2) + [q])
    half = Fraction(1, 2)
    V0 = _pint(v)                       # odd polynomial, V0(0) = 0
    P0 = _pint(_pmul([Fraction(0), Fraction(1)], v))
    l1 = 2 * _peval(V0, half)
    iv2 = 2 * _peval(_pint(_pmul(v, v)), half)
    iv3 = 2 * _peval(_pint(_pmul(_pmul(v, v), v)), half)
    # W(eta) = V0(1/2) + V0(1/2 - eta), polynomial in eta on [0, 1]
    W = _padd([_peval(V0, half)], _pcompose_affine(V0, half, Fraction(-1)))
    iW2 = 2 * _peval(_pint(_pmul(W, W)), Fraction(1))
    iW3 = 2 * _peval(_pint(_pmul(_pmul(W, W), W)), Fraction(1))
    # A(s) = 2 s V0(s) - 2 P0(s) + 2 P0(1/2);  T = l1 - A
    A = _padd(_pscale(_pmul([Fraction(0), Fraction(1)], V0), Fraction(2)),
              _padd(_pscale(P0, Fraction(-2)), [2 * _peval(P0, half)]))
    T = _padd([l1], _pscale(A, Fraction(-1)))
    iTv2 = 2 * _peval(_pint(_pmul(T, _pmul(v, v))), half)
    Q2 = iv2 - iW2
    Q3 = iv3 - 3 * iTv2 + 2 * iW3
    m2 = 1 + Q2 / l1 ** 2
    m3 = 1 + 3 * Q2 / l1 ** 2 + Q3 / l1 ** 3
    return m2, m3, 2 * m2 - m3


# ---------------------------------------------------------------------------
# sympy routes (symbolic cross-check of both evaluators above)
# ---------------------------------------------------------------------------

def moments_polyeven_sympy(qs):
    """Exact sympy (m2, m3, F) for v(s) = 1 + sum_i qs[i] s^(2i+2)."""
    import sympy as sp
    s, eta = sp.symbols("s eta")
    v = 1 + sum(sp.Rational(Fraction(q)) * s ** (2 * (i + 1))
                for i, q in enumerate(qs))
    V0 = sp.integrate(v, s)
    P0 = sp.integrate(s * v, s)
    half = sp.Rational(1, 2)
    l1 = 2 * V0.subs(s, half)
    iv2 = 2 * sp.integrate(v ** 2, (s, 0, half))
    iv3 = 2 * sp.integrate(v ** 3, (s, 0, half))
    W = V0.subs(s, half) + V0.subs(s, half - eta)
    iW2 = 2 * sp.integrate(W ** 2, (eta, 0, 1))
    iW3 = 2 * sp.integrate(W ** 3, (eta, 0, 1))
    A = 2 * s * V0 - 2 * P0 + 2 * P0.subs(s, half)
    T = l1 - A
    iTv2 = 2 * sp.integrate(sp.expand(T * v ** 2), (s, 0, half))
    Q2 = iv2 - iW2
    Q3 = iv3 - 3 * iTv2 + 2 * iW3
    m2 = sp.together(1 + Q2 / l1 ** 2)
    m3 = sp.together(1 + 3 * Q2 / l1 ** 2 + Q3 / l1 ** 3)
    return m2, m3, sp.together(2 * m2 - m3)


def moments_cos_sympy(c_num: int, c_den: int):
    """Exact sympy (m2, m3, F) for v(s) = cos(c s), c = c_num/c_den."""
    import sympy as sp
    s, eta = sp.symbols("s eta")
    C = sp.Rational(c_num, c_den)
    v = sp.cos(C * s)
    V0 = sp.sin(C * s) / C
    P0 = (sp.cos(C * s) - 1) / C ** 2 + s * sp.sin(C * s) / C
    # antiderivative identities used everywhere below; verify them
    assert sp.simplify(sp.diff(V0, s) - v) == 0
    assert sp.simplify(sp.diff(P0, s) - s * v) == 0
    half = sp.Rational(1, 2)
    l1 = 2 * V0.subs(s, half)
    iv2 = 2 * sp.integrate(v ** 2, (s, 0, half))
    iv3 = 2 * sp.integrate(v ** 3, (s, 0, half))
    W = V0.subs(s, half) + V0.subs(s, half - eta)
    iW2 = 2 * sp.integrate(sp.expand_trig(W ** 2), (eta, 0, 1))
    iW3 = 2 * sp.integrate(sp.expand_trig(W ** 3), (eta, 0, 1))
    A = 2 * s * V0 - 2 * P0 + 2 * P0.subs(s, half)
    T = l1 - A
    iTv2 = 2 * sp.integrate(sp.expand_trig(sp.expand(T * v ** 2)),
                            (s, 0, half))
    Q2 = sp.simplify(iv2 - iW2)
    Q3 = sp.simplify(iv3 - 3 * iTv2 + 2 * iW3)
    m2 = 1 + Q2 / l1 ** 2
    m3 = 1 + 3 * Q2 / l1 ** 2 + Q3 / l1 ** 3
    return m2, m3, sp.simplify(2 * m2 - m3)


# ---------------------------------------------------------------------------
# validation battery
# ---------------------------------------------------------------------------

def _selftest() -> None:
    import sympy as sp

    print("== validation battery: m2(1,v), m3(1,v) closed forms ==")

    # 1. v = 1 must give the published sine-Gram moments 4/3 and 2 on every route
    r = moments_quad(lambda s: np.ones_like(s))
    assert abs(r["m2"] - 4 / 3) < 1e-14 and abs(r["m3"] - 2.0) < 1e-14, r
    m2, m3, F = moments_pwlinear_exact(np.ones(41))
    assert abs(m2 - 4 / 3) < 1e-13 and abs(m3 - 2.0) < 1e-13
    m2r, m3r, Fr = moments_polyeven_exact([Fraction(0)])
    assert (m2r, m3r, Fr) == (Fraction(4, 3), Fraction(2), Fraction(2, 3))
    print("v = 1: quad, pw-exact and Fraction routes all give (4/3, 2, 2/3)")

    # 2. paper window cos(8s/5): float engine vs 30-digit symbolic reference
    rp = moments_quad(lambda s: np.cos(1.6 * s))
    for key, ref in (("m2", PAPER_M2_30), ("m3", PAPER_M3_30),
                     ("F", PAPER_F_30)):
        assert abs(rp[key] - float(ref)) < 1e-13, (key, rp[key], ref)
    print(f"cos(8s/5): quad engine m2={rp['m2']:.15f} m3={rp['m3']:.15f}")
    print(f"           F=2m2-m3={rp['F']:.15f}  (paper prints 0.68524...)")

    # 3. paper window: full symbolic derivation reproduces the same digits
    m2s, m3s, Fs = moments_cos_sympy(8, 5)
    for expr, ref in ((m2s, PAPER_M2_30), (m3s, PAPER_M3_30), (Fs, PAPER_F_30)):
        got = sp.N(expr, 30)
        assert str(got)[:22] == ref[:22], (got, ref)
    print("cos(8s/5): sympy closed forms reproduce the 30-digit references")
    print("           F closed form:", sp.simplify(Fs))

    # 4. rational quartic window: Fraction route == sympy route exactly
    m2r, m3r, Fr = moments_polyeven_exact(OPT_Q)
    m2y, m3y, Fy = moments_polyeven_sympy(OPT_Q)
    assert sp.Rational(m2r.numerator, m2r.denominator) == sp.nsimplify(m2y)
    assert sp.Rational(m3r.numerator, m3r.denominator) == sp.nsimplify(m3y)
    assert sp.Rational(Fr.numerator, Fr.denominator) == sp.nsimplify(Fy)
    print(f"quartic window {tuple(map(str, OPT_Q))}:")
    print(f"  m2 = {m2r} = {float(m2r):.15f}")
    print(f"  m3 = {m3r} = {float(m3r):.15f}")
    print(f"  F  = {Fr} = {float(Fr):.15f}")
    print("  Fraction route and sympy route agree exactly")

    # 5. float engine agrees with the exact rationals (quartic is polynomial,
    #    so Gauss-Legendre is exact up to rounding here)
    vq = lambda s: 1.0 + float(OPT_Q[0]) * s ** 2 + float(OPT_Q[1]) * s ** 4
    rq = moments_quad(vq)
    assert abs(rq["m2"] - float(m2r)) < 1e-14
    assert abs(rq["m3"] - float(m3r)) < 1e-14
    print("  quad engine matches the exact rationals to < 1e-14")

    # 6. pw-linear exact evaluator, sampling the quartic on 41 knots:
    #    O(h^2) interpolation bias only, must sit within 1e-7
    sg = np.linspace(0.0, 0.5, 41)
    m2p, m3p, Fp = moments_pwlinear_exact(vq(sg))
    assert abs(Fp - float(Fr)) < 1e-7, (Fp, float(Fr))
    print(f"  pw-linear(41) sampling bias: {Fp - float(Fr):+.2e} (expected O(h^2))")

    # 7. gradient field: Euler identity (int g v = 0, homogeneity degree 0)
    #    and finite-difference agreement in four directions
    gf = gradient_field(lambda s: np.cos(1.6 * s))
    assert abs(gf["euler"]) < 1e-12, gf["euler"]
    for j in range(4):
        d = lambda s, j=j: np.cos(2 * np.pi * j * s)
        eps = 1e-6
        Fp_ = moments_quad(lambda s: np.cos(1.6 * s) + eps * d(s))["F"]
        Fm_ = moments_quad(lambda s: np.cos(1.6 * s) - eps * d(s))["F"]
        fd = (Fp_ - Fm_) / (2 * eps)
        an = 2.0 * np.dot(gf["w"], gf["g"] * d(gf["s"]))
        assert abs(fd - an) < 5e-7 * max(1.0, abs(fd)), (j, fd, an)
    print("gradient field: Euler identity and 4 finite-difference checks pass")

    print("== all validations pass ==")


if __name__ == "__main__":
    _selftest()
