"""Arb enclosures for the explicit-formula bounds of RESULTS.md, sections 1 to 4.

Every function here returns python-flint ``arb`` balls.  A bound is accepted
only when the *lower* endpoint of the enclosed margin is positive, so a
rounding error can make a check fail but cannot make it pass.

Notation follows RESULTS.md.  ``theta`` is the zero-free abscissa (7/8 for
OpenAI's Theorem 1.1; other values are ablation controls), ``c`` is the weight
parameter in w(t) = t^c log(1/t), whose Mellin transform is W(s) = 1/(s+c)^2,
and sigma0 = 2 theta + c is the Hadamard comparison point.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from flint import arb, arb_series, ctx

PREC = 160


def _q(r) -> arb:
    """Exact rational -> arb ball."""
    r = Fraction(r)
    return arb(r.numerator) / arb(r.denominator)


def _zeta_taylor(s: arb, n: int = 3):
    """Taylor coefficients of zeta(s + x) at x = 0, as arb balls."""
    ser = arb_series([s, 1], prec=n).zeta()
    return [ser[k] for k in range(n)]


def logderiv_zeta(s: arb) -> tuple[arb, arb]:
    """(zeta'/zeta(s), (zeta'/zeta)'(s)) at a real point s != 1."""
    z0, z1, z2 = _zeta_taylor(s, 3)
    f = z1 / z0
    return f, 2 * z2 / z0 - f * f


def digamma(z: arb) -> arb:
    """psi(z) for real z, using psi(z) = psi(z+1) - 1/z below 1/2."""
    if z < arb("0.5"):
        return digamma(z + 1) - 1 / z
    return z.digamma()


def trigamma(z: arb) -> arb:
    """psi'(z) for real z, using psi'(z) = psi'(z+1) + 1/z^2 below 1/2."""
    if z < arb("0.5"):
        return trigamma(z + 1) + 1 / (z * z)
    ser = arb_series([z, 1], prec=3).lgamma()
    return 2 * ser[2]


@dataclass(frozen=True)
class Constants:
    """The fixed analytic constants of the master inequality (RESULTS.md 1.4)."""

    theta: Fraction
    c: Fraction
    W1: arb  # W(1) = 1/(1+c)^2
    sigma0: arb  # 2 theta + c
    A_chi: arb  # -zeta'/zeta(sigma0) - log(pi)/2 + psi((sigma0+1)/2)/2
    A_zeta: arb  # sum over zeta zeros of Re 1/(sigma0 - rho)
    K_inf: arb  # 1/(theta + c)
    L_star: arb  # K(x) = K_inf once log x >= L_star
    R1: arb  # |F_chi(-c)| <= log q + R1
    R2: arb  # |F_chi'(-c)| <= R2
    Fz: arb  # -zeta'/zeta(-c)
    Fz1: arb  # -(zeta'/zeta)'(-c)
    w_max: arb  # max of t^c log(1/t) = 1/(c e)


def constants(theta=Fraction(7, 8), c=Fraction(1, 4), prec: int = PREC) -> Constants:
    theta, c = Fraction(theta), Fraction(c)
    if not (Fraction(1, 2) <= theta < 1 and 0 < c < 1):
        raise ValueError("need 1/2 <= theta < 1 and 0 < c < 1")
    old = ctx.prec
    ctx.prec = prec
    try:
        th, cc = _q(theta), _q(c)
        pi = arb.pi()
        logpi = pi.log()
        sigma0 = 2 * th + cc
        W1 = 1 / ((1 + cc) ** 2)
        lz, _ = logderiv_zeta(sigma0)
        A_chi = -lz - logpi / 2 + digamma((sigma0 + 1) / 2) / 2
        A_zeta = 1 / sigma0 + 1 / (sigma0 - 1) - logpi / 2 + digamma(sigma0 / 2) / 2 + lz
        K_inf = 1 / (th + cc)
        b_lo = 1 - th
        g_lo = 1 / (2 * th + cc - b_lo) + 2 / (b_lo + cc)
        g_hi = 3 / (th + cc)
        L_star = g_lo if g_lo > g_hi else g_hi
        if not (g_lo > g_hi or g_hi > g_lo):
            L_star = g_lo + g_hi  # overlap: take a safe upper bound
        lz1, dlz1 = logderiv_zeta(1 + cc)
        X = []
        Y = []
        for a in (0, 1):
            X.append(-logpi + digamma((a - cc) / 2) / 2 + digamma((1 + a + cc) / 2) / 2)
            Y.append(trigamma((a - cc) / 2) / 4 + trigamma((1 + a + cc) / 2) / 4)
        R1 = -lz1 + _amax([abs(v) for v in X])
        R2 = dlz1 + _amax(Y)
        lzm, dlzm = logderiv_zeta(-cc)
        w_max = 1 / (cc * arb(1).exp())
        return Constants(theta, c, W1, sigma0, A_chi, A_zeta, K_inf, L_star, R1, R2,
                         -lzm, -dlzm, w_max)
    finally:
        ctx.prec = old


def _amax(vals):
    """Upper bound for the max of arb balls (componentwise upper endpoints)."""
    best = vals[0]
    for v in vals[1:]:
        best = arb(max(best.upper(), v.upper()))
    return arb(best.upper())


def K_of_x(C: Constants, logx: arb, pieces: int = 400) -> arb:
    """Upper bound for K(x) = sup_{1-theta<=b<=theta} x^(b-theta)(sigma0-b)/(b+c)^2.

    Once log x >= L_star the supremum is attained at b = theta (RESULTS.md,
    Lemma 2) and equals 1/(theta+c).  Below that, a monotone bound on each of
    ``pieces`` subintervals is used: x^(b-theta) increases, the other factor
    decreases, so the top endpoint of the first and the bottom endpoint of the
    second bound the piece.
    """
    if logx >= C.L_star:
        return C.K_inf
    th, cc = _q(C.theta), _q(C.c)
    lo = 1 - th
    width = (2 * th - 1) / pieces
    best = arb(0)
    for i in range(pieces):
        b0 = lo + width * i
        b1 = b0 + width
        val = ((b1 - th) * logx).exp() * (C.sigma0 - b0) / (b0 + cc) ** 2
        best = arb(max(best.upper(), val.upper()))
    return arb(best.upper())


def margin(C: Constants, x: arb, logq: arb, omega_x: arb) -> arb:
    """Phi(x, q): the master-inequality margin of RESULTS.md (1.9).

    ``logq`` may be any upper bound for log q; ``omega_x`` any upper bound for
    the number of primes p | q with p <= x.  If the returned ball is strictly
    positive, every nonprincipal character mod q takes a value outside {0, 1}
    at some prime p <= x.
    """
    th, cc = _q(C.theta), _q(C.c)
    logx = x.log()
    K = K_of_x(C, logx)
    x_th = (th * logx).exp()
    x_mc = (-cc * logx).exp()
    zero_terms = x_th * K * (logq / 2 + C.A_chi + C.A_zeta)
    xm2 = 1 / (x * x)
    T_chi_a0 = 1 / (cc * cc) + xm2 / ((2 - cc) ** 2 * (1 - xm2))
    T_chi_a1 = (1 / x) / ((1 - cc) ** 2 * (1 - xm2))
    T_chi = arb(max(T_chi_a0.upper(), T_chi_a1.upper()))
    T_zeta = xm2 / ((2 - cc) ** 2 * (1 - xm2))
    R_chi = x_mc * (C.R2 + (logq + C.R1) * logx)
    R_zeta = x_mc * (abs(C.Fz1) + abs(C.Fz) * logx)
    E_q = 2 * omega_x * logx * C.w_max
    return x * C.W1 - zero_terms - T_chi - T_zeta - R_chi - R_zeta - E_q


def margin_closed(C: Constants, L: arb, kappa: arb = arb(1)) -> arb:
    """Margin at x = (kappa L)^8-type point x = (kappa*L)^(1/(1-theta)), log q = L.

    Uses omega(q) <= log q / log 2.  Returns Phi / x, the normalised margin.
    """
    exponent = 1 / (1 - _q(C.theta))
    x = ((kappa * L).log() * exponent).exp()
    omega = L / arb(2).log()
    return margin(C, x, L, omega) / x


def sieve_factor(primes_of_pm1: list[int], j: int) -> Fraction | None:
    """Cohen-Huczynska sieve factor for core e = first j primes of rad(p-1).

    Returns Lambda with: if S0 > Lambda * E then a prime primitive root <= x
    exists (RESULTS.md, Lemma 7).  None when delta <= 0.
    """
    ps = sorted(primes_of_pm1)
    s = len(ps) - j
    Om = 2 ** j
    if s == 0:
        return Fraction(Om - 1)
    delta = 1 - sum(Fraction(1, p) for p in ps[j:])
    if delta <= 0:
        return None
    return Fraction(2 * Om - 1) + Fraction((s - 1) * (3 * Om - 2)) / delta


def best_sieve_factor(primes_of_pm1: list[int]) -> Fraction:
    vals = [v for j in range(len(primes_of_pm1) + 1)
            if (v := sieve_factor(primes_of_pm1, j)) is not None]
    return min(vals)


def primroot_margin(C: Constants, x: arb, logp: arb, lam: arb, p_le_x: bool) -> arb:
    """S0_low - lam * E_up for the prime modulus p (RESULTS.md, Theorem 3)."""
    th, cc = _q(C.theta), _q(C.c)
    logx = x.log()
    K = K_of_x(C, logx)
    x_th = (th * logx).exp()
    x_mc = (-cc * logx).exp()
    xm2 = 1 / (x * x)
    T_zeta = xm2 / ((2 - cc) ** 2 * (1 - xm2))
    T_chi_a0 = 1 / (cc * cc) + xm2 / ((2 - cc) ** 2 * (1 - xm2))
    T_chi_a1 = (1 / x) / ((1 - cc) ** 2 * (1 - xm2))
    T_chi = arb(max(T_chi_a0.upper(), T_chi_a1.upper()))
    R_zeta = x_mc * (abs(C.Fz1) + abs(C.Fz) * logx)
    R_chi = x_mc * (C.R2 + (logp + C.R1) * logx)
    S0_low = x * C.W1 - x_th * K * C.A_zeta - T_zeta - R_zeta
    if p_le_x:
        S0_low = S0_low - logx * C.w_max
    E_up = x_th * K * (logp / 2 + C.A_chi) + T_chi + R_chi
    return S0_low - lam * E_up


def least_x(pred, lo: float = 2.0, hi: float = 1e40, steps: int = 60) -> float:
    """Smallest x on a bisection grid (in log x) where pred(x) is True.

    ``pred`` must be monotone (False below a threshold, True above); the
    returned float is a point where pred was verified True.
    """
    import math
    if not pred(hi):
        raise ValueError("predicate false at the top of the range")
    a, b = math.log(lo), math.log(hi)
    if pred(lo):
        return lo
    for _ in range(steps):
        m = (a + b) / 2
        if pred(math.exp(m)):
            b = m
        else:
            a = m
    return math.exp(b)


def quartic_kernel_c1(theta=Fraction(7, 8), c=Fraction(0)) -> tuple[arb, arb]:
    """Asymptotic constant for the kernel W(s) = (s + c)^-4 (RESULTS.md 2(c)).

    With D = theta + c and sigma0 = theta + D/sqrt(3), the supremum over gamma
    of |W(theta + i gamma)| / Re 1/(sigma0 - theta - i gamma) is
    3 sqrt(3)/(8 D^3), and c1 = (1 + c)^4 * 3 sqrt(3)/(16 D^3).  Returns
    (c1, c1^(1/(1-theta))).
    """
    th, cc = _q(theta), _q(c)
    D = th + cc
    c1 = (1 + cc) ** 4 * 3 * arb(3).sqrt() / (16 * D ** 3)
    return c1, c1 ** int(1 / (1 - Fraction(theta)))
