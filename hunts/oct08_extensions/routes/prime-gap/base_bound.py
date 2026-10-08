"""Arb enclosures for the smoothed explicit-formula bound of RESULTS.md.

Every numbered quantity here is defined in RESULTS.md (section 2 for the
weight, section 3 for the zero sums, section 4 for the interval bound,
section 5 for the tails).  Functions return arb balls; the caller decides
with ``.upper()`` or with certain comparisons only.

External inputs, cited in RESULTS.md section 1:

* H0 = 3 000 175 332 800: Platt and Trudgian, Bull. LMS 53 (2021) 792-797,
  Theorem 1 (every zero with 0 < gamma <= H0 has beta = 1/2).
* N(T) remainder: coefficientwise maximum of Rosser (1941) and of the second
  estimate of Bellotti and Wong, arXiv:2412.15470v2, Theorem 1.1, both in the
  form |N(T) - (T/2pi) log(T/(2 pi e))| <= C1 log T + C2 log log T + C3 for
  T >= e (Rosser's row as tabulated in Bellotti-Wong Table 1).
* The zero-free half-plane: OpenAI, The Quasi-Riemann Hypothesis (2026),
  Theorem 1.1, beta <= theta with theta = 7/8; theta is a parameter here so
  that the weakened control theta = 15/16 runs through the same code.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from flint import arb, ctx

PREC = 256

H0 = 3000175332800
ROSSER = (Fraction(137, 1000), Fraction(443, 1000), Fraction(2463, 1000))
BELLOTTI_WONG_2 = (Fraction(11200, 100000), Fraction(12567, 100000),
                   Fraction(377417, 100000))
C1, C2, C3 = (max(r, b) for r, b in zip(ROSSER, BELLOTTI_WONG_2))

# Weight: phi = quadratic B-spline on [0, 1] (RESULTS.md section 2).
# Envelope of |W(rho)| / (h x^(beta-1)) in u = gamma*eta/(1+eta):
#   g(u) = min(1, (9/2)/u, 216/u^3);  the m = 2 bound 36/u^2 is never smaller.
PHI_MAX = Fraction(9, 4)
U1 = Fraction(9, 2)          # end of the flat piece
C_M1 = Fraction(9, 2)        # ||phi'||_1
C_M3 = 216                   # total variation of phi''


def a_(q) -> arb:
    """Exact rational (or int) as an arb ball containing it."""
    q = Fraction(q)
    return arb(q.numerator) / arb(q.denominator)


def U2() -> arb:
    """Crossover (9/2)/u = 216/u^3, u = sqrt(48) = 4 sqrt(3)."""
    return arb(48).sqrt()


def L0() -> arb:
    """log(2 pi e)."""
    return (2 * arb.pi()).log() + 1


def R(t: arb) -> arb:
    return a_(C1) * t.log() + a_(C2) * t.log().log() + a_(C3)


def N_plus(t: arb) -> arb:
    """Upper bound for N(t), t >= e."""
    return t / (2 * arb.pi()) * (t.log() - L0()) + R(t)


def N_minus(t: arb) -> arb:
    """Lower bound for N(t), t >= e."""
    return t / (2 * arb.pi()) * (t.log() - L0()) - R(t)


def log_int(p: int, j: int, A: arb, B: arb | None) -> arb:
    """Integral of t^(-p) (log t)^j over [A, B] (B None means infinity)."""
    if p == 1:
        if B is None:
            raise ValueError("divergent")
        if j == 0:
            return B.log() - A.log()
        return (B.log() ** 2 - A.log() ** 2) / 2
    q = arb(p - 1)

    def prim(t: arb) -> arb:  # minus the antiderivative, evaluated at t
        if j == 0:
            return t ** (-q) / q
        return t ** (-q) * (t.log() / q + 1 / q ** 2)

    return prim(A) - (0 if B is None else prim(B))


def int_N_plus(p: int, A: arb, B: arb | None) -> arb:
    """Upper bound for the integral of N_plus(t) t^(-p) over [A, B], A > e.

    log log t is replaced by its tangent line at t = A (concavity of log), so
    every piece integrates in closed form.
    """
    lA = A.log()
    main = (log_int(p - 1, 1, A, B) - L0() * log_int(p - 1, 0, A, B)) / (2 * arb.pi())
    i0, i1 = log_int(p, 0, A, B), log_int(p, 1, A, B)
    return (main + a_(C1) * i1 + a_(C3) * i0
            + a_(C2) * ((lA.log() - 1) * i0 + i1 / lA))


def g(u: arb) -> arb:
    """The envelope g(u) = min(1, (9/2)/u, 216/u^3), for an exact point u."""
    if u <= a_(U1):
        return arb(1)
    if u <= U2():
        return a_(C_M1) / u
    if u >= U2():
        return a_(C_M3) / u ** 3
    raise ArithmeticError("u straddles the crossover; perturb a")


def S_low(a: arb) -> arb:
    """Upper bound for sum_{0 < gamma <= H0} g(gamma/a); a an exact point >= 1.

    H0 = 0 is the mode that uses no verification of RH at all.
    """
    if H0 == 0:
        return arb(0)
    H = arb(H0)
    t1, t2 = a_(U1) * a, U2() * a
    if H <= t1:
        return N_plus(H)
    val = g(H / a) * N_plus(H)
    if H <= t2:
        return val + a_(C_M1) * a * int_N_plus(2, t1, H)
    if H >= t2:
        return (val + a_(C_M1) * a * int_N_plus(2, t1, t2)
                + 3 * C_M3 * a ** 3 * int_N_plus(4, t2, H))
    raise ArithmeticError("H0 straddles t2; perturb a")


def S_high(a: arb) -> arb:
    """Upper bound for sum_{gamma > H0} g(gamma/a); a an exact point >= 1."""
    t1, t2 = a_(U1) * a, U2() * a
    if H0 == 0:   # sum over every zero; N(0) = 0 and G is flat below t1 >= 9/2 > e
        return (a_(C_M1) * a * int_N_plus(2, t1, t2)
                + 3 * C_M3 * a ** 3 * int_N_plus(4, t2, None))
    H = arb(H0)
    val = -g(H / a) * N_minus(H)
    lo = H if H >= t1 else t1
    if lo <= t2:
        return (val + a_(C_M1) * a * int_N_plus(2, lo, t2)
                + 3 * C_M3 * a ** 3 * int_N_plus(4, t2, None))
    if lo >= t2:
        return val + 3 * C_M3 * a ** 3 * int_N_plus(4, lo, None)
    raise ArithmeticError("H0 straddles t2; perturb a")


# ---------------------------------------------------------------------------
# Interval families (RESULTS.md section 4)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class KthPowers:
    """x = n^k, h = (n+1)^k - n^k, parametrised by L = log n."""
    k: int

    def data(self, La: arb, Lb: arb) -> dict:
        k = arb(self.k)
        eta_a = (k * (-La).exp().log1p()).expm1()
        return {
            "lx_lo": k * La,
            "eta_lo": (k * (-Lb).exp().log1p()).expm1(),
            "log_xph_hi": k * (Lb + (-Lb).exp().log1p()),
            "h_lo": (k * La).exp() * eta_a,
        }


@dataclass(frozen=True)
class PowerLog:
    """h = c x^theta log x, parametrised by L = log x; needs L >= 1/(1-theta)."""
    c: Fraction
    theta: Fraction

    def data(self, La: arb, Lb: arb) -> dict:
        c, th = a_(self.c), a_(self.theta)
        if not La >= 1 / (1 - th):
            raise ValueError("eta is decreasing only for log x >= 1/(1-theta)")
        h_b = c * (th * Lb).exp() * Lb
        return {
            "lx_lo": La,
            "eta_lo": c * ((th - 1) * Lb).exp() * Lb,
            "log_xph_hi": (Lb.exp() + h_b).log(),
            "h_lo": c * (th * La).exp() * La,
        }


def interval_bound(family, theta: Fraction, La: arb, Lb: arb) -> dict:
    """Bound E and the prime-power share on one parameter interval.

    Returns arb balls; the interval is closed when ``margin > 0`` is certain.
    """
    d = family.data(La, Lb)
    lx, eta = d["lx_lo"], d["eta_lo"]
    a_star = (1 + 1 / eta).upper()          # exact point >= 1 + 1/eta
    x_lo = lx.exp()
    low = 2 * (-lx / 2).exp() * S_low(a_star)
    high = 2 * ((a_(theta) - 1) * lx).exp() * S_high(a_star)
    triv = 1 / (x_lo * (x_lo ** 2 - 1))
    E = low + high + triv
    lxh = d["log_xph_hi"]
    p2 = ((arb.pi() ** 2 / 6 - 1) * (-lx / 2).exp() * lxh
          + lxh * (lxh / arb(2).log()).log() / d["h_lo"])
    share = a_(PHI_MAX) * p2
    return {"a_star": a_star, "low": low, "high": high, "triv": triv,
            "E": E, "prime_power_share": share, "margin": 1 - E - share}


# ---------------------------------------------------------------------------
# Tail constants (RESULTS.md section 5)
# ---------------------------------------------------------------------------


def envelope_moments() -> dict:
    """J1 = int u(-g'), J1L = int u log u (-g'), JL = int log u (-g'), over u >= U1."""
    u1, u2 = a_(U1), U2()
    J1 = a_(C_M1) * (u2.log() - u1.log()) + 3 * C_M3 / (2 * u2 ** 2)
    J1L = (a_(C_M1) * (u2.log() ** 2 - u1.log() ** 2) / 2
           + 3 * C_M3 * u2 ** (-2) * (u2.log() / 2 + arb(1) / 4))
    JL = (a_(C_M1) * (u1 ** -1 * (u1.log() + 1) - u2 ** -1 * (u2.log() + 1))
          + 3 * C_M3 * u2 ** (-3) * (u2.log() / 3 + arb(1) / 9))
    return {"J1": J1, "J1L": J1L, "JL": JL}


def _monomials_decrease(monos, L: arb) -> bool:
    """Each coef * n^-e (log n)^j (log log n)^l decreases for log n >= L."""
    for _, e, j, l in monos:
        slope = arb(j) / L + (arb(l) / (L * L.log()) if l else 0)
        if not slope < e:
            return False
    return True


def _monomials_value(monos, L: arb) -> arb:
    total = arb(0)
    for coef, e, j, l in monos:
        term = coef * (-e * L).exp() * L ** j
        if l:
            term *= L.log() ** l
        total += term
    return total


def kth_power_tail(k: int, theta: Fraction, Linf: Fraction) -> dict:
    """Bound E + share for every n >= exp(Linf) (RESULTS.md section 5.1)."""
    L = a_(Linf)
    kk, th = arb(k), a_(theta)
    e_main = kk * (1 - th) - 1
    if not e_main > 0:
        return {"closed": False, "reason": "k(1-theta) <= 1: the main term does not decay"}
    J = envelope_moments()
    Bplus = (J["J1L"] - L0() * J["J1"]).max(arb(0))
    n_over_k_log = L - kk.log()
    K0 = a_(C1) * J["JL"] + a_(C2) * J["JL"] / n_over_k_log + a_(C3)
    e_high = kk * (1 - th)
    phim = a_(PHI_MAX)
    monos = [
        (J["J1"] / arb.pi(), e_main, 1, 0),
        (Bplus / arb.pi(), e_main, 0, 0),
        (2 * a_(C1), e_high, 1, 0),
        (2 * a_(C2), e_high, 0, 1),
        (2 * K0, e_high, 0, 0),
        (2 * N_plus(arb(H0)) if H0 else arb(0), kk / 2, 0, 0),
        (arb(2), 3 * kk, 0, 0),
        (phim * (arb.pi() ** 2 / 6 - 1) * kk, kk / 2, 1, 0),
        (phim * (arb.pi() ** 2 / 6 - 1) * kk, kk / 2, 0, 0),
        (phim * kk / arb(2).log(), kk - 1, 2, 0),
        (phim * 2 * kk / arb(2).log(), kk - 1, 1, 0),
        (phim * kk / arb(2).log(), kk - 1, 0, 0),
    ]
    # prerequisites used in the derivation: a* = 1 + n/k satisfies a* >= 2 pi e,
    # a* <= n, and (log a* - L0) J1 + J1L >= 0 there.
    ok_pre = bool(n_over_k_log > L0() + 1)
    dec = _monomials_decrease(monos, L)
    value = _monomials_value(monos, L)
    return {"closed": bool(ok_pre and dec and value < 1), "prereq": ok_pre,
            "decreasing": dec, "sup_bound": value}


def powerlog_tail(c: Fraction, theta: Fraction, Linf: Fraction) -> dict:
    """Bound E + share for every x >= exp(Linf), h = c x^theta log x (section 5.2)."""
    L = a_(Linf)
    cc, th = a_(c), a_(theta)
    J = envelope_moments()
    s = 1 - th
    # Y(L) = J1 (log 2 - L0 - log(cL)) + J1L, decreasing in L.
    Y = J["J1"] * (arb(2).log() - L0() - (cc * L).log()) + J["J1L"]
    Yp = Y.max(arb(0))
    limit = J["J1"] * s / (arb.pi() * cc)
    head = limit + Yp / (arb.pi() * cc * L)
    phim = a_(PHI_MAX)
    K0 = a_(C1) * (arb(2).log() + J["JL"]) + a_(C2) * J["JL"] / (s * L - (cc * L).log()) + a_(C3)
    monos = [
        (J["J1"] * s / arb.pi(), s, 1, 0),
        (Yp / arb.pi(), s, 0, 0),
        (2 * a_(C1) * s, s, 1, 0),
        (2 * a_(C2), s, 0, 1),
        (2 * K0, s, 0, 0),
        (2 * N_plus(arb(H0)) if H0 else arb(0), arb(1) / 2, 0, 0),
        (arb(2), arb(3), 0, 0),
        (phim * (arb.pi() ** 2 / 6 - 1), arb(1) / 2, 1, 0),
        (phim * (arb.pi() ** 2 / 6 - 1) * arb(2).log(), arb(1) / 2, 0, 0),
        (phim / (arb(2).log() * cc), th, 1, 0),
        (phim * 2 / (arb(2).log() * cc), th, 0, 0),
        (phim / (arb(2).log() * cc), th, -1, 0),
    ]
    # prerequisites: x^(1-theta)/(cL) >= 1 (so log a <= sL - log(cL) + log 2),
    # a >= 2 pi e, h <= x, and log a >= sL - log(cL) > 1 for the JL/log a term.
    a_min_log = s * L - (cc * L).log()
    ok_pre = bool(a_min_log > L0() + 1 and cc * L * (th * L).exp() < L.exp()
                  and cc * L >= 1)
    dec = _monomials_decrease([m for m in monos if m[2] >= 0], L)
    value = head + _monomials_value(monos, L)
    return {"closed": bool(ok_pre and dec and value < 1), "prereq": ok_pre,
            "decreasing": dec, "limit": limit, "sup_bound": value}


def set_precision(bits: int = PREC) -> None:
    ctx.prec = bits


# ---------------------------------------------------------------------------
# Pointwise psi bound (RESULTS.md section 8): sums of g(gamma/a)/gamma
# ---------------------------------------------------------------------------

T_ZERO_FREE = 14   # N(14) = 0, checked by Arb's zeta_nzeros in the tests


def _pieces(a: arb):
    """(start, end, coefficient, p) with -d/dt[g(t/a)/t] = coefficient * t^-p."""
    t1, t2 = a_(U1) * a, U2() * a
    return [(None, t1, arb(1), 2), (t1, t2, 2 * a_(C_M1) * a, 3),
            (t2, None, 4 * C_M3 * a ** 3, 5)]


def _gt(t: arb, a: arb) -> arb:
    return g(t / a) / t


def _int_pieces(a: arb, lo: arb, hi: arb | None) -> arb:
    """Upper bound for the integral of N_plus * (-d/dt g(t/a)/t) over [lo, hi]."""
    total = arb(0)
    for s0, s1, coef, p in _pieces(a):
        A = lo if s0 is None or s0 <= lo else s0
        if s0 is not None and not (s0 <= lo or s0 >= lo):
            raise ArithmeticError("breakpoint straddles lo")
        Bp = hi if s1 is None else (s1 if hi is None or s1 <= hi else hi)
        if hi is not None and s1 is not None and not (s1 <= hi or s1 >= hi):
            raise ArithmeticError("breakpoint straddles hi")
        if Bp is not None and not A < Bp:
            continue
        total += coef * int_N_plus(p, A, Bp)
    return total


def Sp_low(a: arb) -> arb:
    """Upper bound for sum_{0 < gamma <= H0} g(gamma/a)/gamma."""
    if H0 == 0:
        return arb(0)
    H = arb(H0)
    return _gt(H, a) * N_plus(H) + _int_pieces(a, arb(T_ZERO_FREE), H)


def Sp_high(a: arb) -> arb:
    """Upper bound for sum_{gamma > H0} g(gamma/a)/gamma."""
    if H0 == 0:
        return _int_pieces(a, arb(T_ZERO_FREE), None)
    H = arb(H0)
    return -_gt(H, a) * N_minus(H) + _int_pieces(a, H, None)


def psi_ratio_bound(theta: Fraction, La: arb, Lb: arb, delta: arb) -> arb:
    """Upper bound for |psi(x) - x| / x^theta on log x in [La, Lb], smoothing width delta."""
    th = a_(theta)
    a = ((1 + delta) / delta).upper()
    return (delta * ((1 - th) * Lb).exp() / 2
            + 2 * (1 + delta).sqrt() * ((arb(1) / 2 - th) * La).exp() * Sp_low(a)
            + 2 * (1 + delta) ** th * Sp_high(a)
            + ((2 * arb.pi()).log() + (-2 * La).exp()) * (-th * La).exp())


def psi_target(theta: Fraction, L: arb) -> arb:
    """(1 - theta)^2 L^2 / (2 pi): the claimed bound for |psi(x) - x| / x^theta."""
    return (1 - a_(theta)) ** 2 * L ** 2 / (2 * arb.pi())


def psi_interval(theta: Fraction, La: arb, Lb: arb, factors=(0.5, 0.7, 1.0, 1.4, 2.0)) -> dict:
    """Best of a few smoothing widths delta = f * L e^{-(1-theta)L} / (4 pi) on one interval."""
    th = a_(theta)
    best = None
    for f in factors:
        d = (a_(Fraction(f).limit_denominator(100)) * La * (-(1 - th) * La).exp()
             / (4 * arb.pi())).upper()
        if not d < a_(Fraction(1, 2)):
            continue
        r = psi_ratio_bound(theta, La, Lb, d)
        if best is None or r.upper() < best[1].upper():
            best = (d, r)
    target = psi_target(theta, La)
    return {"delta": best[0], "ratio": best[1], "target": target,
            "margin": target - best[1]}


def psi_tail(theta: Fraction, Linf: Fraction) -> dict:
    """|psi(x) - x| / x^theta < s^2 L^2/(2 pi), s = 1 - theta, for every L = log x >= Linf.

    RESULTS.md section 8.3.  No verified height is used (every zero gets theta);
    delta = L e^{-sL}/(4 pi).  Writes the bound as target - D(L) and checks
    D(Linf) > 0 and D' > 0 on [Linf, infinity).
    """
    th = a_(theta)
    s_ = 1 - th
    L = a_(Linf)
    pi = arb.pi()
    u1, u2 = a_(U1), U2()
    k1, k2 = L0() - u1.log(), L0() - u2.log()
    c1, c2, c3 = a_(C1), a_(C2), a_(C3)
    delta_inf = L * (-s_ * L).exp() / (4 * pi)
    T = arb(T_ZERO_FREE)
    lT = T.log()
    rho1 = (c1 * (lT + 1) / T + c3 / T
            + c2 * ((lT.log() - 1) / T + (lT + 1) / (T * lT)))
    mu = L.log() - (4 * pi).log() - delta_inf
    lin = (2 / pi) * (1 - u1 / u2) + 864 / (3 * pi * u2 ** 3)
    const = 2 * rho1 + 864 / (9 * pi * u2 ** 3)
    main = (s_ * L * (mu + k1) / pi - L / (8 * pi) - lin * s_ * L
            - (mu + k1) ** 2 / (2 * pi) - const)
    # small(L) <= 2 delta (Q(L) + E1(L)) + (log 2 pi + 1) e^{-theta L}, each piece a
    # positive-coefficient polynomial of degree <= 3 times e^{-sL} (or e^{-theta L}).
    Q_L = L ** 2 / (4 * pi) + lin / 2 * L + rho1 + 864 / (18 * pi * u2 ** 3)
    lt2 = u2.log() + L
    E1_L = (arb(9) / 2 * ((c1 + c2) * lt2 + c3) * (u1 ** -2 - u2 ** -2)
            + 864 / u2 ** 4 * ((c1 + c2) * (lt2 / 4 + arb(1) / 16) + c3 / 4))
    small = 2 * delta_inf * (Q_L + E1_L) + ((2 * pi).log() + 1) * (-th * L).exp()
    D = main - small
    dmain = s_ * (mu + k1 + 1) / pi - 1 / (8 * pi) - lin * s_ - (mu + k1) / (pi * L)
    prereq = bool(-delta_inf.log() > k1        # lambda >= log(1/delta) above the vertex of Q
                  and mu + k2 > 0              # dropped -lin (mu + k2)
                  and delta_inf < a_(Fraction(1, 2))
                  and L > 3 / s_               # small(L) decreasing, delta decreasing
                  and L > (1 - (mu - L.log() + k1)).exp())   # (log L + c)/L decreasing
    return {"closed": bool(prereq and dmain > 0 and D > 0), "D": D,
            "dD_lower": dmain, "prereq": prereq}
