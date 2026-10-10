"""Explicit lower bound for L(1, chi) from a zero-free half-plane Re s > sigma0.

Every quantity returned here is an Arb ball (python-flint), and the bound used
downstream is the lower endpoint of the final ball.  The derivation is in
RESULTS.md section 2; the names follow it:

    q        conductor of the primitive odd real character chi_D (q = |D|)
    sigma0   zero-free abscissa (7/8 from OpenAI's Theorem 1.1); eps0 = 1 - sigma0
    a, b     a = log y, b = log x, 0 < a < b: the two Cesaro cutoffs
    dy, dx   split points sigma_1 - 1 for the y-term and the x-term

    log L(1, chi) >= M(a, b) - (R(b, dx) + R(a, dy) + T) / (b - a)

with M the prime-sum main term (Lemma 3) and R the zero-sum bound (Lemma 2).
"""

from __future__ import annotations

import math
from fractions import Fraction

import numpy as np
from flint import arb, arb_series, ctx

PREC = 128

#: Primes below this are summed exactly (in Arb); above it the
#: Rosser-Schoenfeld bound sum_{p<=t} 1/p < log log t + B + 1/(2 log^2 t)
#: (t >= 286; RS 1962, Theorem 5, (3.20)) is used.
T_EXACT = 10**7

# ---------------------------------------------------------------------------
# primes and exact prime sums
# ---------------------------------------------------------------------------


def primes_upto(n: int) -> np.ndarray:
    """All primes <= n (numpy sieve of Eratosthenes)."""
    if n < 2:
        return np.zeros(0, dtype=np.int64)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    sieve[4::2] = False
    for p in range(3, int(n**0.5) + 1, 2):
        if sieve[p]:
            sieve[p * p::2 * p] = False
    return np.nonzero(sieve)[0].astype(np.int64)


class _PrimeTables:
    """Prefix sums over primes p <= T_EXACT, every entry an Arb ball."""

    def __init__(self, limit: int = T_EXACT):
        with ctx.workprec(PREC):
            self.limit = limit
            self.p = primes_upto(limit)
            self.logp_f = np.log(self.p.astype(float))
            S, T, g2, g4 = [arb(0)], [arb(0)], [arb(0)], [arb(0)]
            s = t = u = v = arb(0)
            for p in self.p.tolist():
                inv = arb(1) / p
                s += inv
                t += arb(p).log() * inv
                inv2 = inv * inv
                u += inv2 / 2 - inv2 * inv / 3
                v += inv2 * inv2 / 4 - inv2 * inv2 * inv / 5
                S.append(s)
                T.append(t)
                g2.append(u)
                g4.append(v)
            # index k holds the sum over the first k primes
            self.S, self.T, self.g2, self.g4 = S, T, g2, g4

    def count_le_log(self, u: arb) -> int:
        """Number of primes p <= T_EXACT with log p <= u (u an Arb ball).

        Raises if a prime sits inside the ball's uncertainty.
        """
        lo = float(u.lower()) - 1e-12
        hi = float(u.upper()) + 1e-12
        k_lo = int(np.searchsorted(self.logp_f, lo, side='right'))
        k_hi = int(np.searchsorted(self.logp_f, hi, side='right'))
        if k_lo != k_hi:
            # decide the straddling primes exactly
            for k in range(k_lo, k_hi):
                lp = arb(int(self.p[k])).log()
                if lp < u:
                    continue
                if lp > u:
                    return k
                raise ValueError('prime boundary inside a ball; perturb a or b')
            return k_hi
        return k_lo


_TABLES: dict[int, _PrimeTables] = {}


def tables(limit: int = T_EXACT) -> _PrimeTables:
    if limit not in _TABLES:
        _TABLES[limit] = _PrimeTables(limit)
    return _TABLES[limit]


def meissel_mertens() -> arb:
    """B = gamma + sum_{k>=2} mu(k) log zeta(k) / k, with a rigorous tail.

    Tail: |log zeta(k)| <= zeta(k) - 1 <= 3 * 2^-k for k >= 2, so the terms
    k > K contribute at most 3 * 2^-K / K in absolute value.
    """
    with ctx.workprec(PREC + 20):
        K = 160
        mu = _mobius_upto(K)
        total = arb.const_euler()
        for k in range(2, K + 1):
            if mu[k]:
                total += mu[k] * arb(k).zeta().log() / k
        tail = arb(3) * arb(2) ** (-K) / K
        return total + arb(0, tail.upper())


def _mobius_upto(n: int) -> list[int]:
    mu = [1] * (n + 1)
    mu[0] = 0
    is_comp = [False] * (n + 1)
    for p in range(2, n + 1):
        if not is_comp[p]:
            for m in range(p, n + 1, p):
                is_comp[m] = True if m != p else is_comp[m]
                mu[m] = -mu[m]
            for m in range(p * p, n + 1, p * p):
                mu[m] = 0
    return mu


# ---------------------------------------------------------------------------
# the main term M(a, b)   (Lemma 3)
# ---------------------------------------------------------------------------


def s_integral_upper(a: arb, b: arb, tab: _PrimeTables, B: arb) -> arb:
    """Upper bound for int_a^b S(e^u) du, S(t) = sum_{p <= t} 1/p.

    Exact below log T_EXACT (S is a step function), Rosser-Schoenfeld above.
    """
    astar = arb(tab.limit).log()
    total = arb(0)
    # exact part on [a, c], c = min(b, astar)
    if a < astar:
        c = b if b < astar else astar
        ka = tab.count_le_log(a)
        kc = tab.count_le_log(c)
        # int_a^c S(e^u) du = c S(e^c) - a S(e^a) - sum_{e^a < p <= e^c} log p / p
        total += c * tab.S[kc] - a * tab.S[ka] - (tab.T[kc] - tab.T[ka])
    elif not (a >= astar):
        raise ValueError('a straddles log T_EXACT')
    # Rosser-Schoenfeld part on [max(a, astar), b]
    lo = a if a >= astar else astar
    if b > lo:
        def F(u):  # antiderivative of log u + B + 1/(2u^2)
            return u * u.log() - u + B * u - 1 / (2 * u)
        total += F(b) - F(lo)
    if tab.limit < 286:
        raise ValueError('Rosser-Schoenfeld (3.20) needs t >= 286')
    return total


def p2_lower(a: arb, tab: _PrimeTables) -> arb:
    """Lower bound for sum_p sum_{k>=2} (-1)^k w(p^k)/(k p^k) (Lemma 3 (ii)).

    Uses 1/(2p^2) - 1/(3p^3) for p^2 <= y and adds 1/(4p^4) - 1/(5p^5) for
    p^4 <= y; every omitted term is >= 0 (alternating, nonincreasing).
    Primes above T_EXACT are dropped (their terms are positive).
    """
    k2 = tab.count_le_log(a / 2)
    k4 = tab.count_le_log(a / 4)
    return tab.g2[k2] + tab.g4[k4]


def main_term_lower(a, b, B=None, tab=None) -> arb:
    """M(a, b) <= sum_n Lambda(n) chi(n) w(n) / (n log n) for every real chi."""
    with ctx.workprec(PREC):
        a, b = _arb(a), _arb(b)
        tab = tab or tables()
        B = B if B is not None else meissel_mertens()
        if not (a > arb(30).log()):
            raise ValueError('need y > 30')
        avg = s_integral_upper(a, b, tab, B) / (b - a)
        return -avg + p2_lower(a, tab)


# ---------------------------------------------------------------------------
# the zero-sum term R(L, delta)   (Lemma 2)
# ---------------------------------------------------------------------------

#: Global u-grid (u = sigma - 1), exact rationals.  delta must lie on it.
def _grid() -> list[Fraction]:
    g = [Fraction(j, 2000) for j in range(0, 1001)]          # to 0.5 by 1/2000
    g += [Fraction(1, 2) + Fraction(k, 500) for k in range(1, 751)]   # to 2
    g += [Fraction(2) + Fraction(k, 100) for k in range(1, 401)]      # to 6
    return g


GRID = _grid()
U_MAX = GRID[-1]
_P_CACHE: dict[Fraction, arb] = {}


def P_sum(sigma: arb) -> arb:
    """sum_p log p / (p^sigma + 1) = -zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma)."""
    z1 = arb_series([sigma, 1], prec=2).zeta()
    z2 = arb_series([2 * sigma, 1], prec=2).zeta()
    return -z1[1] / z1[0] + 2 * z2[1] / z2[0]


def P_on_grid(u: Fraction) -> arb:
    if u not in _P_CACHE:
        with ctx.workprec(PREC):
            _P_CACHE[u] = P_sum(1 + arb(u.numerator) / u.denominator)
    return _P_CACHE[u]


def _arb(x) -> arb:
    if isinstance(x, arb):
        return x
    if isinstance(x, Fraction):
        return arb(x.numerator) / x.denominator
    if isinstance(x, int):
        return arb(x)
    if isinstance(x, str):
        return arb(x) if '/' not in x else _arb(Fraction(x))
    raise TypeError(f'exact input required, got {type(x)}')


def zero_sum_upper(L, delta: Fraction, half_log_q_over_pi: arb, eps0: arb,
                   g_nonneg: bool = False) -> arb:
    """R(t) for t = e^L: upper bound for sum_rho int_1^inf t^{beta-sigma}/|sigma-rho|^2.

    R = e^{-eps0 L} [ (delta+eps0) G(1+delta) int_0^delta e^{-uL}/(u+eps0)^2 du
                      + int_delta^inf e^{-uL} G(1+u)/(u+eps0) du ],
    G(sigma) = (1/2) log(q/pi) + (1/2) psi((sigma+1)/2) + P(sigma).
    Both integrals are bounded by upper sums on GRID (the weights are
    decreasing, psi is increasing and P is decreasing in u).

    With g_nonneg=True the first argument is used as is (pass (1/2) log Q)
    and G is replaced by half + max(0, psi/2 + P): the form needed for the
    monotone tail argument of Theorem A.
    """
    with ctx.workprec(PREC):
        L = _arb(L)
        if delta not in _GRID_INDEX or delta <= 0:
            raise ValueError('delta must be a positive grid point')
        jd = _GRID_INDEX[delta]
        d = _arb(delta)

        def G_upper(u_lo: Fraction, u_hi: Fraction) -> arb:
            psi = (1 + _arb(u_hi) / 2).digamma()
            g = psi / 2 + P_on_grid(u_lo)
            if g_nonneg:
                g = _nonneg(g)
            return half_log_q_over_pi + g

        def exp_piece(u_lo, u_hi):  # int_{u_lo}^{u_hi} e^{-uL} du
            return ((-_arb(u_lo) * L).exp() - (-_arb(u_hi) * L).exp()) / L

        # part 1: sigma in [1, 1 + delta]
        part1 = arb(0)
        for j in range(jd):
            u0, u1 = GRID[j], GRID[j + 1]
            part1 += exp_piece(u0, u1) / (_arb(u0) + eps0) ** 2
        g1 = G_upper(delta, delta)
        part1 *= (d + eps0) * _nonneg(g1)
        # part 2: sigma in [1 + delta, 1 + U_MAX]
        part2 = arb(0)
        for j in range(jd, len(GRID) - 1):
            u0, u1 = GRID[j], GRID[j + 1]
            g = _nonneg(G_upper(u0, u1))
            part2 += exp_piece(u0, u1) / (_arb(u0) + eps0) * g
        # tail u >= U: G <= C0 + u/4 with C0 = (1/2)log(q/pi) + P(1+U)
        U = _arb(U_MAX)
        C0 = _nonneg(half_log_q_over_pi + P_on_grid(U_MAX))
        if g_nonneg:
            C0 = half_log_q_over_pi + _nonneg(P_on_grid(U_MAX))
        tail = (-U * L).exp() / (U + eps0) * (C0 / L + (U / L + 1 / (L * L)) / 4)
        return (-eps0 * L).exp() * (part1 + part2 + tail)


_GRID_INDEX = {u: j for j, u in enumerate(GRID)}


def _nonneg(x: arb) -> arb:
    """An upper bound that is >= 0 (keeps upper sums valid)."""
    up = x.upper()
    return up if up > 0 else arb(0)


def trivial_upper(L) -> arb:
    """sum_k int_1^inf t^{-(2k+1)-sigma}/(2k+1+sigma)^2 <= (pi^2/24) t^{-2}/log t."""
    L = _arb(L)
    return arb.pi() ** 2 / 24 * (-2 * L).exp() / L


# ---------------------------------------------------------------------------
# the bound
# ---------------------------------------------------------------------------


def log_L1_lower(q, a, b, dx: Fraction, dy: Fraction, sigma0='7/8',
                 B=None, tab=None, detail=False):
    """Lower bound (Arb ball; use .lower()) for log L(1, chi).

    Valid for every primitive odd real character chi of conductor <= q, given
    that L(s, chi) has no zeros with Re s > sigma0.
    """
    with ctx.workprec(PREC):
        q = _arb(q)
        a, b = _arb(a), _arb(b)
        if not (b > a):
            raise ValueError('need b > a')
        eps0 = 1 - _arb(sigma0)
        h = (q / arb.pi()).log() / 2
        M = main_term_lower(a, b, B=B, tab=tab)
        Rx = zero_sum_upper(b, dx, h, eps0)
        Ry = zero_sum_upper(a, dy, h, eps0)
        T = trivial_upper(a) + trivial_upper(b)
        E = (Rx + Ry + T) / (b - a)
        val = M - E
        if detail:
            return {'M': M, 'Rx': Rx, 'Ry': Ry, 'T': T, 'E': E, 'logL': val}
        return val


def h_lower(q_lo, q_hi, params, sigma0='7/8', B=None, tab=None) -> arb:
    """Lower bound for h(D) = sqrt|D| L(1,chi_D)/pi on q_lo <= |D| <= q_hi (D < -4)."""
    a, b, dx, dy = params
    with ctx.workprec(PREC):
        lg = log_L1_lower(q_hi, a, b, dx, dy, sigma0=sigma0, B=B, tab=tab)
        return _arb(q_lo).sqrt() * lg.lower().exp() / arb.pi()


# ---------------------------------------------------------------------------
# a fast float model of the same bound, only for choosing parameters
# ---------------------------------------------------------------------------


class FloatModel:
    """Float64 replica of log_L1_lower used to optimise (a, b, dx, dy).

    It assigns no truth: every reported bound is recomputed by log_L1_lower.
    """

    def __init__(self, sigma0=7/8, tab=None):
        from scipy.special import digamma
        self.eps0 = 1 - float(sigma0)
        tab = tab or tables()
        self.tab = tab
        self.B = float(meissel_mertens().mid())
        g = np.array([float(u) for u in GRID])
        self.g = g
        self.P = np.array([float(P_on_grid(u).mid()) for u in GRID])
        self.psi_hi = np.array([digamma(1 + u / 2) for u in g])
        self.S = np.array([float(s.mid()) for s in tab.S])
        self.T = np.array([float(s.mid()) for s in tab.T])
        self.g2 = np.array([float(s.mid()) for s in tab.g2])
        self.g4 = np.array([float(s.mid()) for s in tab.g4])
        self.logp = tab.logp_f
        self.astar = math.log(tab.limit)

    def main(self, a, b):
        tot = 0.0
        if a < self.astar:
            c = min(b, self.astar)
            ka = np.searchsorted(self.logp, a, side='right')
            kc = np.searchsorted(self.logp, c, side='right')
            tot += c * self.S[kc] - a * self.S[ka] - (self.T[kc] - self.T[ka])
        lo = max(a, self.astar)
        if b > lo:
            F = lambda u: u * math.log(u) - u + self.B * u - 1 / (2 * u)
            tot += F(b) - F(lo)
        k2 = np.searchsorted(self.logp, a / 2, side='right')
        k4 = np.searchsorted(self.logp, a / 4, side='right')
        return -tot / (b - a) + self.g2[k2] + self.g4[k4]

    def R(self, L, jd, h):
        g, e = self.g, self.eps0
        ex = (np.exp(-g[:-1] * L) - np.exp(-g[1:] * L)) / L
        G = np.maximum(h + self.psi_hi[1:] / 2 + self.P[:-1], 0)
        part1 = np.sum(ex[:jd] / (g[:jd] + e) ** 2)
        g1 = max(h + self.psi_hi[jd] / 2 + self.P[jd], 0)
        part1 *= (g[jd] + e) * g1
        part2 = np.sum(ex[jd:] / (g[jd:-1] + e) * G[jd:])
        U = g[-1]
        C0 = max(h + self.P[-1], 0)
        tail = math.exp(-U * L) / (U + e) * (C0 / L + (U / L + 1 / L**2) / 4)
        return math.exp(-e * L) * (part1 + part2 + tail)

    def logL(self, logq, a, b, jx, jy):
        h = 0.5 * (logq - math.log(math.pi))
        M = self.main(a, b)
        E = (self.R(b, jx, h) + self.R(a, jy, h)
             + math.pi**2 / 24 * (math.exp(-2 * a) / a + math.exp(-2 * b) / b)) / (b - a)
        return M - E

    def optimise(self, logq, start=None):
        """Coordinate search over (a, b) continuous and (jx, jy) grid indices."""
        if start is None:
            start = (12.0, 20.0, 200, 200)
        a, b, jx, jy = start
        best = self.logL(logq, a, b, jx, jy)
        steps = [1.0, 0.25, 0.05, 0.01]
        jsteps = [64, 16, 4, 1]
        amin = math.log(31.0)
        for st, js in zip(steps, jsteps):
            improved = True
            while improved:
                improved = False
                for da, db, djx, djy in [(st, 0, 0, 0), (-st, 0, 0, 0), (0, st, 0, 0),
                                         (0, -st, 0, 0), (0, 0, js, 0), (0, 0, -js, 0),
                                         (0, 0, 0, js), (0, 0, 0, -js), (st, st, 0, 0),
                                         (-st, -st, 0, 0)]:
                    na, nb, njx, njy = a + da, b + db, jx + djx, jy + djy
                    if na < amin or nb <= na + 0.05 or not (1 <= njx <= 1000) \
                            or not (1 <= njy <= 1000):
                        continue
                    v = self.logL(logq, na, nb, njx, njy)
                    if v > best + 1e-12:
                        a, b, jx, jy, best = na, nb, njx, njy, v
                        improved = True
        return best, (a, b, jx, jy)


def params_from_float(a: float, b: float, jx: int, jy: int, digits: int = 3):
    """Round optimiser output to exact inputs (decimal strings, grid fractions)."""
    fa = Fraction(round(a * 10**digits), 10**digits)
    fb = Fraction(round(b * 10**digits), 10**digits)
    return fa, fb, GRID[jx], GRID[jy]
