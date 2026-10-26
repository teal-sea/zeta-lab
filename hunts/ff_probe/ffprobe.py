"""Hunt #148 (`ff_probe`): the 7/8 probe's local identity over F_q[T].

Exact arithmetic only.  Every algebraic number is an element of a cyclotomic
field Q(zeta_N), stored as a rational polynomial reduced modulo the N-th
cyclotomic polynomial, so an equality test is an equality of reduced
polynomials.  Polynomials over F_q (q prime) are python-flint ``nmod_poly``
objects or plain coefficient tuples (constant term first).

Conventions (each one is checked by ``test_ffprobe.py``, none is assumed):

* ``chi(x) = x^((q-1)/n)`` on F_q^x, and ``eps`` sends ``g^((q-1)/n)`` to
  ``zeta_n``, where ``g`` is the least primitive root mod q.
* The n-th power residue symbol of ``a`` modulo a monic ``c`` is
  ``(a/c)_n = chi(Res(c, a))`` (Patterson 2007, section 1), and modulo a monic
  irreducible ``P`` it is the constant ``a^((|P|-1)/n) mod P``.  Both routes are
  implemented and compared.
* The additive character is ``e(f) = exp(2 pi i a_{-1}(f) / q)``, with
  ``a_{-1}(f)`` the coefficient of ``T^-1`` in the expansion of ``f`` in
  ``1/T`` (Patterson 2014, ``e(f) = e_o(-Res_infty(f dx))``).
* ``g(r, j, c) = sum_{y mod c, (y,c)=1} eps((y/c)_n)^j e(r y / c)``.

Run ``.venv/bin/python hunts/ff_probe/ffprobe.py --report`` for the summary
tables quoted in this hunt's documents.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import sys
import time
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

import flint
import numpy as np

HERE = Path(__file__).resolve().parent

# ---------------------------------------------------------------------------
# Fault injection (used only by the planted-fault tests)
# ---------------------------------------------------------------------------

#: ``FAULTS`` switches on planted defects so the tests can show that the
#: equality checks are able to fail.  ``"gauss_sign"``: negate the prime Gauss
#: sum G_1(P) = sum eps((y/P)) e(y/P) at every prime of degree 2 in the
#: structural route.  ``"symbol"``: shift the Frobenius-route residue symbol
#: modulo T+1 by one step; ``"symbol_res"``: the same in the resultant route.
#: Further plants, each a wrong Gauss-sum sign or a wrong residue symbol at a
#: different place: ``"gauss_brute_sign"`` (every enumerated Gauss sum),
#: ``"dh_sign"`` (the Davenport-Hasse closed form), ``"prime_gauss_all"`` (every
#: prime Gauss sum G_m(P) of the structural route), ``"tau_sign"`` (every finite
#: field Gauss sum tau(eps chi^j)), and ``"dlog"`` (the discrete logarithm of 2,
#: which both symbol routes share, one step off).
FAULTS: set[str] = set()


# ---------------------------------------------------------------------------
# 1. Exact cyclotomic arithmetic
# ---------------------------------------------------------------------------


class CycField:
    """Q(zeta_N) with elements reduced modulo Phi_N."""

    def __init__(self, N: int):
        self.N = N
        self.Phi = flint.fmpq_poly(flint.fmpz_poly.cyclotomic(N))
        self.dim = self.Phi.degree()
        self._pow = [flint.fmpq_poly([0] * k + [1]) % self.Phi for k in range(N)]
        self.zero = Cyc(self, flint.fmpq_poly([]))
        self.one = Cyc(self, flint.fmpq_poly([1]))

    def zeta(self, k: int) -> "Cyc":
        return Cyc(self, self._pow[k % self.N])

    def from_hist(self, hist) -> "Cyc":
        """sum_k hist[k] zeta_N^k for an integer vector of length N."""
        h = [int(v) for v in hist]
        return Cyc(self, flint.fmpq_poly(h) % self.Phi)

    def scalar(self, v) -> "Cyc":
        v = Fraction(v)
        return Cyc(self, flint.fmpq_poly([flint.fmpq(v.numerator, v.denominator)]))

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"CycField({self.N})"


class Cyc:
    """An element of Q(zeta_N)."""

    __slots__ = ("K", "p")

    def __init__(self, K: CycField, p):
        self.K = K
        self.p = p

    def _coerce(self, o):
        if isinstance(o, Cyc):
            return o.p
        if isinstance(o, (int, Fraction)):
            o = Fraction(o)
            return flint.fmpq_poly([flint.fmpq(o.numerator, o.denominator)])
        raise TypeError(type(o))

    def __add__(self, o):
        return Cyc(self.K, self.p + self._coerce(o))

    __radd__ = __add__

    def __sub__(self, o):
        return Cyc(self.K, self.p - self._coerce(o))

    def __rsub__(self, o):
        return Cyc(self.K, self._coerce(o) - self.p)

    def __neg__(self):
        return Cyc(self.K, -self.p)

    def __mul__(self, o):
        if isinstance(o, (int, Fraction)):
            return Cyc(self.K, self.p * self._coerce(o))
        return Cyc(self.K, (self.p * o.p) % self.K.Phi)

    __rmul__ = __mul__

    def __pow__(self, e: int):
        if e < 0:
            return self.inverse() ** (-e)
        out = self.K.one
        base = self
        while e:
            if e & 1:
                out = out * base
            base = base * base
            e >>= 1
        return out

    def __truediv__(self, o):
        if isinstance(o, (int, Fraction)):
            return self * (Fraction(1) / Fraction(o))
        return self * o.inverse()

    def __eq__(self, o):
        if isinstance(o, (int, Fraction)):
            o = self.K.scalar(o)
        return self.p == o.p

    def __hash__(self):
        return hash(str(self.p))

    def is_zero(self) -> bool:
        return self.p.is_zero()

    def conj(self) -> "Cyc":
        N = self.K.N
        coeffs = self.p.coeffs() if not self.p.is_zero() else []
        out = flint.fmpq_poly([])
        for k, a in enumerate(coeffs):
            if a != 0:
                out += self.K._pow[(-k) % N] * a
        return Cyc(self.K, out % self.K.Phi)

    def inverse(self) -> "Cyc":
        g, s, t = self.p.xgcd(self.K.Phi)
        # s * p + t * Phi = g, with g a nonzero constant when p != 0
        if g.degree() != 0:
            raise ZeroDivisionError("not invertible")
        return Cyc(self.K, (s / g[0]) % self.K.Phi)

    def to_complex(self) -> complex:
        N = self.K.N
        coeffs = self.p.coeffs() if not self.p.is_zero() else []
        z = 0j
        for k, a in enumerate(coeffs):
            if a != 0:
                z += float(a) * complex(math.cos(2 * math.pi * k / N), math.sin(2 * math.pi * k / N))
        return z

    def abs2(self) -> "Cyc":
        return self * self.conj()

    def rational(self) -> Fraction | None:
        """The value as a rational number, or None if it is not rational."""
        if self.p.is_zero():
            return Fraction(0)
        if self.p.degree() == 0:
            c = self.p[0]
            return Fraction(int(c.p), int(c.q))
        return None

    def __repr__(self) -> str:
        return f"Cyc[{self.K.N}]({self.p})"


# ---------------------------------------------------------------------------
# 2. The arithmetic of F_q and F_q[T]
# ---------------------------------------------------------------------------


def primitive_root(q: int) -> int:
    for g in range(2, q):
        if all(pow(g, (q - 1) // r, q) != 1 for r in range(2, q) if (q - 1) % r == 0 and all(r % s for s in range(2, r))):
            return g
    raise ValueError(q)


class Setup:
    """Everything fixed for one (q, n): the field, eps, chi, the additive character.

    ``N`` is chosen so that zeta_n, zeta_q, i and sqrt(q) all lie in Q(zeta_N).
    """

    def __init__(self, q: int, n: int):
        assert (q - 1) % n == 0, "need q = 1 mod n"
        self.q = q
        self.n = n
        self.N = math.lcm(n, q, 4)
        self.K = CycField(self.N)
        self.g = primitive_root(q)
        self.dlog = {pow(self.g, e, q): e for e in range(q - 1)}
        self.zn = self.N // n  # zeta_n = zeta_N^zn
        self.zq = self.N // q  # zeta_q = zeta_N^zq
        # sqrt(q): the quadratic Gauss sum G = sum_a zeta_q^(a^2) is sqrt(q) for
        # q = 1 mod 4 and i sqrt(q) for q = 3 mod 4.
        hist = [0] * self.N
        for a in range(q):
            hist[(self.zq * (a * a % q)) % self.N] += 1
        G = self.K.from_hist(hist)
        i = self.K.zeta(self.N // 4)
        self.sqrtq = G if q % 4 == 1 else -(i * G)
        assert self.sqrtq * self.sqrtq == q
        _SETUPS[(q, n)] = self

    # -- characters of F_q ---------------------------------------------------
    def _dlog(self, x: int) -> int:
        e = self.dlog[x % self.q]
        if "dlog" in FAULTS and x % self.q == 2:
            e += (self.q - 1) // self.n
        return e

    def chi_exp(self, x: int) -> int:
        """Exponent k with eps(chi(x)) = zeta_n^k, for x in F_q^x."""
        return self._dlog(x) % self.n

    def mu_exp(self, u: int) -> int:
        """Exponent k with eps(u) = zeta_n^k for u in mu_n(F_q)."""
        e = self._dlog(u)
        assert e % ((self.q - 1) // self.n) == 0, "not an n-th root of unity"
        return (e // ((self.q - 1) // self.n)) % self.n

    def zeta_n(self, k: int) -> Cyc:
        return self.K.zeta(self.zn * k)

    def zeta_q(self, k: int) -> Cyc:
        return self.K.zeta(self.zq * k)

    def tau(self, j: int) -> Cyc:
        """tau(eps chi^j) = sum_{y in F_q^x} eps(chi(y))^j e_o(y)."""
        hist = [0] * self.N
        for y in range(1, self.q):
            hist[(self.zn * j * self.chi_exp(y) + self.zq * y) % self.N] += 1
        t = self.K.from_hist(hist)
        return -t if "tau_sign" in FAULTS else t

    def eps_chi_minus1(self) -> int:
        """Exponent of eps(chi(-1))."""
        return self.chi_exp(self.q - 1)

    # -- polynomials -----------------------------------------------------------
    def P(self, coeffs) -> flint.nmod_poly:
        return flint.nmod_poly([int(c) % self.q for c in coeffs], self.q)

    def T(self) -> flint.nmod_poly:
        return self.P([0, 1])

    def monic(self, d: int):
        """All monic polynomials of degree d."""
        q = self.q
        for low in itertools.product(range(q), repeat=d):
            yield self.P(list(low) + [1])

    def residues(self, d: int):
        """All polynomials of degree < d (a complete residue system modulo any modulus of degree d)."""
        q = self.q
        for low in itertools.product(range(q), repeat=d):
            yield self.P(list(low))

    @staticmethod
    def key(f: flint.nmod_poly) -> tuple:
        return tuple(int(c) for c in f.coeffs())

    # -- the n-th power residue symbol ----------------------------------------
    def symbol_res(self, a: flint.nmod_poly, c: flint.nmod_poly) -> int | None:
        """Exponent of eps((a/c)_n) for monic c, by the resultant route; None if (a,c) != 1."""
        if c.degree() == 0:
            return 0
        r = int(c.resultant(a)) % self.q
        if r == 0:
            return None
        k = self.chi_exp(r)
        if "symbol_res" in FAULTS and self.key(c) == (1, 1):
            k = (k + 1) % self.n
        return k

    def symbol_frob(self, a: flint.nmod_poly, Pp: flint.nmod_poly) -> int | None:
        """Exponent of eps((a/P)_n) for monic irreducible P, by Frobenius: a^((|P|-1)/n) mod P."""
        d = Pp.degree()
        am = a % Pp
        if am.is_zero():
            return None
        e = (self.q ** d - 1) // self.n
        b = am.pow_mod(e, Pp)
        assert b.degree() == 0, "power residue is not a constant"
        k = self.mu_exp(int(b[0]))
        if "symbol" in FAULTS and self.key(Pp) == (1, 1):
            k = (k + 1) % self.n
        return k

    def factor(self, c: flint.nmod_poly):
        """[(P, e)] with P monic irreducible."""
        if c.degree() == 0:
            return []
        lead, fac = c.factor()
        return [(P, int(e)) for P, e in fac]

    def symbol(self, a: flint.nmod_poly, c: flint.nmod_poly) -> int | None:
        """Exponent of eps((a/c)_n) for monic c, by factorization and Frobenius."""
        k = 0
        for Pp, e in self.factor(c):
            s = self.symbol_frob(a, Pp)
            if s is None:
                return None
            k += e * s
        return k % self.n

    # -- the additive character ------------------------------------------------
    def e_exp(self, b: flint.nmod_poly, c: flint.nmod_poly) -> int:
        """Exponent l with e(b/c) = zeta_q^l, for monic c: the coefficient of T^(deg c - 1) in b mod c."""
        d = c.degree()
        if d == 0:
            return 0
        r = b % c
        return int(r[d - 1]) % self.q if r.degree() >= d - 1 else 0


# ---------------------------------------------------------------------------
# 3. Vectorized tables over a complete residue system
# ---------------------------------------------------------------------------

#: digit matrices: DIGITS[(q, d)][code, i] is the coefficient of T^i of the
#: polynomial with integer code sum_i y_i q^i, for the q^d polynomials of degree < d.
_DIGITS: dict[tuple[int, int], np.ndarray] = {}


def digits(q: int, d: int) -> np.ndarray:
    key = (q, d)
    if key not in _DIGITS:
        codes = np.arange(q ** d, dtype=np.int64)
        _DIGITS[key] = np.stack([(codes // q ** i) % q for i in range(d)], axis=1) if d else np.zeros((1, 0), dtype=np.int64)
    return _DIGITS[key]


def code_of(S: "Setup", f: flint.nmod_poly, d: int) -> int:
    """Integer code of f (of degree < d) in the digit convention above."""
    c = 0
    for i, a in enumerate(f.coeffs()):
        if i >= d:
            assert int(a) == 0
            continue
        c += int(a) * S.q ** i
    return c


def poly_of_code(S: "Setup", code: int, d: int) -> flint.nmod_poly:
    return S.P([(code // S.q ** i) % S.q for i in range(d)])


def symbol_table_res(S: "Setup", c: flint.nmod_poly) -> np.ndarray:
    """Exponent of eps((y/c)_n) for every y of degree < deg c, -1 where (y,c) != 1.

    Resultant route, one resultant per residue: the brute-force reference."""
    d = c.degree()
    out = np.empty(S.q ** d, dtype=np.int64)
    for code, y in enumerate(_residues_in_code_order(S, d)):
        k = S.symbol_res(y, c)
        out[code] = -1 if k is None else k
    return out


def _residues_in_code_order(S: "Setup", d: int):
    D = digits(S.q, d)
    for row in D:
        yield S.P(list(row))


def reduction_matrix(S: "Setup", d: int, m: flint.nmod_poly) -> np.ndarray:
    """Matrix M over F_q with (y mod m) = M y for y of degree < d (coefficient vectors)."""
    e = m.degree()
    M = np.zeros((e, d), dtype=np.int64)
    for i in range(d):
        r = S.P([0] * i + [1]) % m
        for k, a in enumerate(r.coeffs()):
            M[k, i] = int(a)
    return M


@lru_cache(maxsize=None)
def _log_table(q: int, n: int, Pkey: tuple) -> np.ndarray:
    """For a monic irreducible P: exponent of eps((y/P)_n) at every residue code mod P (-1 at 0).

    Built from a primitive element of F_q[T]/P: the symbol of gamma^k is the
    exponent of eps(gamma^(k (|P|-1)/n)), which is k mod n once eps(gamma^((|P|-1)/n))
    is read off by Frobenius (a constant in mu_n(F_q))."""
    S = _SETUPS[(q, n)]
    Pp = S.P(list(Pkey))
    d = Pp.degree()
    size = q ** d
    # find a primitive element
    order = size - 1
    primes = [p for p in range(2, order + 1) if order % p == 0 and all(p % s for s in range(2, int(p ** 0.5) + 1))]
    gamma = None
    for code in range(1, size):
        cand = poly_of_code(S, code, d)
        ok = True
        for p in primes:
            if (cand.pow_mod(order // p, Pp) - S.P([1])).is_zero():
                ok = False
                break
        if ok:
            gamma = cand
            break
    assert gamma is not None
    base = S.symbol_frob(gamma, Pp)  # exponent of eps((gamma/P))
    table = np.full(size, -1, dtype=np.int64)
    x = S.P([1])
    for k in range(order):
        table[code_of(S, x, d)] = (k * base) % n
        x = (x * gamma) % Pp
    return table


_SETUPS: dict[tuple[int, int], "Setup"] = {}


def symbol_table_crt(S: "Setup", c: flint.nmod_poly) -> np.ndarray:
    """Same table as ``symbol_table_res`` by factorization, CRT and discrete logs."""
    d = c.degree()
    D = digits(S.q, d)
    out = np.zeros(S.q ** d, dtype=np.int64)
    bad = np.zeros(S.q ** d, dtype=bool)
    for Pp, e in S.factor(c):
        M = reduction_matrix(S, d, Pp)
        res = (D @ M.T) % S.q
        dP = Pp.degree()
        codes = res @ (S.q ** np.arange(dP, dtype=np.int64))
        tab = _log_table(S.q, S.n, S.key(Pp))
        vals = tab[codes]
        bad |= vals < 0
        out = out + e * np.where(vals < 0, 0, vals)
    out = out % S.n
    out[bad] = -1
    return out


def e_table(S: "Setup", r: flint.nmod_poly, c: flint.nmod_poly) -> np.ndarray:
    """l(y) with e(r y / c) = zeta_q^l(y) for every y of degree < deg c."""
    d = c.degree()
    if d == 0:
        return np.zeros(1, dtype=np.int64)
    lam = np.zeros(d, dtype=np.int64)
    for i in range(d):
        lam[i] = S.e_exp(r * S.P([0] * i + [1]), c)
    return (digits(S.q, d) @ lam) % S.q


def hist_to_cyc(S: "Setup", expo: np.ndarray, weights=None) -> "Cyc":
    """sum over entries of zeta_N^expo (times integer weights)."""
    h = np.bincount(expo % S.N, weights=weights, minlength=S.N)
    return S.K.from_hist(np.rint(h).astype(np.int64) if weights is not None else h)


# ---------------------------------------------------------------------------
# 4. Gauss sums
# ---------------------------------------------------------------------------


def gauss_brute(S: "Setup", r: flint.nmod_poly, j: int, c: flint.nmod_poly, route: str = "res",
                table: np.ndarray | None = None) -> "Cyc":
    """g(r, eps^j, c) by summing over all y mod c (zero extension at non-units)."""
    if c.degree() == 0:
        return S.K.one
    if table is None:
        table = symbol_table_res(S, c) if route == "res" else symbol_table_crt(S, c)
    l = e_table(S, r, c)
    ok = table >= 0
    expo = S.zn * j * table[ok] + S.zq * l[ok]
    g = hist_to_cyc(S, expo)
    return -g if "gauss_brute_sign" in FAULTS else g


def is_squarefree(S: Setup, c: flint.nmod_poly) -> bool:
    return c.degree() == 0 or c.gcd(c.derivative()).degree() == 0


def mobius(S: Setup, c: flint.nmod_poly) -> int:
    fac = S.factor(c)
    if any(e > 1 for _, e in fac):
        return 0
    return (-1) ** len(fac)


def gauss_dh(S: Setup, r: flint.nmod_poly, j: int, c: flint.nmod_poly, variant: str = "2014") -> Cyc:
    """The Davenport-Hasse closed form for (r, c) = 1 (Patterson 2014, section 2):

    g(r, eps, c) = mu(c) eps((r/c)^(-1) (c'/c)) (-tau(eps chi))^deg c,

    applied to eps^j.  ``variant="2007"`` uses the 2007 note's ((-r)/c)^(-1).
    """
    m = mobius(S, c)
    if m == 0:
        return S.K.zero
    rr = r if variant == "2014" else -r
    kr = S.symbol_res(rr, c)
    kd = S.symbol_res(c.derivative(), c)
    assert kr is not None and kd is not None
    t = -S.tau(j)
    g = m * S.zeta_n(j * (kd - kr)) * (t ** c.degree())
    return -g if "dh_sign" in FAULTS else g


# -- the structural route: factorization, CRT, prime powers, prime Gauss sums --


@lru_cache(maxsize=None)
def _prime_gauss_cached(q: int, n: int, Pkey: tuple, m: int, route: str) -> "Cyc":
    S = _SETUPS[(q, n)]
    Pp = S.P(list(Pkey))
    if route == "brute":
        return gauss_brute(S, S.P([1]), m, Pp, route="crt")
    # Davenport-Hasse: G_m(P) = -eps((P'/P))^m (-tau(eps chi^m))^deg P
    kd = S.symbol_res(Pp.derivative(), Pp)
    return -(S.zeta_n(m * kd) * ((-S.tau(m)) ** Pp.degree()))


def prime_gauss(S: "Setup", Pp: flint.nmod_poly, m: int, route: str = "dh") -> "Cyc":
    """G_m(P) = sum_{y mod P} eps((y/P))^m e(y/P) for m != 0 mod n."""
    m %= S.n
    assert m != 0
    G = _prime_gauss_cached(S.q, S.n, S.key(Pp), m, route)
    if "gauss_sign" in FAULTS and Pp.degree() == 2 and m == 1:
        G = -G
    if "prime_gauss_all" in FAULTS:
        G = -G
    return G


def valuation(f: flint.nmod_poly, Pp: flint.nmod_poly) -> int:
    if f.is_zero():
        return 10 ** 9
    v = 0
    while True:
        qt, rm = divmod(f, Pp)
        if not rm.is_zero():
            return v
        f = qt
        v += 1


def gauss_prime_power(S: "Setup", r: flint.nmod_poly, j: int, Pp: flint.nmod_poly, e: int,
                      route: str = "dh") -> "Cyc":
    """g(r, eps^j, P^e) from the prime-power reduction (no sum over residues)."""
    Q = S.q ** Pp.degree()
    v = valuation(r, Pp)
    m = (j * e) % S.n
    if m == 0:
        # Ramanujan sum for the principal character extended by zero
        val = (Q ** e if v >= e else 0) - (Q ** (e - 1) if v >= e - 1 else 0)
        return S.K.scalar(val)
    if v != e - 1:
        return S.K.zero
    rp = r
    for _ in range(e - 1):
        rp = rp // Pp
    k = S.symbol_frob(rp, Pp)
    return S.K.scalar(Q ** (e - 1)) * S.zeta_n(-m * k) * prime_gauss(S, Pp, m, route)


def gauss_struct(S: "Setup", r: flint.nmod_poly, j: int, c: flint.nmod_poly, route: str = "dh") -> "Cyc":
    """g(r, eps^j, c) by CRT over the prime-power factors of c (twisted multiplicativity)."""
    fac = S.factor(c)
    out = S.K.one
    expo = 0
    for (P1, e1) in fac:
        out = out * gauss_prime_power(S, r, j, P1, e1, route)
        if out.is_zero():
            return out
    for a in range(len(fac)):
        for b in range(a + 1, len(fac)):
            (P1, e1), (P2, e2) = fac[a], fac[b]
            s12 = S.symbol_frob(P1, P2)
            s21 = S.symbol_frob(P2, P1)
            expo += j * e1 * e2 * (s12 + s21)
    return out * S.zeta_n(expo)


# ---------------------------------------------------------------------------
# 5. Patterson's coefficients C, Psi, rho_0 (Patterson 2007, 2014)
# ---------------------------------------------------------------------------


def C_sum(S: "Setup", r: flint.nmod_poly, j: int, i: int, route: str = "struct") -> "Cyc":
    """C(r, eps^j, i) = sum over monic c of degree i of g(r, eps^j, c)."""
    tot = S.K.zero
    if route == "brute":
        for c in S.monic(i):
            tot = tot + gauss_brute(S, r, j, c)
        return tot
    for c in S.monic(i):
        tot = tot + gauss_struct(S, r, j, c)
    return tot


def C_star_fast(S: "Setup", r: flint.nmod_poly, j: int, i: int) -> "Cyc":
    """C*(r, eps^j, i): sum over squarefree monic c of degree i coprime to r, by the
    Davenport-Hasse form, accumulated as a signed histogram of roots of unity."""
    hist = np.zeros(S.N, dtype=np.int64)
    for c in S.monic(i):
        if i > 0 and c.gcd(r).degree() > 0:
            continue
        m = mobius(S, c)
        if m == 0:
            continue
        kr = S.symbol_res(r, c) if i > 0 else 0
        kd = S.symbol_res(c.derivative(), c) if i > 0 else 0
        hist[(S.zn * j * (kd - kr)) % S.N] += m
    return S.K.from_hist(hist) * ((-S.tau(j)) ** i)


def _rstar_candidates(S: "Setup", r: flint.nmod_poly, maxdeg: int):
    primes = [P for P, _ in S.factor(r)]
    out = []

    def rec(idx, cur):
        if idx == len(primes):
            out.append(cur)
            return
        P = primes[idx]
        x = cur
        while x.degree() <= maxdeg:
            rec(idx + 1, x)
            x = x * P

    rec(0, S.P([1]))
    return [x for x in out if x.degree() <= maxdeg]


def C_fast(S: "Setup", r: flint.nmod_poly, j: int, i: int) -> "Cyc":
    """C(r, eps^j, i) by Patterson's decomposition c = r* c_1 (2007, eq. (5)):

    C(r,eps,i) = sum_{r*} g(r,eps,r*) eps(chi(-1))^((i-1) deg r*) C*(r r*^(n-2), eps, i - deg r*).
    """
    tot = S.K.zero
    sgn = S.eps_chi_minus1()
    for rs in _rstar_candidates(S, r, i):
        g = gauss_struct(S, r, j, rs)
        if g.is_zero():
            continue
        rr = r * (rs ** (S.n - 2)) if S.n >= 2 else r
        tot = tot + g * S.zeta_n(j * sgn * (i - 1) * rs.degree()) * C_star_fast(S, rr, j, i - rs.degree())
    return tot


def psi_coeffs(S: "Setup", Cvals: list) -> list:
    """T-coefficients D_l of Psi = (1 - q^(n+1) T)/(1 - q^n T) * sum_l C_l T^l."""
    q, n = S.q, S.n
    out = []
    for l in range(len(Cvals)):
        v = Cvals[l]
        for m in range(l):
            v = v - Cvals[m] * ((q - 1) * q ** (n * (l - m)))
        out.append(v)
    return out


def R_index(S: "Setup", degr: int, i: int) -> int:
    """R = floor((1 + deg r - i)/n)."""
    return (1 + degr - i) // S.n


def rho0(S: "Setup", r: flint.nmod_poly, j: int, i: int, Cfun=None, extra: int = 0):
    """rho_0(r, eps^j, i) = Psi(r, eps^j, i, q^(-n-1)), with Psi read from C sums.

    Returns (rho0, D) where D lists the T-coefficients of Psi up to degree R + extra,
    so the coefficients above R can be checked to vanish."""
    if Cfun is None:
        Cfun = C_fast
    R = R_index(S, r.degree(), i)
    top = max(R, -1) + extra
    Cvals = [Cfun(S, r, j, i + S.n * l) for l in range(top + 1)]
    D = psi_coeffs(S, Cvals)
    val = S.K.zero
    for l in range(min(R, top) + 1):
        val = val + D[l] * Fraction(1, S.q ** ((S.n + 1) * l))
    return val, D


# -- relations among the rho_0 (Patterson 2014, section 2) ---------------------


def hecke_infinity(S: "Setup", r: flint.nmod_poly, j: int, rho: dict) -> list:
    """Check the Hecke relations at infinity for every 0 <= i < n.

    ``rho[i]`` holds rho_0(r, eps^j, i).  Returns a list of (i, i', ok) records:
    rho_0(r,i) = eps chi(-1)^(i sigma) tau(eps chi^(i-i')) q^(-1) rho_0(r,i') and
    rho_0(r,i') = eps chi(-1)^(i' sigma) tau(eps chi^(i'-i)) rho_0(r,i) for i < i',
    and rho_0(r, i) = 0 when i = i'."""
    n, q = S.n, S.q
    sgn = S.eps_chi_minus1()
    sigma = r.degree() + 1
    out = []
    for i in range(n):
        ip = (sigma - i) % n
        if ip == i:
            out.append((i, ip, rho[i].is_zero()))
        elif i < ip:
            A = S.zeta_n(j * sgn * i * sigma) * S.tau(j * (i - ip))
            B = S.zeta_n(j * sgn * ip * sigma) * S.tau(j * (ip - i))
            ok1 = rho[i] == A * rho[ip] * Fraction(1, q)
            ok2 = rho[ip] == B * rho[i]
            out.append((i, ip, ok1 and ok2))
    return out


def finite_hecke_rhs(S: "Setup", ro: flint.nmod_poly, Pp: flint.nmod_poly, jj: int, j: int, i: int,
                     rho_fun) -> "Cyc":
    """Right side of Patterson's finite Hecke relation (2014, section 2) for
    rho_0(r_o P^jj, eps^j, i), 0 <= jj < n-1, r_o coprime to P."""
    n, q = S.n, S.q
    sgn = S.eps_chi_minus1()
    D = (jj + 1) * Pp.degree()
    carry = (i % n) - ((i - D) % n) - (D % n)  # 0 or -n
    assert carry in (0, -n)
    qexp = (carry // n) * (n + 1) + (D % n) - (D // n)
    factor = S.zeta_n(j * sgn * i * D) * gauss_struct(S, -ro, j * (jj + 1), Pp)
    val = rho_fun(ro * Pp ** (n - 2 - jj), (i - D) % n)
    if qexp >= 0:
        return factor * val * (q ** qexp)
    return factor * val * Fraction(1, q ** (-qexp))


# ---------------------------------------------------------------------------
# 6. Truncated power series in several variables, with Cyc coefficients
# ---------------------------------------------------------------------------


class Series:
    """A truncated multivariate power series {exponent tuple: Cyc}.

    ``bound`` is a function of an exponent tuple returning True when the
    monomial is kept."""

    def __init__(self, K: CycField, nvars: int, bound, terms=None):
        self.K = K
        self.nvars = nvars
        self.bound = bound
        self.terms = {} if terms is None else {e: c for e, c in terms.items() if bound(e) and not c.is_zero()}

    @classmethod
    def const(cls, K, nvars, bound, c):
        return cls(K, nvars, bound, {(0,) * nvars: c})

    @classmethod
    def mono(cls, K, nvars, bound, expo, c):
        return cls(K, nvars, bound, {tuple(expo): c})

    def copy(self):
        return Series(self.K, self.nvars, self.bound, dict(self.terms))

    def __add__(self, o):
        out = dict(self.terms)
        for e, c in o.terms.items():
            out[e] = out[e] + c if e in out else c
        return Series(self.K, self.nvars, self.bound, out)

    def __sub__(self, o):
        out = dict(self.terms)
        for e, c in o.terms.items():
            out[e] = out[e] - c if e in out else -c
        return Series(self.K, self.nvars, self.bound, out)

    def scale(self, c):
        return Series(self.K, self.nvars, self.bound, {e: v * c for e, v in self.terms.items()})

    def __mul__(self, o):
        if not isinstance(o, Series):
            return self.scale(o)
        out: dict = {}
        for e1, c1 in self.terms.items():
            for e2, c2 in o.terms.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                if not self.bound(e):
                    continue
                v = c1 * c2
                out[e] = out[e] + v if e in out else v
        return Series(self.K, self.nvars, self.bound, out)

    def geometric(self):
        """1/(1 - self) for a series with zero constant term."""
        assert (0,) * self.nvars not in self.terms
        out = Series.const(self.K, self.nvars, self.bound, self.K.one)
        power = out
        while True:
            power = power * self
            if not power.terms:
                break
            out = out + power
        return out

    def equals(self, o) -> bool:
        keys = set(self.terms) | set(o.terms)
        z = self.K.zero
        return all(self.terms.get(e, z) == o.terms.get(e, z) for e in keys)

    def diff_keys(self, o) -> list:
        keys = set(self.terms) | set(o.terms)
        z = self.K.zero
        return sorted(e for e in keys if not self.terms.get(e, z) == o.terms.get(e, z))

    def coeff(self, e):
        return self.terms.get(tuple(e), self.K.zero)


def hecke_infinity_2007(S: "Setup", r: flint.nmod_poly, j: int, rho: dict) -> list:
    """Patterson 2007, relations (9) and (10), read with rho -> rho_0:

    rho(r, i) = tau(eps^(2i-1-deg r)) eps chi(-1)^(i(1+deg r)) rho(r, (1+deg r-i)_n) q^(2i+E-3-deg r),
    E = 2 + floor((2i-2-deg r)/n), and rho(r, i) = 0 when 2i = 1 + deg r mod n."""
    n, q = S.n, S.q
    sgn = S.eps_chi_minus1()
    dr = r.degree()
    out = []
    for i in range(n):
        ip = (1 + dr - i) % n
        if (2 * i - 1 - dr) % n == 0:
            out.append((i, ip, rho[i].is_zero()))
            continue
        E = 2 + (2 * i - 2 - dr) // n
        qe = 2 * i + E - 3 - dr
        rhs = S.tau(j * (2 * i - 1 - dr)) * S.zeta_n(j * sgn * i * (1 + dr)) * rho[ip]
        rhs = rhs * (q ** qe) if qe >= 0 else rhs * Fraction(1, q ** (-qe))
        out.append((i, ip, rho[i] == rhs))
    return out


# ---------------------------------------------------------------------------
# 7. The base probe over F_q[T]: cubic theta row, sextic averaging (n = 6 symbols)
# ---------------------------------------------------------------------------


class Probe:
    """The F_q[T] transplant of the 7/8 paper's base probe (Section 6, eq. general-probe).

    The sextic symbol chi_c(a) = (a/c)_6, the excluded set S = {T}, b_* = T, the
    auxiliary character xi = chi_T^xi_j (nonprincipal at T, order dividing 6), and a
    target character eta modulo T^2:  eta(a) = eps(a_0)^eta_e zeta_q^(eta_t a_1/a_0)
    for a = a_0 + a_1 T + ... with a_0 != 0.  The angular character alpha of the
    number field becomes the degree character lambda_alpha^deg with
    lambda_alpha = (-tau(eps chi^2)/sqrt q)^3, the Eisenstein-Weil value that makes
    gamma_2(c)^3 = mu(c) alpha(c).  The other phases are the paper's definitions
    with F_q[T] reciprocity: R(a, b) = eps(chi(-1))^(deg a deg b) and
    G(c) = conj(chi_c(4)) Gamma(c), Gamma(c) = |c|^(-1/2) sum_{x mod c} e(x^2/c).
    """

    def __init__(self, S: "Setup", eta_e: int = 1, eta_t: int = 1, xi_j: int = 1, eta_fun=None):
        assert S.n % 6 == 0 and S.n == 6, "the sextic probe needs n = 6"
        self.eta_fun = eta_fun
        self.S = S
        self.K = S.K
        self.q = S.q
        self.T = S.P([0, 1])
        self.one = S.P([1])
        self.xi_j = xi_j
        self.eta_e = eta_e
        self.eta_t = eta_t
        self.sgn = S.eps_chi_minus1()  # eps(chi(-1)) = zeta_6^sgn
        self.gxi = gauss_brute(S, self.one, xi_j, self.T)  # g_xi(T, 1)
        self.tau = self.gxi / S.sqrtq
        self.lam_alpha = ((-S.tau(2)) / S.sqrtq) ** 3
        self._Gamma_cache: dict = {}

    # -- characters ------------------------------------------------------------
    def chi(self, c: flint.nmod_poly, a: flint.nmod_poly) -> int | None:
        """Exponent of chi_c(a) = (a/c)_6 for monic c (None at a non-unit)."""
        return self.S.symbol_res(a, c)

    def chi_val(self, c, a, power: int = 1) -> "Cyc":
        k = self.chi(c, a)
        if k is None:
            return self.K.zero
        return self.S.zeta_n(power * k)

    def xi(self, m: flint.nmod_poly) -> "Cyc":
        return self.chi_val(self.T, m, self.xi_j)

    def R(self, a: flint.nmod_poly, b: flint.nmod_poly) -> "Cyc":
        return self.S.zeta_n(self.sgn * a.degree() * b.degree())

    def alpha(self, c: flint.nmod_poly) -> "Cyc":
        return self.lam_alpha ** c.degree()

    def eta(self, a: flint.nmod_poly) -> "Cyc":
        """The target character, a Dirichlet character modulo T^2 (zero at multiples of T),
        or the function ``eta_fun`` when one was given (the rival uses this)."""
        if self.eta_fun is not None:
            return self.eta_fun(a)
        e = self.eta_exp(a)
        return self.K.zero if e is None else self.K.zeta(e)

    def eta_exp(self, a: flint.nmod_poly) -> int | None:
        """Exponent e with eta(a) = zeta_N^e for the character modulo T^2 (None at multiples of T)."""
        assert self.eta_fun is None
        co = a.coeffs()
        a0 = int(co[0]) if co else 0
        a1 = int(co[1]) if len(co) > 1 else 0
        if a0 % self.q == 0:
            return None
        inv = pow(a0, self.q - 2, self.q)
        return (self.S.zn * self.eta_e * self.S.chi_exp(a0) + self.S.zq * ((self.eta_t * a1 * inv) % self.q)) % self.S.N

    def Xi(self, a: flint.nmod_poly) -> "Cyc":
        return self.xi(a) * self.chi_val(a, self.T)

    def gamma(self, c: flint.nmod_poly, j: int) -> "Cyc":
        """gamma_j(c) = |c|^(-1/2) g_{chi_c^j}(c, 1) (structural route)."""
        return gauss_struct(self.S, self.one, j, c) / (self.S.sqrtq ** c.degree())

    def Gamma(self, c: flint.nmod_poly, route: str = "closed") -> "Cyc":
        """Gamma(c) = |c|^(-1/2) sum_{x mod c} e(x^2/c)."""
        if route == "brute":
            d = c.degree()
            hist = [0] * self.S.N
            for x in self.S.residues(d):
                hist[(self.S.zq * self.S.e_exp(x * x, c)) % self.S.N] += 1
            return self.K.from_hist(hist) / (self.S.sqrtq ** d)
        # closed form for q = 3 mod 4 or 1 mod 4 (checked against the brute route):
        # Gamma(c) = (-1)^(D(D-1)/2 * (q-1)/2) (tau_quad/sqrt q)^D with D = deg c,
        # tau_quad = sum_{x in F_q} e_o(x^2).
        D = c.degree()
        tq = self.S.sqrtq if self.q % 4 == 1 else self.K.zeta(self.S.N // 4) * self.S.sqrtq
        sign = (-1) ** ((D * (D - 1) // 2) * ((self.q - 1) // 2) % 2)
        return (tq / self.S.sqrtq) ** D * sign

    def G(self, c: flint.nmod_poly, route: str = "closed") -> "Cyc":
        return self.chi_val(c, self.S.P([4])).conj() * self.Gamma(c, route)

    # -- the Poisson coefficient F(s, A, H) of eq. (local-F) ---------------------
    def gauss_mod_TA(self, A: flint.nmod_poly, k: flint.nmod_poly) -> "Cyc":
        """g_{xi chi_A}(T A, k) for A coprime to T, by CRT over T and A."""
        S = self.S
        km = k % self.T
        if km.is_zero():
            return self.K.zero
        gT = self.xi(k).conj() * self.gxi
        return self.xi(A) * self.chi_val(A, self.T) * gT * gauss_struct(S, k, 1, A)

    def F_def(self, s: flint.nmod_poly, A: flint.nmod_poly, H: flint.nmod_poly) -> "Cyc":
        """F(s, A, H) = sum_{d mod s, H = T A d mod s} chi_s(d) g_{xi chi_A}(T A, (H - T A d)/s)."""
        S = self.S
        TA = self.T * A
        if s.degree() == 0:
            return self.gauss_mod_TA(A, H)
        g = TA.gcd(s)
        if not (H % g).is_zero():
            return self.K.zero
        sp, TAp, Hp = s // g, TA // g, H // g
        if sp.degree() == 0:
            d0 = S.P([0])
        else:
            _, inv, _ = TAp.xgcd(sp)
            d0 = (Hp * inv) % sp
        tot = self.K.zero
        for e in S.residues(g.degree()):
            d = (d0 + sp * e) % s
            kd = self.chi(s, d)
            if kd is None:
                continue
            num = H - TA * d
            k, rem = divmod(num, s)
            assert rem.is_zero()
            tot = tot + S.zeta_n(kd) * self.gauss_mod_TA(A, k)
        return tot

    def F_brute(self, s, A, H) -> "Cyc":
        """F(s, A, H) by summing over d mod s and x mod T A (small degrees only)."""
        S = self.S
        TA = self.T * A
        hist = [0] * S.N
        dTA = TA.degree()
        tabTA = [None] * (S.q ** dTA)
        for code, x in enumerate(_residues_in_code_order(S, dTA)):
            kx = self.chi(self.T, x)
            ka = self.chi(A, x) if A.degree() > 0 else 0
            tabTA[code] = None if (kx is None or ka is None) else (self.xi_j * kx + ka)
        xs = list(_residues_in_code_order(S, dTA))
        for d in _residues_in_code_order(S, s.degree()):
            if not ((H - TA * d) % s).is_zero() if s.degree() > 0 else False:
                continue
            kd = self.chi(s, d) if s.degree() > 0 else 0
            if kd is None:
                continue
            k = (H - TA * d) // s if s.degree() > 0 else H
            for code, x in enumerate(xs):
                kk = tabTA[code]
                if kk is None:
                    continue
                l = S.e_exp(k * x, TA)
                hist[(S.zn * (kd + kk) + S.zq * l) % S.N] += 1
        return self.K.from_hist(hist)

    # -- the local scalar C_p(t, k, j') of eq. (local-scalar-definition) ----------
    def C_p_def(self, Pp: flint.nmod_poly, t: int, k: int, jp: int) -> "Cyc":
        """C_p(t,k,j') = sum_{d mod p^k, p^j' = p^t d mod p^k} chi_p^k(d) g_{chi_p^t}(p^t, (p^j' - p^t d)/p^k).

        The outer sum is enumerated; the inner Gauss sum uses the prime-power
        reduction (checked against brute force by the tests)."""
        S = self.S
        pk = Pp ** k
        pt = Pp ** t
        pj = Pp ** jp
        tot = self.K.zero
        if k == 0:
            # modulus one: d = 0 and chi^0 at modulus one means one
            return gauss_prime_power(S, pj, 1, Pp, t) if t > 0 else self.K.one
        # the solutions d mod p^k of p^j' = p^t d (mod p^k), enumerated directly
        if t >= k:
            if jp < k:
                return self.K.zero
            sols = list(S.residues(pk.degree()))
        else:
            if jp < t:
                return self.K.zero
            d0 = Pp ** (jp - t) % (Pp ** (k - t))
            step = Pp ** (k - t)
            sols = [(d0 + step * e) % pk for e in S.residues(pt.degree())]
        for d in sols:
            if not ((pj - pt * d) % pk).is_zero():
                continue
            kd = S.symbol_frob(d, Pp)
            if kd is None:
                continue  # chi_p^k(d) is zero at multiples of p, also when 6 | k
            y = (pj - pt * d) // pk
            g = gauss_prime_power(S, y, 1, Pp, t) if t > 0 else self.K.one
            tot = tot + S.zeta_n(k * kd) * g
        return tot

    def C_p_closed(self, Pp: flint.nmod_poly, t: int, k: int, jp: int) -> "Cyc":
        """The paper's complete evaluation, eq. (local-scalar-values)."""
        S = self.S
        Q = S.q ** Pp.degree()
        if t == 0 and k == 0:
            return self.K.one
        if t == 0:
            return self.K.one if jp == 0 else self.K.zero
        if k == 0:
            return self.g_pt(Pp, t, t, jp)
        if k == 1 and jp >= 1:
            G1 = prime_gauss(S, Pp, 1)
            om = self.chi_val(Pp, S.P([S.q - 1]))
            return om.conj() * G1 * self.g_pt(Pp, t - 1, t, jp - 1)
        return self.K.zero

    def g_pt(self, Pp, r: int, t: int, jp: int) -> "Cyc":
        """g_{chi_p^r}(p^t, p^j') from the displayed formula above eq. (local-scalar-definition)."""
        S = self.S
        Q = S.q ** Pp.degree()
        if r % 6 != 0:
            if jp != t - 1:
                return self.K.zero
            G = prime_gauss(S, Pp, r)
            return G * (Q ** (t - 1))
        val = (Q ** t if jp >= t else 0) - (Q ** (t - 1) if jp >= t - 1 else 0)
        return self.K.scalar(val)

    # -- the factorization of F(s, A, H) (lines 3927-3951) --------------------------
    def F_local(self, s, A, H) -> "Cyc":
        """sqrt(q) tau xi(A) conj(xi(H/s)) prod_{p | sA} U_p C_p(t_p, k_p, j'_p)."""
        S = self.S
        if (H % self.T).is_zero():
            return self.K.zero
        out = S.sqrtq * self.tau * self.xi(A) * self.xi(H).conj() * self.xi(s)
        primes = {S.key(P): P for P, _ in S.factor(s * A)}
        for P in primes.values():
            t = valuation(A, P)
            k = valuation(s, P)
            jp = valuation(H, P)
            hp = H
            for _ in range(jp):
                hp = hp // P
            sp = s
            for _ in range(k):
                sp = sp // P
            Ap = A
            for _ in range(t):
                Ap = Ap // P
            U = (self.chi_val(P, hp, k - t) * self.chi_val(P, sp, t) * self.chi_val(P, Ap, t - k)
                 * self.chi_val(P, self.T, t - k))
            out = out * U * self.C_p_def(P, t, k, jp)
            if out.is_zero():
                return out
        return out

    # -- the coefficient K of eq. (local-full-coefficient) -------------------------
    def K_def(self, c, n, s, a, u, F_route: str = "def") -> "Cyc":
        A = c * n ** 3
        H = u * a ** 6
        Fv = self.F_def(s, A, H) if F_route == "def" else (self.F_brute(s, A, H) if F_route == "brute" else self.F_local(s, A, H))
        if Fv.is_zero():
            return Fv
        pre = self.chi_val(s, self.T) / (self.S.sqrtq * self.tau * self.xi(s) * self.xi(u).conj())
        theta = self.gamma(c, 2) * self.alpha(A).conj() * self.G(A).conj()
        return Fv * pre * theta * self.eta(A) * self.Xi(A).inverse() * self.R(A, s)

    # -- the local summand of eq. (local-P) -------------------------------------------
    def local_params(self, Pp, u):
        S = self.S
        j = valuation(u, Pp)
        uu = u
        for _ in range(j):
            uu = uu // Pp
        rho = self.chi_val(Pp, uu)
        om = self.chi_val(Pp, S.P([S.q - 1]))
        eta_p = self.eta(Pp)
        al = self.alpha(Pp)
        a_p = al.conj() ** 3 * eta_p ** 3
        b_p = al.conj() ** 2 * eta_p ** 2 * self.chi_val(Pp, S.P([4])).conj()
        return j, rho, om, eta_p, a_p, b_p

    def kappa(self, Pp, e0: int, l: int, k: int, m: int, u, closed: bool = False) -> "Cyc":
        S = self.S
        j, rho, om, eta_p, a_p, b_p = self.local_params(Pp, u)
        t = e0 + 3 * l
        g1 = self.gamma(Pp, 1)
        g3 = self.gamma(Pp, 3)
        Cp = (self.C_p_closed if closed else self.C_p_def)(Pp, t, k, j + 6 * m)
        if Cp.is_zero():
            return Cp
        v = (g1.inverse() * eta_p * (-1)) ** e0 * (a_p * g3.conj()) ** l * rho ** (k - t)
        v = v * om ** (t * k - e0 * l - l * (l - 1) // 2)
        return v * Cp

    # -- Lemma 7.1: the local factor as a series in (x_p, w_p, v_p) -------------------
    #    x_p = Q^-x, w_p = Q^-w, v_p = Q^-6z; a monomial x^(e0+3l) w^k v^m carries
    #    the normalization Q^(-e0/2 - l) of eq. (local-P).
    def P_local_def(self, Pp, u, bound) -> Series:
        S = self.S
        dP = Pp.degree()
        sq = S.sqrtq ** dP  # Q^(1/2)
        out = {}
        Xm, Wm, Vm = bound.maxes
        for e0 in (0, 1):
            for l in range(0, Xm // 3 + 1):
                ex = e0 + 3 * l
                if ex > Xm:
                    continue
                for k in range(0, Wm + 1):
                    for m in range(0, Vm + 1):
                        kap = self.kappa(Pp, e0, l, k, m, u)
                        if kap.is_zero():
                            continue
                        norm = (sq ** (e0 + 2 * l)).inverse()
                        out[(ex, k, m)] = kap * norm
        return Series(self.K, 3, bound, out)

    def P_local_closed(self, Pp, u, bound) -> Series:
        """Lemma 7.1, eq. (old-eq:5.13a) with the six values J_j."""
        S = self.S
        K = self.K
        dP = Pp.degree()
        Q = S.q ** dP
        sq = S.sqrtq ** dP
        j, rho, om, eta_p, a_p, b_p = self.local_params(Pp, u)
        one = Series.const(K, 3, bound, K.one)
        mono = lambda e, c: Series.mono(K, 3, bound, e, c)
        V = mono((0, 0, 1), K.one)
        Wl = mono((0, 1, 0), rho)
        Rr = mono((6, 0, 1), a_p ** 2 * (Q ** 4))
        inv1mV = V.geometric()
        inv1mR = Rr.geometric()
        out = inv1mV
        if j == 0:
            out = out + Wl * Wl.geometric()
        xw = mono((1, 1, 0), K.one)
        term = Rr * (1 - Fraction(1, Q)) - xw * (eta_p * (Q - 1)) * (V if j <= 1 else one)
        if j == 0:
            J = mono((1, 0, 0), -(eta_p * rho.inverse())) + Wl * Rr
        elif j == 1:
            J = mono((1, 1, 0), eta_p)
        elif j == 2:
            J = mono((3, 0, 0), a_p * rho.inverse() ** 3 * sq ** 3)
        elif j == 3:
            J = mono((3, 1, 0), -(eta_p * b_p * rho.inverse() ** 2 * Q ** 2)) + mono((4, 0, 0), b_p ** 2 * rho.inverse() ** 4 * Q ** 2)
        elif j == 4:
            J = mono((4, 1, 0), -(eta_p * a_p * rho.inverse() ** 3 * sq ** 5))
        else:
            J = mono((6, 0, 0), -(a_p ** 2 * Q ** 3))
        out = out + inv1mR * (term * inv1mV + J)
        return out


class Bound:
    """Monomials with exponents at most (Xm, Wm, Vm)."""

    def __init__(self, Xm: int, Wm: int, Vm: int):
        self.maxes = (Xm, Wm, Vm)

    def __call__(self, e) -> bool:
        return e[0] <= self.maxes[0] and e[1] <= self.maxes[1] and e[2] <= self.maxes[2]


# ---------------------------------------------------------------------------
# 8. Global objects: monic polynomials coprime to T, primes, the high series
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def primes_upto(q: int, n: int, d: int) -> tuple:
    """Monic irreducibles of degree <= d other than T, as coefficient tuples."""
    S = _SETUPS[(q, n)]
    out = []
    for e in range(1, d + 1):
        for c in S.monic(e):
            fac = S.factor(c)
            if len(fac) == 1 and fac[0][1] == 1 and S.key(c) != (0, 1):
                out.append(S.key(c))
    return tuple(out)


def monic_coprime_T(S: "Setup", d: int) -> list:
    T = S.P([0, 1])
    if d == 0:
        return [S.P([1])]
    return [c for c in S.monic(d) if not (c % T).is_zero()]


def theta_indices(S: "Setup", D: int) -> list:
    """All (c, n) with c squarefree monic, n monic, deg(c n^3) = D, coprime to T."""
    out = []
    for dn in range(0, D // 3 + 1):
        dc = D - 3 * dn
        for n_ in monic_coprime_T(S, dn):
            for c in monic_coprime_T(S, dc):
                if mobius(S, c) != 0:
                    out.append((c, n_))
    return out


def euler_product(Pr: "Probe", u, bound: Bound, closed: bool = True) -> Series:
    """prod over primes p != T of the local factor, in global variables X, W, V
    (x_p = X^deg p, w_p = W^deg p, v_p = V^deg p)."""
    S = Pr.S
    Xm, Wm, Vm = bound.maxes
    dmax = max(Xm, Wm, Vm, 1)
    out = Series.const(Pr.K, 3, bound, Pr.K.one)
    for key in primes_upto(S.q, S.n, dmax):
        Pp = S.P(list(key))
        dP = Pp.degree()
        lb = Bound(Xm // dP, Wm // dP, Vm // dP)
        loc = (Pr.P_local_closed if closed else Pr.P_local_def)(Pp, u, lb)
        glob = {}
        for (ex, ew, ev), cval in loc.terms.items():
            glob[(ex * dP, ew * dP, ev * dP)] = cval
        out = out * Series(Pr.K, 3, bound, glob)
    return out


def high_series_def(Pr: "Probe", u, bound: Bound, F_route: str = "def") -> Series:
    """F_u = sum over (c, n, s, a) of K(c,n,s,a;u) q^(-deg c/2 - deg n) X^deg(cn^3) W^deg s V^deg a."""
    S = Pr.S
    Xm, Wm, Vm = bound.maxes
    out = {}
    for D in range(0, Xm + 1):
        for (c, n_) in theta_indices(S, D):
            norm = (S.sqrtq ** (c.degree() + 2 * n_.degree())).inverse()
            for ds in range(0, Wm + 1):
                for s in monic_coprime_T(S, ds):
                    for da in range(0, Vm + 1):
                        for a in monic_coprime_T(S, da):
                            kv = Pr.K_def(c, n_, s, a, u, F_route)
                            if kv.is_zero():
                                continue
                            e = (D, ds, da)
                            out[e] = out[e] + kv * norm if e in out else kv * norm
    return Series(Pr.K, 3, bound, out)


def K_product(Pr: "Probe", c, n_, s, a, u, closed: bool = False) -> "Cyc":
    """prod over primes p | c n s a u (p != T) of the local summand kappa_p."""
    S = Pr.S
    primes = {}
    for f in (c, n_, s, a, u):
        for Pp, _ in S.factor(f):
            if S.key(Pp) != (0, 1):
                primes[S.key(Pp)] = Pp
    out = Pr.K.one
    for Pp in primes.values():
        out = out * Pr.kappa(Pp, valuation(c, Pp), valuation(n_, Pp), valuation(s, Pp),
                             valuation(a, Pp), u, closed)
        if out.is_zero():
            return out
    return out


# ---------------------------------------------------------------------------
# 9. The probe at degree parameters (D_X, D_s, D_A), three representations
# ---------------------------------------------------------------------------
#
#   I(D_X, D_s, D_A) = sum_{deg s = D_s} sum_{deg A = D_A, A = c n^3} w(s, A)
#                      sum_{deg m < D_X + D_s + 1} xi(m) chi_A(m) g_{chi_s}(s, -m),
#   w(s, A) = chi_s(T) / (tau xi(s)) * gamma_2(c) conj(alpha(A)) eta(A) Xi(A)^-1 R(A, s)
#             conj(G(A)) q^(-deg c/2 - deg n).
#
# The box deg m < D_X + D_s + 1 is the function-field W_0(q_m/(q_b* q_s X)) with
# X = q^D_X, the sharp degree cut-offs replace W_1 and the Mellin integral in Z.
# Finite Poisson summation on F_q[T] modulo M = T s A gives exactly
#   sum_{deg m < N} f(m) = q^(D_X + D_s - D_A) sum_{0 != H, deg H < D_A - D_X} F(s, A, H),
# and H = u a^6 splits the frequencies into the rows u of eq. (probe-poisson-identity).


def _box_symbol_exps(S: "Setup", box: np.ndarray, modulus: flint.nmod_poly) -> np.ndarray:
    """Exponent of (m/modulus)_n for every box element (rows of digit matrix), -1 at non-units."""
    d = modulus.degree()
    if d == 0:
        return np.zeros(box.shape[0], dtype=np.int64)
    N = box.shape[1]
    if S.q ** d <= 4 * box.shape[0]:
        tab = symbol_table_crt(S, modulus)
        M = reduction_matrix(S, N, modulus)
        codes = ((box @ M.T) % S.q) @ (S.q ** np.arange(d, dtype=np.int64))
        return tab[codes]
    out = np.empty(box.shape[0], dtype=np.int64)
    for i, row in enumerate(box):
        k = S.symbol_res(S.P(list(row)), modulus)
        out[i] = -1 if k is None else k
    return out


def probe_direct(Pr: "Probe", DX: int, Ds: int, DA: int) -> "Cyc":
    S = Pr.S
    q, n = S.q, S.n
    N = DX + Ds + 1
    box = digits(q, N)
    xi_tab = np.array([-1] + [(Pr.xi_j * S.chi_exp(a)) % n for a in range(1, q)], dtype=np.int64)
    xi_e = xi_tab[box[:, 0]]
    total = Pr.K.zero
    Aparts = []
    for (c, n_) in theta_indices(S, DA):
        A = c * n_ ** 3
        wA = (Pr.gamma(c, 2) * Pr.alpha(A).conj() * Pr.eta(A) * Pr.Xi(A).inverse() * Pr.G(A).conj()
              * (S.sqrtq ** (c.degree() + 2 * n_.degree())).inverse())
        if wA.is_zero():
            continue
        Aparts.append((A, wA, _box_symbol_exps(S, box, A)))
    for s in monic_coprime_T(S, Ds):
        ws = Pr.chi_val(s, Pr.T) / (Pr.tau * Pr.xi(s))
        ks = _box_symbol_exps(S, box, s)
        sqf = mobius(S, s) != 0
        if sqf:
            gs1 = gauss_struct(S, Pr.one, 1, s)
            km1 = S.symbol_res(S.P([q - 1]), s) if Ds > 0 else 0
            pref = gs1 * S.zeta_n(-km1)
        else:
            M = reduction_matrix(S, N, s)
            rcodes = ((box @ M.T) % q) @ (q ** np.arange(Ds, dtype=np.int64))
            gtab = [gauss_struct(S, -poly_of_code(S, cd, Ds), 1, s) for cd in range(q ** Ds)]
        for (A, wA, kA) in Aparts:
            if sqf:
                ok = (xi_e >= 0) & (kA >= 0) & (ks >= 0)
                expo = S.zn * ((xi_e + kA - ks) % n)
                inner = hist_to_cyc(S, expo[ok]) * pref
            else:
                ok = (xi_e >= 0) & (kA >= 0)
                e6 = (xi_e + kA) % n
                cnt = np.bincount(rcodes[ok] * n + e6[ok], minlength=(q ** Ds) * n).reshape(q ** Ds, n)
                inner = Pr.K.zero
                for r in range(q ** Ds):
                    if cnt[r].any() and not gtab[r].is_zero():
                        h = np.zeros(S.N, dtype=np.int64)
                        for k6 in range(n):
                            h[(S.zn * k6) % S.N] += cnt[r, k6]
                        inner = inner + gtab[r] * S.K.from_hist(h)
            if inner.is_zero():
                continue
            total = total + ws * wA * Pr.R(A, s) * inner
    return total


def nonzero_frequencies(S: "Setup", Dmax: int) -> list:
    """All H != 0 coprime to T with deg H < Dmax (any leading coefficient)."""
    out = []
    T = S.P([0, 1])
    for d in range(0, Dmax):
        for lc in range(1, S.q):
            for low in itertools.product(range(S.q), repeat=d):
                H = S.P(list(low) + [lc])
                if not (H % T).is_zero():
                    out.append(H)
    return out


def probe_poisson(Pr: "Probe", DX: int, Ds: int, DA: int) -> "Cyc":
    S = Pr.S
    Hs = nonzero_frequencies(S, DA - DX)
    total = Pr.K.zero
    for (c, n_) in theta_indices(S, DA):
        A = c * n_ ** 3
        wA = (Pr.gamma(c, 2) * Pr.alpha(A).conj() * Pr.eta(A) * Pr.Xi(A).inverse() * Pr.G(A).conj()
              * (S.sqrtq ** (c.degree() + 2 * n_.degree())).inverse())
        if wA.is_zero():
            continue
        for s in monic_coprime_T(S, Ds):
            ws = Pr.chi_val(s, Pr.T) / (Pr.tau * Pr.xi(s))
            acc = Pr.K.zero
            for H in Hs:
                acc = acc + Pr.F_def(s, A, H)
            if acc.is_zero():
                continue
            total = total + ws * wA * Pr.R(A, s) * acc
    e = DX + Ds - DA
    return total * (S.q ** e) if e >= 0 else total * Fraction(1, S.q ** (-e))


def sixth_power_free_rows(S: "Setup", Dmax: int) -> list:
    """(u, a) with u sixth-power free (any unit factor), a monic, both coprime to T,
    deg u + 6 deg a < Dmax: the decomposition H = u a^6 of the frequencies."""
    out = []
    for H in nonzero_frequencies(S, Dmax):
        lc = int(H.coeffs()[-1])
        Hm = H * S.P([pow(lc, S.q - 2, S.q)])
        a = S.P([1])
        u = S.P([1])
        for Pp, e in S.factor(Hm):
            a = a * Pp ** (e // 6)
            u = u * Pp ** (e % 6)
        out.append((u * S.P([lc]), a))
    return out


def probe_euler(Pr: "Probe", DX: int, Ds: int, DA: int, closed: bool = True) -> "Cyc":
    """The Poisson rows evaluated through the Euler product of local factors."""
    S = Pr.S
    total = Pr.K.zero
    for (u, a) in sixth_power_free_rows(S, DA - DX):
        da = a.degree()
        B = Bound(DA, Ds, da)
        ser = euler_product(Pr, u, B, closed)
        coef = ser.coeff((DA, Ds, da))
        if coef.is_zero():
            continue
        total = total + Pr.xi(u).conj() * coef
    e = DX + Ds - DA
    total = total * S.sqrtq
    return total * (S.q ** e) if e >= 0 else total * Fraction(1, S.q ** (-e))


# ---------------------------------------------------------------------------
# 9b. Vectorized Poisson and Euler sides for D_s = 0 (s = 1)
# ---------------------------------------------------------------------------
#
# With s = 1 the Poisson coefficient is F(1, A, H) = xi(A) chi_A(T) conj(xi(H)) g_xi(T, 1)
# g_{chi_A}(A, H), and for squarefree A, g_{chi_A}(A, H) = conj(chi_A(H)) g_{chi_A}(A, 1) when
# (H, A) = 1 and 0 otherwise, so the frequency sum is one character histogram per A.
#
# On the Euler side only the monomials W^0 V^0 enter (deg s = deg a = 0; a = 1 because
# 6 deg a <= deg H < D_A - D_X <= 6).  Setting w = v = 0 in eq. (old-eq:5.13a) kills R, W_loc
# and every term carrying Q^-w, so P_p = 1 + J_j(p) restricted to w = v = 0:
#
#   j = 0: 1 - eta(p) conj(chi_p(u)) X^deg p      j = 2: 1 + a_p rho^-3 Q^(3/2) X^(3 deg p)
#   j = 3: 1 + b_p^2 rho^-4 Q^2 X^(4 deg p)        j = 5: 1 - a_p^2 Q^3 X^(6 deg p)
#   j = 1, 4: 1,
#
# and the product over p not dividing u T is the Moebius sum
# sum_{m sf, (m, uT) = 1} mu(m) eta(m) conj((u/m)_6) X^deg m.  This is a second route to the
# Euler side (no series arithmetic, no local factor from the definition), derived here by
# hand from the closed form and checked against ``probe_euler`` where both run.


def _symbol_exps_table(S: "Setup", box: np.ndarray, modulus: flint.nmod_poly) -> np.ndarray:
    """Exponent of (m/modulus)_n for every box row (-1 at non-units): ``_box_symbol_exps``,
    which uses the full residue table when the box is large against q^deg and one resultant
    per row otherwise."""
    return _box_symbol_exps(S, box, modulus)


def _frequency_box(S: "Setup", L: int):
    """Digit rows of every H with deg H < L and H(0) != 0 (so H != 0 and (H, T) = 1)."""
    box = digits(S.q, L)
    return box[box[:, 0] != 0]


def probe_poisson_s1(Pr: "Probe", DX: int, DA: int) -> "Cyc":
    """The Poisson representation for D_s = 0, vectorized over the frequencies H."""
    S = Pr.S
    q, n = S.q, S.n
    L = DA - DX
    if L <= 0:
        return Pr.K.zero
    box = _frequency_box(S, L)
    xi_tab = np.array([0] + [(Pr.xi_j * S.chi_exp(a)) % n for a in range(1, q)], dtype=np.int64)
    xi_e = xi_tab[box[:, 0]]
    total = Pr.K.zero
    for (c, n_) in theta_indices(S, DA):
        A = c * n_ ** 3
        wA = (Pr.gamma(c, 2) * Pr.alpha(A).conj() * Pr.eta(A) * Pr.Xi(A).inverse() * Pr.G(A).conj()
              * (S.sqrtq ** (c.degree() + 2 * n_.degree())).inverse())
        if wA.is_zero():
            continue
        pref = Pr.xi(A) * Pr.chi_val(A, Pr.T) * Pr.gxi
        if mobius(S, A) != 0:
            kA = _symbol_exps_table(S, box, A)
            ok = kA >= 0
            expo = (-(xi_e[ok] + kA[ok])) % n
            hsum = hist_to_cyc(S, S.zn * expo) * gauss_struct(S, Pr.one, 1, A)
        else:
            # g_{chi_A}(A, H) can be nonzero only if v_P(H) >= e - 1 at every P^e || A, e >= 2
            keep = np.ones(box.shape[0], dtype=bool)
            for Pp, e in S.factor(A):
                if e >= 2:
                    M = reduction_matrix(S, L, Pp ** (e - 1))
                    keep &= ~((box @ M.T) % q).any(axis=1)
            hsum = Pr.K.zero
            for row in box[keep]:
                H = S.P(list(row))
                g = gauss_struct(S, H, 1, A)
                if not g.is_zero():
                    hsum = hsum + g * Pr.xi(H).conj()
        if hsum.is_zero():
            continue
        total = total + wA * pref * hsum
    total = total / Pr.tau
    e = DX - DA
    return total * (q ** e) if e >= 0 else total * Fraction(1, q ** (-e))


def _squarefree_moduli(S: "Setup", Pr: "Probe", Dmax: int) -> dict:
    """{D: (digit matrix of m with D+1 columns, mu(m), eta exponent of m)} for squarefree monic
    m coprime to T of degree D <= Dmax."""
    out = {}
    for D in range(Dmax + 1):
        rows, mus, ets = [], [], []
        for m in monic_coprime_T(S, D):
            mu = mobius(S, m)
            if mu == 0:
                continue
            k = Pr.eta_exp(m)
            co = [int(x) for x in m.coeffs()] + [0] * (D + 1)
            rows.append(co[:D + 1])
            mus.append(mu)
            ets.append(k)
        out[D] = (np.array(rows, dtype=np.int64).reshape(len(rows), D + 1), np.array(mus, dtype=np.int64),
                  np.array(ets, dtype=np.int64))
    return out


def _row_local_poly(Pr: "Probe", u: flint.nmod_poly, DA: int) -> list:
    """Coefficients (X^0 .. X^DA) of prod over p | u of P_p at w = v = 0 (the list above)."""
    S = Pr.S
    K = Pr.K
    out = [K.one] + [K.zero] * DA
    for Pp, j in S.factor(u):
        dP = Pp.degree()
        Q = S.q ** dP
        sq = S.sqrtq ** dP
        _, rho, om, eta_p, a_p, b_p = Pr.local_params(Pp, u)
        if j == 2:
            term = (3 * dP, a_p * rho.inverse() ** 3 * sq ** 3)
        elif j == 3:
            term = (4 * dP, b_p ** 2 * rho.inverse() ** 4 * Q ** 2)
        elif j == 5:
            term = (6 * dP, -(a_p ** 2 * Q ** 3))
        else:
            continue  # j = 1, 4: the factor is 1 at w = v = 0
        e, cval = term
        new = list(out)
        for k in range(DA + 1 - e):
            if not out[k].is_zero():
                new[k + e] = new[k + e] + out[k] * cval
        out = new
    return out


def probe_euler_s1(Pr: "Probe", DX: int, DA: int) -> "Cyc":
    """The Euler representation for D_s = 0: each row u is a Moebius sum times the local
    factors at the primes of u, all at w = v = 0 (see the comment above)."""
    S = Pr.S
    q, n, N = S.q, S.n, S.N
    L = DA - DX
    if L <= 0:
        return Pr.K.zero
    assert L <= 6, "a = 1 needs deg H < 6"
    mods = _squarefree_moduli(S, Pr, DA)
    sgn = S.eps_chi_minus1()
    total = Pr.K.zero
    for H in nonzero_frequencies(S, L):
        u = H
        du = u.degree()
        lc = int(u.coeffs()[-1])
        um = u * S.P([pow(lc, q - 2, q)])
        klc = S.chi_exp(lc)
        coef = Pr.K.zero
        loc = _row_local_poly(Pr, u, DA)
        for D in range(DA + 1):
            if loc[DA - D].is_zero():
                continue
            rows, mus, ets = mods[D]
            if rows.shape[0] == 0:
                continue
            if du == 0:
                tabk = np.zeros(rows.shape[0], dtype=np.int64)
            else:
                tabk = _symbol_exps_table(S, rows, um)
            ok = tabk >= 0
            # (u/m)_6 = chi(lc)^D chi(-1)^(D du) ((m mod um)/um)_6
            k = (D * klc + D * du * sgn + tabk[ok]) % n
            expo = (ets[ok] - S.zn * k) % N
            h = np.zeros(N, dtype=np.int64)
            np.add.at(h, expo, mus[ok])
            coef = coef + S.K.from_hist(h) * loc[DA - D]
        if coef.is_zero():
            continue
        total = total + Pr.xi(u).conj() * coef
    total = total * S.sqrtq
    e = DX - DA
    return total * (q ** e) if e >= 0 else total * Fraction(1, q ** (-e))


# ---------------------------------------------------------------------------
# 10. The biquadratic theta over F_13[T] (n = 4): components, forced zeros, 3-body defect
# ---------------------------------------------------------------------------


def hecke_infinity_corrected(S: "Setup", r: flint.nmod_poly, j: int, rho: dict) -> list:
    """Patterson 2007 (9)-(10) with the last argument read as the unreduced index
    1 + deg r - i, converted with rho(r, i + nN) = q^((n+1)N) rho(r, i):

    rho_0(r,i) = tau(eps chi^(2i-1-deg r)) eps chi(-1)^(i(1+deg r)) q^(2i+E-3-deg r+(n+1)R) rho_0(r,i'),
    E = 2 + floor((2i-2-deg r)/n), R = floor((1+deg r-i)/n), i' = (1+deg r-i) mod n."""
    n, q = S.n, S.q
    sgn = S.eps_chi_minus1()
    dr = r.degree()
    out = []
    for i in range(n):
        ip = (1 + dr - i) % n
        if (2 * i - 1 - dr) % n == 0:
            out.append((i, ip, rho[i].is_zero()))
            continue
        E = 2 + (2 * i - 2 - dr) // n
        Rr = (1 + dr - i) // n
        qe = 2 * i + E - 3 - dr + (n + 1) * Rr
        rhs = S.tau(j * (2 * i - 1 - dr)) * S.zeta_n(j * sgn * i * (1 + dr)) * rho[ip]
        rhs = rhs * (q ** qe) if qe >= 0 else rhs * Fraction(1, q ** (-qe))
        out.append((i, ip, rho[i] == rhs))
    return out


def hecke_infinity_both(S: "Setup", r: flint.nmod_poly, j: int, rho: dict, rho_minus: dict) -> dict:
    """The Hecke relation at infinity in the two additive characters.

    ``rho`` holds rho_0(r, eps^j, i) for e = e_o(a_-1) (the 2014 character, this hunt's),
    ``rho_minus`` holds rho_0(-r, eps^j, i), which is rho_0(r, eps^j, i) for e = e_o(-a_-1)
    (the 2007 note's e_omega, omega = dx).  With sigma = 1 + deg r, the unreduced reading of
    (9), and tau(eps chi^m) = sum eps(chi(y))^m e_o(y) in both:

    * in the 2007 character the sign is eps(chi(-1))^(i sigma), as printed;
    * in the 2014 character it is eps(chi(-1))^((i+1) sigma).

    The two signs differ by eps(chi(-1))^sigma, which is 1 when q = 1 mod 2n."""
    n, q = S.n, S.q
    sgn = S.eps_chi_minus1()
    dr = r.degree()
    sigma = 1 + dr
    out = {"2007_character": [0, 0], "2014_character": [0, 0]}
    for i in range(n):
        ip = (sigma - i) % n
        for name, rr, extra in (("2007_character", rho_minus, 0), ("2014_character", rho, 1)):
            out[name][1] += 1
            if (2 * i - 1 - dr) % n == 0:
                out[name][0] += int(rr[i].is_zero())
                continue
            E = 2 + (2 * i - 2 - dr) // n
            Rr = (1 + dr - i) // n
            qe = 2 * i + E - 3 - dr + (n + 1) * Rr
            rhs = S.tau(j * (2 * i - 1 - dr)) * S.zeta_n(j * sgn * (i + extra) * sigma) * rr[ip]
            rhs = rhs * (q ** qe) if qe >= 0 else rhs * Fraction(1, q ** (-qe))
            out[name][0] += int(rr[i] == rhs)
    return out


def zero_reason(S: "Setup", degr: int, i: int) -> str | None:
    """Why rho_0(r, eps, i) must vanish for every r of degree degr, if it must."""
    if (1 + degr - i) // S.n < 0:
        return "R<0"
    if (2 * i - 1 - degr) % S.n == 0:
        return "i=i'"
    return None


def hypergeometric_sum(S: "Setup", r: flint.nmod_poly, j: int) -> "Cyc":
    """sum over a in F_q with r(a) != 0 of conj(eps(chi(r(a))))^j: the classical
    character sum in Patterson's C*(r, eps, 1) = (-tau(eps chi)) * this."""
    hist = [0] * S.N
    for a in range(S.q):
        v = sum(int(cf) * pow(a, k, S.q) for k, cf in enumerate(r.coeffs())) % S.q
        if v == 0:
            continue
        hist[(-S.zn * j * S.chi_exp(v)) % S.N] += 1
    return S.K.from_hist(hist)


def three_body_defect(S: "Setup", f: dict, P1, P2, P3) -> "Cyc":
    """|f(P1P2P3)|^2 |f(P1)f(P2)f(P3)|^2 / (|f(P1P2) f(P1P3) f(P2P3)|^2 |f(1)|^2).

    ``f`` maps coefficient-tuple keys of squarefree products to Cyc values.  For a
    function whose modulus is multiplicative this is exactly 1."""
    k = S.key
    num = f[k(P1 * P2 * P3)].abs2() * f[k(P1)].abs2() * f[k(P2)].abs2() * f[k(P3)].abs2()
    den = f[k(P1 * P2)].abs2() * f[k(P1 * P3)].abs2() * f[k(P2 * P3)].abs2() * f[k(S.P([1]))].abs2()
    return num / den


# ---------------------------------------------------------------------------
# 11. Dirichlet characters modulo T^e, their L-polynomials, and the rival
# ---------------------------------------------------------------------------


class CharModT3:
    """chi(a) = eps(a_0)^e zeta_q^(alpha x + beta (y - x^2/2)) for a = a_0 (1 + x T + y T^2) mod T^3.

    Primitive modulo T^3 when beta != 0, odd (nontrivial on F_q^x) when e != 0 mod n."""

    def __init__(self, S: "Setup", e: int, alpha: int, beta: int):
        self.S, self.e, self.alpha, self.beta = S, e, alpha, beta
        self.half = pow(2, S.q - 2, S.q)

    def exp(self, a: flint.nmod_poly) -> int | None:
        S = self.S
        q = S.q
        co = [int(c) for c in a.coeffs()] + [0, 0, 0]
        a0, a1, a2 = co[0] % q, co[1] % q, co[2] % q
        if a0 == 0:
            return None
        inv = pow(a0, q - 2, q)
        x, y = (a1 * inv) % q, (a2 * inv) % q
        add = (self.alpha * x + self.beta * (y - x * x * self.half)) % q
        return (S.zn * self.e * S.chi_exp(a0) + S.zq * add) % S.N

    def __call__(self, a: flint.nmod_poly) -> "Cyc":
        k = self.exp(a)
        return self.S.K.zero if k is None else self.S.K.zeta(k)

    def conj(self) -> "CharModT3":
        return CharModT3(self.S, -self.e, -self.alpha, -self.beta)


def L_poly(S: "Setup", chi, maxdeg: int) -> list:
    """Coefficients c_d = sum over monic a of degree d of chi(a), d = 0..maxdeg."""
    out = []
    for d in range(maxdeg + 1):
        hist = [0] * S.N
        for a in S.monic(d):
            k = chi.exp(a)
            if k is not None:
                hist[k] += 1
        out.append(S.K.from_hist(hist))
    return out


class Rival:
    """chi(a) + eps(chi) conj(chi)(a): the function-field Davenport-Heilbronn rival.

    Its Dirichlet series is L(u, chi) + eps L(u, conj chi), proportional to
    eps^(-1/2) L(u, chi) + eps^(1/2) L(u, conj chi), with the same zeros."""

    def __init__(self, S: "Setup", chi: CharModT3):
        self.S = S
        self.chi = chi
        self.chib = chi.conj()
        L = L_poly(S, chi, 4)
        self.L = L
        assert all(c.is_zero() for c in L[3:]), "L(u, chi) has degree <= 2 for conductor T^3"
        self.eps = L[2] / S.q  # root number, from c_2 = q eps
        self.Lb = L_poly(S, self.chib, 2)

    def __call__(self, a: flint.nmod_poly) -> "Cyc":
        """The coefficient d(a) = (chi(a) + eps conj(chi)(a)) / (1 + eps), so that d(1) = 1."""
        return (self.chi(a) + self.eps * self.chib(a)) / (1 + self.eps)

    def poly(self) -> list:
        """The rival polynomial L(u, chi) + eps L(u, conj chi), coefficients of u^0, u^1, u^2."""
        return [self.L[d] + self.eps * self.Lb[d] for d in range(3)]


# ---------------------------------------------------------------------------
# 12. Fault planting, cache control
# ---------------------------------------------------------------------------


class planted:
    """Context manager: ``with planted("gauss_sign"): ...`` switches a planted defect on.

    Faults: ``gauss_sign`` negates the structural prime Gauss sum G_1 at every prime
    of degree 2; ``symbol`` shifts the Frobenius-route residue symbol modulo T + 1 by
    one step; ``symbol_res`` does the same in the resultant route."""

    def __init__(self, *names):
        self.names = set(names)

    def __enter__(self):
        clear_caches()
        FAULTS.update(self.names)
        return self

    def __exit__(self, *exc):
        FAULTS.difference_update(self.names)
        clear_caches()
        return False


def clear_caches():
    _prime_gauss_cached.cache_clear()
    _log_table.cache_clear()
    primes_upto.cache_clear()


# ---------------------------------------------------------------------------
# 13. Reports: each part writes results_<part>.json (checkpoint per part)
# ---------------------------------------------------------------------------


def cyc_record(z: "Cyc") -> dict:
    c = z.to_complex()
    return {"poly": str(z.p), "N": z.K.N, "re": c.real, "im": c.imag, "abs": abs(c)}


def lin_poly(S: "Setup", a: int) -> flint.nmod_poly:
    """The monic linear polynomial T - a."""
    return S.P([(-a) % S.q, 1])


def part_sources() -> dict:
    import hashlib

    cache = Path(os.environ.get("ZETA_LAB_CACHE", os.path.expanduser("~/.cache/zeta-lab")))

    def sha(p):
        p = cache / p
        return hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None

    return {
        "paper_tex": sha("openai-math-adc7f124/paper.tex"),
        "patterson_2007_pdf": sha("ffprobe-sources-patterson2007/patterson2007.pdf"),
        "patterson_2014_eprint": sha("ffprobe-sources-patterson2014/eprint.bin"),
        "patterson_2014_tex": sha("ffprobe-sources-patterson2014/JHPaper.tex"),
    }



def affine_transform(S: "Setup", r: flint.nmod_poly, a: int, b: int) -> flint.nmod_poly:
    """a^(-deg r) r(a x + b): the monic image of r under x -> a x + b."""
    arg = S.P([b, a])
    out = S.P([0])
    for e, cf in enumerate(r.coeffs()):
        out = out + S.P([int(cf)]) * arg ** e
    lc = int(out.coeffs()[-1])
    return out * S.P([pow(lc, S.q - 2, S.q)])

def part_step1(full: bool = True) -> dict:
    """Step 1: the function-field formulas, checked by brute force at q = 7, n = 3."""
    out: dict = {}
    t0 = time.time()
    S = Setup(7, 3)
    maxd = 3 if full else 2
    # (a) the two residue-symbol routes
    n_c = n_bad = 0
    for d in range(1, maxd + 1):
        for c in S.monic(d):
            n_c += 1
            n_bad += int((symbol_table_res(S, c) != symbol_table_crt(S, c)).any())
    out["symbol_routes"] = {"q": 7, "n": 3, "max_deg": maxd, "moduli": n_c, "disagree": n_bad}
    # (b) Davenport-Hasse, both printed forms, three (q, n)
    dh = {}
    for (q, n, md) in ((7, 3, maxd), (7, 6, maxd), (13, 4, 2)):
        Sx = Setup(q, n)
        cnt = {"2014": 0, "2007_own_character": 0, "2007_with_2014_character": 0}
        tot = 0
        nonsf_zero = nonsf_tot = 0
        for d in range(1, md + 1):
            for c in Sx.monic(d):
                tab = symbol_table_res(Sx, c)
                sf = is_squarefree(Sx, c)
                for rd in range(0, 3):
                    for r in Sx.monic(rd):
                        if r.gcd(c).degree() > 0:
                            continue
                        if not sf:
                            if rd <= 1:
                                nonsf_tot += 1
                                nonsf_zero += int(gauss_brute(Sx, r, 1, c, table=tab).is_zero())
                            continue
                        for j in range(1, n):
                            g = gauss_brute(Sx, r, j, c, table=tab)
                            gm = gauss_brute(Sx, -r, j, c, table=tab)  # the character e_o(-a_-1)
                            tot += 1
                            cnt["2014"] += int(gauss_dh(Sx, r, j, c, "2014") != g)
                            cnt["2007_own_character"] += int(gauss_dh(Sx, r, j, c, "2007") != gm)
                            cnt["2007_with_2014_character"] += int(gauss_dh(Sx, r, j, c, "2007") != g)
        dh[f"q{q}_n{n}"] = {"max_deg": md, "checked": tot, "mismatches": cnt,
                             "nonsquarefree_checked": nonsf_tot, "nonsquarefree_zero": nonsf_zero}
    out["davenport_hasse"] = dh
    # (c) structural Gauss sums against brute force (all r, all c, j = 1, 2)
    bad = tot = 0
    for d in range(1, maxd + 1):
        for c in S.monic(d):
            tab = symbol_table_res(S, c)
            for rd in range(0, maxd + 1):
                for r in S.monic(rd):
                    for j in (1, 2):
                        tot += 1
                        bad += int(gauss_brute(S, r, j, c, table=tab) != gauss_struct(S, r, j, c))
    out["structural_vs_brute"] = {"max_deg_c": maxd, "max_deg_r": maxd, "checked": tot, "mismatches": bad}
    # (d) three routes to C(r, eps^j, i)
    T = S.P([0, 1])
    rs = [S.P([1]), T, T * lin_poly(S, 1), T * T, S.P([1, 0, 1]), T * lin_poly(S, 1) * lin_poly(S, 3),
          S.P([1, 1, 0, 1])]
    bad = tot = 0
    for r in rs:
        for j in (1, 2):
            for i in range(0, maxd + 1):
                tot += 1
                cb = C_sum(S, r, j, i, "brute")
                bad += int(not (cb == C_sum(S, r, j, i, "struct") and cb == C_fast(S, r, j, i)))
    out["C_routes"] = {"checked": tot, "mismatches": bad, "max_i": maxd}
    # (e)-(i) the coefficients and their relations
    cache: dict = {}

    def rho(r, j, i):
        key = (S.key(r), j, i % 3)
        if key not in cache:
            cache[key] = rho0(S, r, j, i % 3)[0]
        return cache[key]

    one = S.P([1])
    out["theta_base"] = {f"j{j}": {"rho0_1_0_is_1": rho(one, j, 0) == 1,
                                   "rho0_1_1_is_q_tau": rho(one, j, 1) == S.tau(j) * 7,
                                   "rho0_1_2_is_0": rho(one, j, 2).is_zero()} for j in (1, 2)}
    poly_ok = poly_tot = 0
    for r in [one, T, lin_poly(S, 1), T * lin_poly(S, 1), S.P([1, 0, 1]), T * T]:
        for j in (1, 2):
            for i in range(3):
                _, D = rho0(S, r, j, i, extra=1)
                R = R_index(S, r.degree(), i)
                poly_tot += 1
                poly_ok += int(all(x.is_zero() for x in D[max(R, -1) + 1:]))
    out["psi_polynomial"] = {"checked": poly_tot, "vanish_above_R": poly_ok}
    hinf = {"printed_2014": [0, 0], "printed_2007": [0, 0], "corrected": [0, 0]}
    rlist = [one, T, lin_poly(S, 1), T * lin_poly(S, 1), S.P([1, 0, 1]), T * lin_poly(S, 1) * lin_poly(S, 3),
             S.P([1, 1, 0, 1]), T * S.P([1, 0, 1]), T ** 3, S.P([0, 1, 0, 1]) * lin_poly(S, 2)]
    for r in rlist:
        for j in (1, 2):
            rr = {i: rho(r, j, i) for i in range(3)}
            for name, fun in (("printed_2014", hecke_infinity), ("printed_2007", hecke_infinity_2007),
                              ("corrected", hecke_infinity_corrected)):
                res = fun(S, r, j, rr)
                hinf[name][0] += sum(1 for x in res if x[2])
                hinf[name][1] += len(res)
    out["hecke_infinity"] = {k: {"hold": v[0], "checked": v[1]} for k, v in hinf.items()}
    both = {}
    for (qq, nn) in ((7, 3), (7, 6)):
        Sx = Setup(qq, nn)
        Lx = lambda a: lin_poly(Sx, a)
        tot = {"2007_character": [0, 0], "2014_character": [0, 0]}
        for r in [Sx.P([1]), Lx(1), Lx(1) * Lx(2), Sx.P([1, 0, 1]), Lx(1) * Lx(2) * Lx(3)]:
            for jj in ((1, 2) if nn == 3 else (1,)):
                rr = {i: rho0(Sx, r, jj, i)[0] for i in range(nn)}
                rm = {i: rho0(Sx, -r, jj, i)[0] for i in range(nn)}
                res = hecke_infinity_both(Sx, r, jj, rr, rm)
                for k in tot:
                    tot[k][0] += res[k][0]
                    tot[k][1] += res[k][1]
        both[f"q{qq}_n{nn}"] = {k: {"hold": v[0], "checked": v[1]} for k, v in tot.items()}
    out["hecke_infinity_both"] = both
    S = Setup(7, 3)  # restore the (7, 3) setup used below
    fh_ok = fh_tot = van_ok = van_tot = 0
    for ro, P in [(one, T), (one, lin_poly(S, 1)), (lin_poly(S, 1), T), (one, S.P([1, 0, 1])),
                  (lin_poly(S, 2), S.P([1, 0, 1])), (T * lin_poly(S, 1), lin_poly(S, 3))]:
        for jj in range(0, 2):
            for j in (1, 2):
                for i in range(3):
                    fh_tot += 1
                    fh_ok += int(rho(ro * P ** jj, j, i) == finite_hecke_rhs(S, ro, P, jj, j, i,
                                                                             lambda a, b, j=j: rho(a, j, b)))
        for j in (1, 2):
            for i in range(3):
                van_tot += 1
                van_ok += int(rho(ro * P ** 2, j, i).is_zero())
    out["finite_hecke"] = {"hold": fh_ok, "checked": fh_tot, "vanish_at_r_o_P^(n-1)": [van_ok, van_tot]}
    per_ok = per_tot = 0
    for r, b in [(T, lin_poly(S, 1)), (lin_poly(S, 2), T), (one, T), (S.P([1, 0, 1]), lin_poly(S, 4))]:
        for j in (1, 2):
            for i in range(3):
                per_tot += 1
                per_ok += int(rho(r * b ** 3, j, i) == rho(r, j, i))
    out["periodicity"] = {"hold": per_ok, "checked": per_tot}
    aff_ok = aff_tot = 0
    for r in [T, T * lin_poly(S, 1), S.P([1, 0, 1]), T * lin_poly(S, 1) * lin_poly(S, 3)]:
        k = r.degree()
        for a in (2, 3):
            for b in (0, 1, 5):
                # rt(x) = a^-k r(a x + b), monic of degree k
                rt = affine_transform(S, r, a, b)
                for j in (1, 2):
                    for i in range(3):
                        aff_tot += 1
                        pred = rho(r, j, i) * S.zeta_n(j * i * (k + 1 - i) * S.chi_exp(a))
                        aff_ok += int(rho(rt, j, i) == pred)
    out["affine_invariance"] = {"hold": aff_ok, "checked": aff_tot}
    # (j) the genuine cubic theta against the probe's gamma_2
    S6 = Setup(7, 6)
    Pr = Probe(S6)
    fam = {}
    for b in (0, 1, 2):
        rec = {}
        for d in range(0, maxd + 1):
            vals = {}
            for c in S.monic(d):
                if mobius(S, c) == 0:
                    continue
                ratio = rho(c, 2, (b - d) % 3) / Pr.gamma(S6.P([int(x) for x in c.coeffs()]), 2)
                vals[str(ratio.p)] = ratio
            rec[str(d)] = {"distinct_ratios": len(vals), "ratio": cyc_record(next(iter(vals.values())))}
        fam[f"b{b}"] = rec
    out["cubic_theta_vs_gamma2"] = fam
    out["seconds"] = round(time.time() - t0, 1)
    return out


#: the probe triples (D_X, D_s, D_A) checked in three representations; the
#: unit sum makes the probe vanish unless D_s = D_A + xi_j (mod 6), so the
#: nonzero triples are listed explicitly, up to total degree 9.
PROBE_TRIPLES_SMALL = [(0, 0, 1), (0, 0, 2), (1, 0, 2), (0, 1, 1), (0, 1, 2), (1, 1, 2), (0, 0, 3),
                       (1, 0, 3), (2, 0, 3), (0, 2, 1), (0, 2, 2), (1, 1, 3), (0, 3, 2)]
PROBE_TRIPLES_LARGE = [(1, 3, 2), (3, 0, 5), (4, 0, 5)]


def part_step2(full: bool = True, out: dict | None = None) -> dict:
    """Step 2: the F_7[T] cubic-theta probe with sextic averaging, and Lemma 7.1."""
    out = {} if out is None else out
    t0 = time.time()
    S = Setup(7, 6)
    Pr = Probe(S)
    T = Pr.T
    mon = lambda d: monic_coprime_T(S, d)
    allmon = lambda d: list(S.monic(d))
    # (a) the phase identities of the paper, read in F_7[T]
    if not ("phase_identities" in out):
        rec_bad = rec_tot = 0
        for da in range(1, 3):
            for db in range(1, 3):
                for a in allmon(da):
                    for b in allmon(db):
                        if a.gcd(b).degree() > 0:
                            continue
                        rec_tot += 1
                        rec_bad += int(not Pr.chi_val(b, a) == Pr.R(a, b) * Pr.chi_val(a, b))
        gam_bad = gam_tot = 0
        for d in range(0, 4):
            for c in allmon(d):
                gam_tot += 1
                gam_bad += int(not Pr.Gamma(c, "brute") == Pr.Gamma(c, "closed"))
        sig = {"gamma2_cubed": 0, "gamma1_gamma2": 0, "G_squarefree": 0}
        sig_tot = 0
        for d in range(1, 4):
            for c in allmon(d):
                m = mobius(S, c)
                if m == 0:
                    continue
                sig_tot += 1
                g1, g2, g3 = Pr.gamma(c, 1), Pr.gamma(c, 2), Pr.gamma(c, 3)
                sig["gamma2_cubed"] += int(not g2 ** 3 == Pr.alpha(c) * m)
                sig["gamma1_gamma2"] += int(not g1 * g2 == Pr.alpha(c) * Pr.G(c) * m)
                sig["G_squarefree"] += int(not Pr.G(c) == Pr.chi_val(c, S.P([4])).conj() * g3)
        ref_bad = ref_tot = 0
        for dv in range(0, 3):
            for dw in range(0, 3):
                for v in allmon(dv):
                    for w in allmon(dw):
                        ref_tot += 1
                        ref_bad += int(not Pr.G(v * w, "brute") == Pr.G(v, "brute") * Pr.G(w, "brute") * Pr.R(v, w))
        pp_bad = pp_tot = 0
        for key in primes_upto(7, 6, 2):
            Pp = S.P(list(key))
            pp_tot += 1
            pp_bad += int(not (Pr.G(Pp * Pp) == Pr.chi_val(Pp, S.P([4])) and Pr.G(Pp ** 3) == Pr.gamma(Pp, 3)
                              and Pr.R(Pp, Pp) == Pr.gamma(Pp, 3) ** 2 and Pr.R(Pp, Pp) == Pr.chi_val(Pp, S.P([6]))))
        out["phase_identities"] = {
            "reciprocity": {"checked": rec_tot, "mismatches": rec_bad},
            "Gamma_closed_form": {"checked": gam_tot, "mismatches": gam_bad},
            "signal": {"checked": sig_tot, "mismatches": sig},
            "G_refinement_all_pairs": {"checked": ref_tot, "mismatches": ref_bad},
            "prime_phases": {"checked": pp_tot, "mismatches": pp_bad},
            "lambda_alpha": cyc_record(Pr.lam_alpha),
        }
    # (b) three routes to F(s, A, H)
    if not ("F_routes" in out):
        bad = {"def": 0, "local": 0}
        tot = 0
        for ds in range(0, 3):
            for dA in range(0, 3):
                if ds + dA > 3:
                    continue
                for s in mon(ds):
                    for A in mon(dA):
                        for H in S.residues(2):
                            if H.is_zero():
                                continue
                            fb = Pr.F_brute(s, A, H)
                            tot += 1
                            bad["def"] += int(not fb == Pr.F_def(s, A, H))
                            bad["local"] += int(not fb == Pr.F_local(s, A, H))
        out["F_routes"] = {"checked": tot, "mismatches_vs_brute": bad}
    # (c) the local scalar C_p, definition against the paper's evaluation
    if not ("C_p_values" in out):
        bad = tot = 0
        for key in [(1, 1), (3, 1), (1, 0, 1), (3, 1, 1)]:
            Pp = S.P(list(key))
            for t in range(0, 8):
                for k in range(0, 3 if Pp.degree() == 1 else 2):
                    for jp in range(0, 9):
                        tot += 1
                        bad += int(not Pr.C_p_def(Pp, t, k, jp) == Pr.C_p_closed(Pp, t, k, jp))
        out["C_p_values"] = {"checked": tot, "mismatches": bad}
    # (d) the coefficient K separates into the local summands of eq. (local-P)
    if not ("K_multiplicative" in out):
        rows = [S.P([1]), S.P([3]), S.P([1, 1]), S.P([2, 1]) ** 2, S.P([1, 0, 1]), S.P([1, 1]) * S.P([2, 1])]
        if full:
            rows += [S.P([5, 1]) ** 3, S.P([1, 1]) ** 5 * S.P([2])]
            specs = [(rows, 3, 1, 1), (rows[:3], 2, 2, 1)]
        else:
            specs = [(rows, 2, 1, 1)]
        kres = []
        for (rws, maxA, maxs, maxa) in specs:
            bad = tot = nz = 0
            for u in rws:
                for D in range(0, maxA + 1):
                    for (c, n_) in theta_indices(S, D):
                        for ds in range(0, maxs + 1):
                            for s in mon(ds):
                                for da in range(0, maxa + 1):
                                    for a in mon(da):
                                        kd = Pr.K_def(c, n_, s, a, u)
                                        tot += 1
                                        nz += int(not kd.is_zero())
                                        bad += int(not kd == K_product(Pr, c, n_, s, a, u))
            kres.append({"rows": [str(u) for u in rws], "max_deg_A": maxA, "max_deg_s": maxs,
                         "max_deg_a": maxa, "checked": tot, "nonzero": nz, "mismatches": bad})
        out["K_multiplicative"] = kres
    # (e) Lemma 7.1: the local factor, definition against the closed form
    if not ("lemma_7_1_local" in out):
        bad = tot = 0
        for key in [(1, 1), (4, 1), (1, 0, 1)]:
            Pp = S.P(list(key))
            B = Bound(13, 3, 2) if Pp.degree() == 1 else Bound(13, 2, 2)
            for j in range(0, 6):
                for w in [S.P([1]), S.P([2]), S.P([3, 1]) if key != (4, 1) else S.P([5, 1]), S.P([1, 1, 1])]:
                    if (w % Pp).is_zero():
                        continue
                    u = Pp ** j * w
                    tot += 1
                    bad += int(not Pr.P_local_def(Pp, u, B).equals(Pr.P_local_closed(Pp, u, B)))
        out["lemma_7_1_local"] = {"checked": tot, "mismatches": bad, "bound_deg1": [13, 3, 2], "bound_deg2": [13, 2, 2]}
    # (f) the probe in three representations
    if not ("probe_representations" in out):
        trip = PROBE_TRIPLES_SMALL + (PROBE_TRIPLES_LARGE if full else [])
        recs = []
        for (DX, Ds, DA) in trip:
            t1 = time.time()
            d = probe_direct(Pr, DX, Ds, DA)
            p = probe_poisson(Pr, DX, Ds, DA)
            e = probe_euler(Pr, DX, Ds, DA)
            recs.append({"triple": [DX, Ds, DA], "direct_eq_poisson": d == p, "poisson_eq_euler": p == e,
                         "zero": d.is_zero(), "value": cyc_record(d), "seconds": round(time.time() - t1, 1)})
        out["probe_representations"] = recs
    out["seconds"] = round(time.time() - t0, 1)
    return out


#: Step 2b.  With xi = chi_T the selection rule leaves, among all triples of total degree
#: at most 6, exactly these with a nonempty frequency box (D_X < D_A): (0,2,1), (0,3,2),
#: (1,3,2) from step 2, and (0,0,5), (1,0,5) here; (3,0,5) and (4,0,5) are rerun to tie the
#: vectorized routes to step 2's values.  On the class with D_X >= D_A the frequency box is
#: empty, so the Poisson and Euler sides are 0 and the direct side must vanish too.
PROBE_TRIPLES_S0 = [(4, 0, 5), (3, 0, 5), (1, 0, 5), (0, 0, 5)]
PROBE_TRIPLES_EMPTY = [(dx, 1, 0) for dx in range(6)] + [(dx, 2, 1) for dx in (1, 2, 3)]


def selection_census(xi_j: int = 1, total: int = 6) -> dict:
    """Every triple (D_X, D_s, D_A) of total degree <= total, by how the probe is decided there."""
    out = {"off_class": [], "on_class_empty_box": [], "on_class_nonempty_box": []}
    for DX in range(total + 1):
        for Ds in range(total + 1 - DX):
            for DA in range(total + 1 - DX - Ds):
                t = [DX, Ds, DA]
                if (Ds - DA - xi_j) % 6 != 0:
                    out["off_class"].append(t)
                elif DA - DX <= 0:
                    out["on_class_empty_box"].append(t)
                else:
                    out["on_class_nonempty_box"].append(t)
    return out


def part_step2b(full: bool = True, out: dict | None = None) -> dict:
    """Step 2b: the remaining triples of total degree <= 6, by the vectorized D_s = 0 routes."""
    out = {} if out is None else out
    t0 = time.time()
    S = Setup(7, 6)
    Pr = Probe(S)
    if "census" not in out:
        out["census"] = selection_census()
    s0 = PROBE_TRIPLES_S0 if full else [(2, 0, 3), (1, 0, 3)]
    for (DX, Ds, DA) in s0:
        key = f"s0_{DX}_{Ds}_{DA}"
        if key in out:
            continue
        t1 = time.time()
        Pq = Pr if full else Probe(S, xi_j=3)
        d = probe_direct(Pq, DX, 0, DA)
        t_d = time.time() - t1
        p = probe_poisson_s1(Pq, DX, DA)
        t_p = time.time() - t1 - t_d
        e = probe_euler_s1(Pq, DX, DA)
        out[key] = {"triple": [DX, Ds, DA], "xi_j": Pq.xi_j, "direct_eq_poisson": d == p, "poisson_eq_euler": p == e,
                    "zero": d.is_zero(), "value": cyc_record(d),
                    "seconds": {"direct": round(t_d, 1), "poisson": round(t_p, 1),
                                "euler": round(time.time() - t1 - t_d - t_p, 1)}}
    for (DX, Ds, DA) in (PROBE_TRIPLES_EMPTY if full else PROBE_TRIPLES_EMPTY[:3]):
        key = f"empty_{DX}_{Ds}_{DA}"
        if key in out:
            continue
        t1 = time.time()
        d = probe_direct(Pr, DX, Ds, DA)
        out[key] = {"triple": [DX, Ds, DA], "frequency_box_empty": DA - DX <= 0, "direct_zero": d.is_zero(),
                    "seconds": round(time.time() - t1, 1)}
    out["seconds"] = round(time.time() - t0, 1)
    return out


def part_step3(full: bool = True, out: dict | None = None) -> dict:
    """Step 3: the biquadratic theta over F_13[T]; does any component family give
    multiplicative squarefree coefficients?"""
    out = {} if out is None else out
    t0 = time.time()
    S = Setup(13, 4)
    q, n = 13, 4
    one = S.P([1])
    cache: dict = {}

    def rho(r, j, i):
        key = (S.key(r), j, i % n)
        if key not in cache:
            cache[key] = rho0(S, r, j, i % n)[0]
        return cache[key]

    j = 1
    L = lambda a: lin_poly(S, a)
    # (a) Patterson's statements for n = 4 (2007, section 4), and the relations
    if not ("base_values" in out and "relations" in out):
        out["base_values"] = {
            "rho0_1_0_is_1": rho(one, j, 0) == 1,
            "rho0_1_1_is_q_tau": rho(one, j, 1) == S.tau(j) * q,
            "rho0_1_2_is_0": rho(one, j, 2).is_zero(),
            "rho0_1_3_is_0": rho(one, j, 3).is_zero(),
            "deg1_rho0_0_is_1": all(rho(L(a), j, 0) == 1 for a in (1, 5)),
            "deg1_rho0_2_is_tau2_q2": all(rho(L(a), j, 2) == S.tau(2 * j) * q * q for a in (1, 5)),
            "deg1_rho0_1_3_zero": all(rho(L(a), j, i).is_zero() for a in (1, 5) for i in (1, 3)),
        }
        hc = [0, 0]
        rl = [one, L(1), L(1) * L(2), S.P([2, 0, 1]), L(1) * L(2) * L(3)]
        for r in rl:
            rr = {i: rho(r, j, i) for i in range(n)}
            res = hecke_infinity_corrected(S, r, j, rr)
            hc[0] += sum(1 for x in res if x[2])
            hc[1] += len(res)
        fh = [0, 0]
        for ro, P in [(one, L(1)), (L(2), L(1)), (one, S.P([2, 0, 1]))]:
            for jj in range(0, n - 1):
                for i in range(n):
                    fh[1] += 1
                    fh[0] += int(rho(ro * P ** jj, j, i) == finite_hecke_rhs(S, ro, P, jj, j, i,
                                                                             lambda a, b: rho(a, j, b)))
        out["relations"] = {"hecke_infinity_corrected": {"hold": hc[0], "checked": hc[1]},
                            "finite_hecke": {"hold": fh[0], "checked": fh[1]},
                            "periodicity_r_b4": all(rho(L(2) * L(1) ** 4, j, i) == rho(L(2), j, i) for i in range(n))}
    # (a1) the Hecke relation at infinity in both additive characters (see hecke_infinity_both)
    if not ("hecke_infinity_both" in out):
        tot = {"2007_character": [0, 0], "2014_character": [0, 0]}
        for r in [one, L(1), L(1) * L(2), S.P([2, 0, 1]), L(1) * L(2) * L(3)]:
            rr = {i: rho(r, j, i) for i in range(n)}
            rm = {i: rho(-r, j, i) for i in range(n)}
            res = hecke_infinity_both(S, r, j, rr, rm)
            for k in tot:
                tot[k][0] += res[k][0]
                tot[k][1] += res[k][1]
        out["hecke_infinity_both"] = {k: {"hold": v[0], "checked": v[1]} for k, v in tot.items()}
    # (a2) Patterson 2007, section 4: the four relations stated for n = 4
    if not ("patterson_n4_relations" in out):
        # Patterson 2007, section 4, the four relations stated for n = 4, tested with the
        # 2014 additive character (C below) and with the 2007 one (C at -r)
        sgn = S.zeta_n(S.eps_chi_minus1())
        rel = {}
        for conv, Cf in (("e_o(a_-1)", lambda r, i: C_fast(S, r, j, i)),
                         ("e_o(-a_-1)", lambda r, i: C_fast(S, -r, j, i))):
            rr = {"deg2_C2_eq_tau_q_C1_epschi(-1)": [], "deg2_C3_eq_tau3_q3": [],
                  "deg3_C3_eq_tau2_q2_C1": [], "deg4_C3_eq_tau_q2_C2": []}
            for r in (L(1) * L(2), S.P([2, 0, 1]), L(3) * L(7)):
                rr["deg2_C2_eq_tau_q_C1_epschi(-1)"].append(Cf(r, 2) == S.tau(j) * q * Cf(r, 1) * sgn)
                rr["deg2_C3_eq_tau3_q3"].append(Cf(r, 3) == S.tau(3 * j) * q ** 3)
            for r in (L(1) * L(2) * L(3), L(1) * S.P([2, 0, 1])):
                rr["deg3_C3_eq_tau2_q2_C1"].append(Cf(r, 3) == S.tau(2 * j) * q ** 2 * Cf(r, 1))
            for r in (L(1) * L(2) * L(3) * L(4),):
                rr["deg4_C3_eq_tau_q2_C2"].append(Cf(r, 3) == S.tau(j) * q ** 2 * Cf(r, 2))
            rel[conv] = rr
        out["patterson_n4_relations"] = rel
    # (b) the component table on squarefree indices: which (deg r, i) vanish, and why
    if not ("component_table" in out and "families" in out):
        samples = {0: [one], 1: [L(1), L(5)], 2: [L(1) * L(2), L(3) * L(7), S.P([2, 0, 1])],
                   3: [L(1) * L(2) * L(3), L(1) * L(2) * L(5), L(1) * S.P([2, 0, 1])]}
        if full:
            samples[4] = [L(1) * L(2) * L(3) * L(4), S.P([2, 0, 1]) * L(3) * L(5)]
        table = {}
        for d, rs in samples.items():
            for i in range(n):
                vals = [rho(r, j, i) for r in rs]
                table[f"{d},{i}"] = {"all_zero": all(v.is_zero() for v in vals),
                                     "forced": zero_reason(S, d, i),
                                     "abs": [round(abs(v.to_complex()), 6) for v in vals]}
        out["component_table"] = table
        # families i(r) = (b - deg r) mod n: forced-zero degree classes (derived) and observed
        fam = {}
        for b in range(n):
            forced = [d for d in range(0, 2 * n) if zero_reason(S, d, (b - d) % n) == "i=i'"]
            fam[f"b{b}"] = {"forced_zero_degrees_below_8": forced}
        out["families"] = fam
    # (c) the three-body defect at r = (x-1)(x-2)(x-lam) for every admissible component choice
    if not ("three_body" in out and "hypergeometric" in out and "moduli_by_lambda" in out):
        lams = [l for l in range(3, q)]
        defects = {}
        for (i0, i1, i2, i3) in itertools.product((0, 1), (0, 2), (0, 1, 2, 3), (1, 3)):
            vals = []
            for lam in lams:
                P1, P2, P3 = L(1), L(2), L(lam)
                f = {S.key(one): rho(one, j, i0)}
                for P in (P1, P2, P3):
                    f[S.key(P)] = rho(P, j, i1)
                for (A_, B_) in ((P1, P2), (P1, P3), (P2, P3)):
                    f[S.key(A_ * B_)] = rho(A_ * B_, j, i2)
                f[S.key(P1 * P2 * P3)] = rho(P1 * P2 * P3, j, i3)
                if any(v.is_zero() for v in f.values()):
                    vals.append(None)
                    continue
                vals.append(three_body_defect(S, f, P1, P2, P3))
            good = [v for v in vals if v is not None]
            distinct = {str(v.p) for v in good}
            defects[f"{i0}{i1}{i2}{i3}"] = {
                "components_deg0_1_2_3": [i0, i1, i2, i3],
                "lambdas": lams,
                "defect": [None if v is None else round(v.to_complex().real, 9) for v in vals],
                "distinct_exact_values": len(distinct),
                "all_equal_one": all(v == 1 for v in good) if good else None,
            }
        out["three_body"] = defects
        # the moduli behind the defect: singles and pairs do not depend on lambda, triples do
        mod = {"single": {}, "pair": {}, "triple": {}}
        for i in range(n):
            mod["single"][str(i)] = sorted({str((rho(L(a), j, i) * rho(L(a), j, i).conj()).p)
                                            for a in [1, 2] + lams})
            mod["pair"][str(i)] = sorted({str((rho(A_ * B_, j, i) * rho(A_ * B_, j, i).conj()).p)
                                          for lam in lams for (A_, B_) in ((L(1), L(lam)), (L(2), L(lam)))}
                                         | {str((rho(L(1) * L(2), j, i) * rho(L(1) * L(2), j, i).conj()).p)})
            mod["triple"][str(i)] = {str(lam): str((rho(L(1) * L(2) * L(lam), j, i)
                                                     * rho(L(1) * L(2) * L(lam), j, i).conj()).p)
                                     for lam in lams}
        out["moduli_by_lambda"] = mod
        # the hypergeometric sum behind the degree-3 coefficient
        hyp = []
        for lam in lams:
            r = L(1) * L(2) * L(lam)
            H = hypergeometric_sum(S, r, j)
            C1 = C_fast(S, r, j, 1)
            hyp.append({"lambda": lam, "abs2": round((H * H.conj()).to_complex().real, 9),
                        "abs2_exact": str((H * H.conj()).p),
                        "C1_equals_tau_times_H": C1 == S.tau(j) * H,
                        "rho0_i1_equals_C1": rho(r, j, 1) == C1})
        out["hypergeometric"] = hyp
    # (d) every squarefree monic r of degree 3: the degree-3 coefficient at component 1 is
    #     C(r, eps, 1) = tau(eps chi) H(r) (R = 0), so its modulus is read off H(r)
    if not ("degree3_census" in out):
        census: dict = {}
        tot = 0
        for r in S.monic(3):
            if mobius(S, r) == 0:
                continue
            tot += 1
            H = hypergeometric_sum(S, r, j)
            ftype = "+".join(str(d) for d in sorted(P.degree() for P, _ in S.factor(r)))
            key = f"{ftype}: {(H * H.conj()).p}"
            census[key] = census.get(key, 0) + 1
        out["degree3_census"] = {"squarefree_monic_degree_3": tot,
                                 "abs2_H_counts_by_factorization_type": census}
    out["seconds"] = round(time.time() - t0, 1)
    return out


def cyc_to_acb(c: "Cyc") -> flint.acb:
    """A ball enclosure of a cyclotomic number at the current working precision."""
    N = c.K.N
    co = c.p.coeffs() if not c.p.is_zero() else []
    acc = flint.acb(0)
    for k, a in enumerate(co):
        if a != 0:
            acc += flint.acb(flint.fmpq(int(a.p), int(a.q))) * flint.acb(flint.fmpq(2 * k, N)).exp_pi_i()
    return acc


def _roots_quadratic_arb(coeffs: list, prec: int = 200):
    """Ball enclosures of the roots of c0 + c1 u + c2 u^2 (python-flint acb_poly)."""
    old = flint.ctx.prec
    flint.ctx.prec = prec
    try:
        cs = [cyc_to_acb(c) for c in coeffs]
        return flint.acb_poly(cs).roots()
    finally:
        flint.ctx.prec = old


def part_rival(full: bool = True) -> dict:
    """Step 5: L(u, chi) + eps L(u, conj chi) over F_7[T], chi primitive odd modulo T^3."""
    out: dict = {}
    t0 = time.time()
    S = Setup(7, 6)
    q = 7
    scan = []
    for e in range(1, 6):
        for alpha in range(0, 7):
            for beta in range(1, 7):
                chi = CharModT3(S, e, alpha, beta)
                R = Rival(S, chi)
                c = R.L
                fe = (c[1] == R.eps * c[1].conj()) and (R.eps * R.eps.conj() == 1)
                d = R.poly()
                rec = {"e": e, "alpha": alpha, "beta": beta, "functional_equation": fe,
                       "d2_equals_q_d0": d[2] == d[0] * q}
                if d[0].is_zero():
                    rec["degenerate"] = True
                    scan.append(rec)
                    continue
                bet = d[1] / d[0]
                rec["beta_real"] = bet == bet.conj()
                disc = bet * bet - 4 * q
                rec["disc"] = round(disc.to_complex().real, 9)
                roots = _roots_quadratic_arb(d)
                mods = []
                for rt in roots:
                    a = abs(rt)
                    mods.append(a)
                rec["root_abs_times_sqrtq"] = [float((m * flint.arb(q).sqrt()).mid()) for m in mods]
                # off the circle |u| = q^(-1/2) exactly when the enclosure of |u| sqrt(q) excludes 1
                rec["off_circle_by_enclosure"] = [bool((m * flint.arb(q).sqrt() - 1) > 0 or (m * flint.arb(q).sqrt() - 1) < 0)
                                                  for m in mods]
                rec["sigma"] = [float((-(m.log()) / flint.arb(q).log()).mid()) for m in mods]
                scan.append(rec)
    out["scan"] = scan
    good = [r for r in scan if not r.get("degenerate")]
    off = [r for r in good if any(r["off_circle_by_enclosure"])]
    out["counts"] = {"characters": len(scan), "degenerate": len(scan) - len(good),
                     "functional_equation_holds": sum(r["functional_equation"] for r in scan),
                     "with_zeros_off_circle": len(off),
                     "off_iff_disc_positive": all((r["disc"] > 0) == any(r["off_circle_by_enclosure"]) for r in good)}
    # the named example: the off-circle rival whose largest zero abscissa lies closest above 7/8
    above = [r for r in off if max(r["sigma"]) > 0.875]
    best = min(above, key=lambda r: max(r["sigma"]))
    out["example"] = best
    out["sigma_max_over_scan"] = max(max(r["sigma"]) for r in off)
    below1 = [max(r["sigma"]) for r in off if max(r["sigma"]) <= 1.0]
    out["largest_sigma_not_above_1"] = max(below1) if below1 else None
    chi = CharModT3(S, best["e"], best["alpha"], best["beta"])
    R = Rival(S, chi)
    out["example_poly"] = [cyc_record(x) for x in R.poly()]
    out["example_L"] = [cyc_record(x) for x in R.L[:3]]
    out["example_eps"] = cyc_record(R.eps)
    # the local identity: definition of the principal row against the Lemma 7.1 product
    B = Bound(3, 1, 0) if full else Bound(2, 0, 0)
    res = {}
    for name, fun in (("rival", R), ("chi", chi)):
        Pr = Probe(S, eta_fun=fun)
        lhs = high_series_def(Pr, S.P([1]), B)
        rhs = euler_product(Pr, S.P([1]), B, closed=True)
        diff = lhs.diff_keys(rhs)
        res[name] = {"bound": list(B.maxes), "mismatched_monomials": [list(k) for k in diff],
                     "first_mismatch": list(diff[0]) if diff else None,
                     "lhs_at_first": cyc_record(lhs.coeff(diff[0])) if diff else None,
                     "rhs_at_first": cyc_record(rhs.coeff(diff[0])) if diff else None}
    out["local_identity"] = res
    # the term: d(P1 P2) - d(P1) d(P2) at two linear primes
    P1, P2 = lin_poly(S, 1), lin_poly(S, 2)
    out["non_multiplicative_at"] = {"P1": str(P1), "P2": str(P2),
                                    "d_P1P2": cyc_record(R(P1 * P2)),
                                    "d_P1_d_P2": cyc_record(R(P1) * R(P2))}
    out["seconds"] = round(time.time() - t0, 1)
    return out


def prime_classes(S: "Setup", Pr: "Probe", dmax: int) -> dict:
    """Counts of primes p != T by (deg p, exponent of eta(p)) for deg p <= dmax."""
    out: dict = {}
    for key in primes_upto(S.q, S.n, dmax):
        Pp = S.P(list(key))
        e = Pr.eta(Pp)
        k = next(kk for kk in range(S.N) if S.K.zeta(kk) == e) if not e.is_zero() else None
        out[(Pp.degree(), k)] = out.get((Pp.degree(), k), 0) + 1
    return out


def H_principal_numeric(Pr: "Probe", X: complex, classes: dict) -> complex:
    """H_eta(x) = H_{eta,1}(x, 1, 1/6) from the closed-form local factors (float grade)."""
    import cmath
    S = Pr.S
    q = S.q
    lam = Pr.lam_alpha.to_complex()
    logH = 0j
    for (dP, k), cnt in classes.items():
        Q = q ** dP
        eta_p = cmath.exp(2j * cmath.pi * k / S.N)
        al = lam ** dP
        x = X ** dP
        V = 1.0 / Q
        W = 1.0 / Q
        D = eta_p * x
        a_p = (al.conjugate() ** 3) * eta_p ** 3
        R = a_p ** 2 * Q ** 4 * x ** 6 * V
        # j = 0, rho = 1 for u = 1
        J = -eta_p * x + W * R
        Pstar = ((R * (1 - 1.0 / Q) - eta_p * (Q - 1) * x * W * V) / (1 - V) + J) / (1 - R)
        P = 1 / (1 - V) + W / (1 - W) + Pstar
        H = P * (1 - V) * (1 - W) / (1 - D)
        logH += cnt * cmath.log(H)
    return cmath.exp(logH)


def template_walls(k: int) -> dict:
    """Hunt 136's order-k template walls (PROBE.md section 3), as exact fractions."""
    return {"balanced": Fraction(1) - Fraction(1, 2 * k), "corner": Fraction(1) - Fraction(3, 4 * k),
            "floor": Fraction(1) - Fraction(4, 5 * k)}


def part_ledger(full: bool = True) -> dict:
    """Step 4: what the template charges against the exact function-field sizes."""
    import cmath
    out: dict = {}
    t0 = time.time()
    S = Setup(7, 6)
    Pr = Probe(S)
    q = 7
    T = Pr.T
    # (1) |F(s, A, H)| against the elementary bound q_s q_{b* A} (paper line 3840)
    worst = 0.0
    best_case = None
    n_nonzero = 0
    for ds in range(0, 3):
        for dA in range(0, 3):
            for s in monic_coprime_T(S, ds):
                for A in monic_coprime_T(S, dA):
                    for H in S.residues(2):
                        if H.is_zero():
                            continue
                        f = Pr.F_def(s, A, H)
                        if f.is_zero():
                            continue
                        n_nonzero += 1
                        ratio = abs(f.to_complex()) / (q ** ds * q ** (1 + dA))
                        if ratio > worst:
                            worst, best_case = ratio, (ds, dA, str(s), str(A), str(H))
    out["F_vs_elementary_bound"] = {"max_ratio": worst, "at": best_case, "nonzero_cases": n_nonzero,
                                    "range": "deg s, deg A <= 2, deg H <= 1"}
    # (2) |F|^2 exactly for squarefree coprime s, A and H coprime to s A: q * q_A (derived)
    exact_ok = exact_tot = 0
    for s in monic_coprime_T(S, 1):
        for A in monic_coprime_T(S, 2):
            if mobius(S, A) == 0 or A.gcd(s).degree() > 0:
                continue
            for H in [S.P([1]), S.P([2, 1]), S.P([3, 0, 1])]:
                if H.gcd(s * A).degree() > 0 or (H % T).is_zero():
                    continue
                f = Pr.F_def(s, A, H)
                exact_tot += 1
                exact_ok += int(f * f.conj() == q * q ** A.degree())
    out["F_abs2_generic"] = {"checked": exact_tot, "equal_q_times_qA": exact_ok}
    # (3) the target: L(u, eta) = 1 + c_1 u with |c_1|^2 = q exactly
    L = []
    for d in range(0, 4):
        acc = S.K.zero
        for a in S.monic(d):
            acc = acc + Pr.eta(a)
        L.append(acc)
    out["target_L"] = {"coefficients": [cyc_record(c) for c in L],
                       "degree_one": all(c.is_zero() for c in L[2:]),
                       "abs2_c1_equals_q": L[1] * L[1].conj() == q}
    # (4) the principal correction H_eta(x) = H_{eta,1}(x, 1, 1/6) on Re x = 7/8 and nearby circles
    dmax = 6 if full else 4
    classes = prime_classes(S, Pr, dmax)
    circ = {}
    for sigma in (Fraction(7, 8), Fraction(5, 6), Fraction(3, 4), Fraction(17, 24)):
        r = q ** (-float(sigma))
        vals = [H_principal_numeric(Pr, r * cmath.exp(2j * math.pi * t / 360), classes) for t in range(360)]
        circ[str(sigma)] = {"max_abs_H_minus_1": max(abs(v - 1) for v in vals),
                            "min_abs_H": min(abs(v) for v in vals)}
    out["principal_correction"] = {"prime_degree_cutoff": dmax, "circles": circ,
                                   "absolute_convergence_abscissa": "2/3"}
    # (5) the balanced probe X = Y = Z^(1/2) at the only balanced degrees within reach:
    #     the unit sum needs D_s = D_A + xi_j (mod 6), so D_s = D_A/2 forces D_A = -2 xi_j (mod 12)
    bal = []
    for (xj, D) in ((5, 1), (4, 2)):
        Pb = Probe(S, xi_j=xj)
        DA = 2 * D
        d = probe_direct(Pb, D, D, DA)
        e = probe_euler(Pb, D, D, DA)
        # the paper's normalization (1/Y)(q_b* q_s X)^(-1/2) q_s^(-1/2) at these degrees
        norm = q ** (-2 * D - (1 + D) / 2)
        bal.append({"xi_j": xj, "D_X": D, "D_s": D, "D_A": DA, "direct_eq_euler": d == e,
                    "abs_I_paper_normalization": abs(d.to_complex()) * norm,
                    "Z_quarter": q ** (DA / 4)})
    out["balanced_probe"] = bal
    # (6) the template's walls for k = 6 (cubic theta, sextic twist) and k = 4 (quartic)
    out["template_walls"] = {str(k): {kk: str(v) for kk, v in template_walls(k).items()} for k in (4, 6)}
    out["truth_in_Fq[T]"] = "1/2"
    out["seconds"] = round(time.time() - t0, 1)
    return out


PARTS = {"sources": part_sources, "step1": part_step1, "step2": part_step2, "step2b": part_step2b,
         "step3": part_step3, "ledger": part_ledger, "rival": part_rival}


def _jsonable(o):
    if isinstance(o, dict):
        return {str(k): _jsonable(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [_jsonable(v) for v in o]
    if isinstance(o, (bool, int, float, str)) or o is None:
        return o
    if isinstance(o, Fraction):
        return str(o)
    if isinstance(o, np.integer):
        return int(o)
    if isinstance(o, np.bool_):
        return bool(o)
    return str(o)


class CheckpointDict(dict):
    """A results dict that rewrites its partial file whenever a top-level unit is stored."""

    def __init__(self, path: Path, initial: dict | None = None):
        super().__init__(initial or {})
        self.path = path

    def __setitem__(self, key, value):
        super().__setitem__(key, _jsonable(value))
        self.path.write_text(json.dumps(dict(self), indent=1, sort_keys=True) + "\n")
        print(f"  checkpoint: {key} -> {self.path.name}", flush=True)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--part", choices=sorted(PARTS), action="append")
    ap.add_argument("--quick", action="store_true", help="smaller ranges (for a smoke run)")
    args = ap.parse_args(argv)
    parts = args.part or sorted(PARTS)
    for name in parts:
        t0 = time.time()
        suffix = "_quick" if args.quick else ""
        path = HERE / f"results_{name}{suffix}.json"
        partial = HERE / f"results_{name}{suffix}.partial.json"
        if name == "sources":
            res = PARTS[name]()
        elif name in ("step2", "step2b", "step3"):
            start = json.loads(partial.read_text()) if partial.is_file() else {}
            start.pop("seconds", None)
            res = PARTS[name](full=not args.quick, out=CheckpointDict(partial, start))
        else:
            res = PARTS[name](full=not args.quick)
        res = _jsonable(dict(res))
        path.write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
        if partial.is_file():
            partial.unlink()
        print(f"{name}: wrote {path.name} in {time.time() - t0:.1f} s", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
