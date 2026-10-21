"""Zero strips for F_k: the Euler-phase abscissa of hunts/lambda_dh_bounds.

``hunts/lambda_dh_bounds/strip2.py`` (``STRIP2.md``) decides, for the
Davenport-Heilbronn function, the abscissa beyond which a zero is impossible
because the two Euler products cannot supply the phase a zero needs.
``strip.py`` decides the weaker coefficient-domination abscissa.  Both are
written for q = 5; this module ports the flint legs to any prime q = 1 mod 4
with the order-4 character, and q = 5 is the calibration: it must return
strip2's enclosure.

The argument (STRIP2.md section 3, with 5 replaced by q).  F_k = A L(s, chi) +
conj(A) L(s, chi-bar), A = (1 - i k)/2.  For Re s > 1 neither L vanishes, so
F_k(s) = 0 iff R(s) = L(s, chi)/L(s, chi-bar) = -conj(A)/A = e^{i(pi + theta)},
since 2 arctan k = theta.  The smallest representative of pi + theta mod 2 pi
has absolute value tau = pi - |theta|.  R is an absolutely convergent Euler
product whose factor is 1 where chi(p) is real (the quadratic residues and q)
and (1 + u)/(1 - u), u = chi(p) p^{-s}, where chi(p) = +-i (the non-residues,
chi-bar(p) = -chi(p)); each such factor has |arg| <= 2 arctan(p^{-sigma})
(STRIP2.md's Moebius lemma).  Hence

    |arg R(s)| <= Theta_q(sigma) = sum_{p non-residue mod q} 2 arctan(p^{-sigma}),

and Theta_q(sigma) < tau forbids a zero on Re s = sigma; Theta_q decreases, so
one decided sigma* closes Re s >= sigma*, and the functional equation closes
Re s <= 1 - sigma*.  The tail over primes is closed by the Euler products of
zeta and of L(s, rho_q), rho_q the Legendre symbol, exactly as in strip2.py:

    T1 - Tchi = log(zeta(s)/L(s, rho_q)) + log(1 - q^{-s})
                + sum_{p <= P, rho_q(p) = -1} [log(1 - p^{-s}) - log(1 + p^{-s})],

equal to 2 sum_{p > P, non-residue} p^{-s} up to eps3 = (2/3) P^{1-3s} /
((3s - 1)(1 - P^{-2s})).  Arb balls carry every step; tau comes from the Gauss
sum of flint's character (``arb_route.ArbRival``).
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from flint import acb, arb, ctx, fmpq  # noqa: E402

import arb_route as B  # noqa: E402


class _prec(B._prec):
    pass


def sieve(n: int) -> list[int]:
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def legendre(a: int, q: int) -> int:
    a %= q
    if a == 0:
        return 0
    return 1 if pow(a, (q - 1) // 2, q) == 1 else -1


def _arbq(x: Fraction) -> arb:
    return arb(fmpq(x.numerator, x.denominator))


def L_rho(sig: arb, q: int) -> arb:
    """L(sigma, rho_q) by the Hurwitz combination, real sigma > 1."""
    s = acb(sig)
    tot = arb(0)
    for a in range(1, q):
        r = legendre(a, q)
        z = s.zeta(acb(fmpq(a, q)))
        if not z.imag.contains(arb(0)):
            raise ArithmeticError("Hurwitz zeta: imaginary ball excludes 0")
        tot += r * z.real
    return tot * arb(q) ** (-sig)


class PhaseStrip:
    """Theta_q bounds and the target tau for one q at sieve limit P."""

    def __init__(self, q: int, P: int = 10 ** 5, prec: int = 192):
        if P < q:
            raise ValueError("the tail identity here assumes P >= q")
        self.q = q
        self.P = P
        self.prec = prec
        self.non = [p for p in sieve(P) if p != q and legendre(p, q) == -1]
        rv = B.ArbRival(q, prec=prec)
        with _prec(prec):
            self.theta = rv.theta_root
            self.tau = arb.pi() - abs(self.theta)
            self.logs = [arb(p).log() for p in self.non]
        self.k = rv.k
        self.rival = rv

    def theta_bounds(self, sig_q: Fraction) -> tuple[arb, arb]:
        with _prec(self.prec):
            sig = _arbq(sig_q)
            head = arb(0)
            diff = arb(0)
            for lp in self.logs:
                x = (-sig * lp).exp()
                head += 2 * x.atan()
                diff += (1 - x).log() - (1 + x).log()
            qs = arb(self.q) ** (-sig)
            t1_minus_tchi = (sig.zeta() / L_rho(sig, self.q)).log() + (1 - qs).log() + diff
            P = arb(self.P)
            w3 = P ** (1 - 3 * sig) / (3 * sig - 1)
            eps3 = (arb(2) / 3) * w3 / (1 - P ** (-2 * sig))
            upper = head + t1_minus_tchi + eps3
            lower = head + t1_minus_tchi - eps3 - (arb(2) / 3) * w3
            return lower, upper

    def excludes(self, sig_q: Fraction) -> bool:
        """Decided Theta_up(sigma) < tau: no zero of F on Re s = sigma (or beyond)."""
        _, up = self.theta_bounds(sig_q)
        with _prec(self.prec):
            return bool(up < self.tau)

    def bisect(self, lo: Fraction, hi: Fraction, width: Fraction, which: str = "upper") -> tuple:
        """Bracket of the root of Theta_which = tau, every sign decided."""

        def sgn(s):
            lo_b, up_b = self.theta_bounds(s)
            v = (up_b if which == "upper" else lo_b) - self.tau
            with _prec(self.prec):
                if v > 0:
                    return 1
                if v < 0:
                    return -1
            raise ArithmeticError(f"sign undecided at {s}")

        if not (sgn(lo) == 1 and sgn(hi) == -1):
            raise ArithmeticError("bracket not decided")
        n = 2
        while hi - lo >= width:
            mid = (lo + hi) / 2
            if sgn(mid) == 1:
                lo = mid
            else:
                hi = mid
            n += 1
        return lo, hi, n


def domination_bracket(q: int, lo: Fraction, hi: Fraction, width: Fraction,
                       prec: int = 128) -> tuple:
    """strip.py's root of sum_{n>=2} |b(n)| n^{-sigma} = 1, decided by bisection."""
    rv = B.ArbRival(q, prec=prec)

    def g(s: Fraction) -> int:
        with _prec(prec):
            sa = acb(_arbq(s))
            tot = arb(0)
            for a, w in rv.dom_weights:
                if w == 0:
                    continue
                tot += w * sa.zeta(acb(fmpq(a, q))).real
            v = tot * arb(q) ** (-_arbq(s)) - 2
            if v > 0:
                return 1
            if v < 0:
                return -1
        raise ArithmeticError("undecided")

    if not (g(lo) == 1 and g(hi) == -1):
        raise ArithmeticError("domination bracket not decided")
    while hi - lo >= width:
        mid = (lo + hi) / 2
        if g(mid) == 1:
            lo = mid
        else:
            hi = mid
    return lo, hi
