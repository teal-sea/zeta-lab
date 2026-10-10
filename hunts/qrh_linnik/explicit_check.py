"""Measured calibration of Lemma 2's sign and normalisation, for zeta.

Lemma 2 (RESULTS.md section 3) for the trivial character reads, after moving
the contour all the way left (zeta'/zeta is regular at 0 and the trivial zeros
are -2, -4, ...):

    psi_w(x) = W(1) x - sum_rho W(rho) x^rho - sum_{k >= 1} W(-2k) x^(-2k),

with psi_w(x) = sum_n Lambda(n) w(n/x) and W the Mellin transform of w.  This
module evaluates both sides for one smooth bump w on [1/2, 1] and the first
`n_zeros` zeta zeros from mpmath, at `mp.workdps(30)`.  The residual is a
measured number (one route, truncated zero sum), not a proof of anything; its
job is to catch a sign or normalisation slip in the formula the proof uses.
"""

from __future__ import annotations

import mpmath as mp

LO, HI = mp.mpf(1) / 2, mp.mpf(1)


def bump(u):
    """exp(1 - 1/(1 - v^2)), v = (u - 3/4)/(1/4); smooth, support [1/2, 1], max 1."""
    v = (u - mp.mpf(3) / 4) * 4
    if abs(v) >= 1:
        return mp.mpf(0)
    return mp.exp(1 - 1 / (1 - v * v))


def mellin(s):
    """W(s) = int_{1/2}^{1} w(u) u^(s-1) du, split for oscillation."""
    nodes = mp.linspace(LO, HI, 2 + int(abs(mp.im(mp.mpmathify(s)))) // 4)
    return mp.quad(lambda u: bump(u) * u ** (s - 1), nodes)


def von_mangoldt(n: int):
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            return mp.log(p) if m == 1 else mp.mpf(0)
        p += 1
    return mp.log(m) if m > 1 else mp.mpf(0)


def psi_w(x: int):
    lo = x // 2
    return mp.fsum(von_mangoldt(n) * bump(mp.mpf(n) / x) for n in range(max(lo, 2), x + 1))


def explicit_side(x, n_zeros: int, sign: int = 1):
    """W(1) x - sign * 2 Re sum_{gamma > 0} W(rho) x^rho - trivial-zero terms."""
    x = mp.mpf(x)
    rhos = [mp.zetazero(k) for k in range(1, n_zeros + 1)]
    zeros = mp.fsum(2 * mp.re(mellin(r) * x ** r) for r in rhos)
    trivial = mp.fsum(mellin(-2 * k) * x ** (-2 * k) for k in range(1, 6))
    return mellin(1) * x - sign * zeros - trivial


def residual(x: int = 2000, n_zeros: int = 60, sign: int = 1):
    with mp.workdps(30):
        return float(abs(psi_w(x) - explicit_side(x, n_zeros, sign)))


def tail_size(n_zeros: int = 60):
    """|W(rho_n)| at the last zero used: the size of the neglected terms."""
    with mp.workdps(30):
        return float(abs(mellin(mp.zetazero(n_zeros))))


if __name__ == "__main__":  # pragma: no cover
    print({"residual": residual(), "flipped_sign": residual(sign=-1), "tail": tail_size()})
