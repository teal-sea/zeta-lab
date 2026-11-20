"""The zero side of the explicit formulas for G and Gchi.

Derivation (ordinary contour shift, stated with its assumptions in RESULTS.md):

    G(y) = sum_rho y^rho / (rho (1 - rho)) + log(2 pi) + T(y),              y >= 1,

and for a primitive chi mod q > 1, with the sum over the nontrivial zeros of
L(s, chi),

    odd:   Gchi(y) = sum_rho y^rho/(rho(1-rho)) + L'/L(0, chi) + T_odd(y)
    even:  Gchi(y) = sum_rho y^rho/(rho(1-rho)) + log y + 1 + b(chi) + T(y)

with b(chi) = lim_{s->0} (L'/L(s, chi) - 1/s).

Every zero used here lies on the critical line: for zeta the ordinates come
from Arb's isolation of the zeros by index (`acb.zeta_zeros`), for L(s, chi)
from sign changes of the Hardy Z function (a lower bound on the count, checked
against the exact value of sum 1/(rho(1-rho))).  The truncated sums are
therefore sums of sqrt(y) cos(gamma log y)/(1/4 + gamma^2) terms.

The tail budget is exact, not estimated: since sum_rho 1/(rho(1-rho)) is known
in closed form, the omitted zeros contribute at most
(closed form - partial sum) * sqrt(y) if they are on the line.
"""

from __future__ import annotations

import math
from pathlib import Path

import numpy as np

from . import instrument as I


def zeta_zero_ordinates(n: int, prec: int = 64, cache_dir: str | None = None, chunk: int = 2000):
    """First n ordinates gamma_1 < ... < gamma_n, with the largest ball radius.

    Returns (float64 array of midpoints, max radius).  Arb isolates the k-th
    zero by index, so the list is complete by construction of that routine.
    Checkpointed per chunk when `cache_dir` is given.
    """
    from flint import acb, ctx

    n = int(n)
    path = None
    if cache_dir is not None:
        path = Path(cache_dir) / f"zeta_zeros_{n}_prec{prec}.npz"
        if path.exists():
            d = np.load(path)
            return d["gammas"], float(d["max_rad"])
    old = ctx.prec
    ctx.prec = prec
    out = np.empty(n, dtype=np.float64)
    max_rad = 0.0
    try:
        done = 0
        while done < n:
            m = min(chunk, n - done)
            part = None
            if cache_dir is not None:
                part = Path(cache_dir) / f"zeta_zeros_part_{done + 1}_{m}_prec{prec}.npz"
            if part is not None and part.exists():
                d = np.load(part)
                out[done : done + m] = d["gammas"]
                max_rad = max(max_rad, float(d["max_rad"]))
            else:
                zs = acb.zeta_zeros(done + 1, m)
                g = np.array([float(z.imag.mid()) for z in zs])
                r = max(float(z.imag.rad()) for z in zs)
                out[done : done + m] = g
                max_rad = max(max_rad, r)
                if part is not None:
                    np.savez(part, gammas=g, max_rad=r)
            done += m
    finally:
        ctx.prec = old
    if path is not None:
        np.savez(path, gammas=out, max_rad=max_rad)
    return out, max_rad


def zeta_weights(gammas: np.ndarray) -> np.ndarray:
    """2 / (1/4 + gamma^2): the weight of the pair rho, conj(rho) at y = 1."""
    return 2.0 / (0.25 + gammas * gammas)


def zeta_partial(gammas: np.ndarray) -> float:
    """sum over the listed pairs of 1/(rho(1-rho)), exactly rounded."""
    return math.fsum(zeta_weights(gammas).tolist())


def zeta_tail_budget(gammas: np.ndarray) -> float:
    """c0 minus the partial sum: the total weight of the zeros not listed."""
    return I.C0 - zeta_partial(gammas)


def zeta_zero_sum(y, gammas: np.ndarray, chunk: int = 4096) -> np.ndarray:
    """sum over listed zeros of y^rho/(rho(1-rho)), for an array of y >= 1."""
    y = np.atleast_1d(np.asarray(y, dtype=np.float64))
    u = np.log(y)
    w = zeta_weights(gammas)
    acc = np.zeros_like(u)
    for i in range(0, len(u), chunk):
        uu = u[i : i + chunk]
        acc[i : i + chunk] = np.cos(np.outer(uu, gammas)) @ w
    return np.sqrt(y) * acc


def zeta_zero_side(y, gammas: np.ndarray) -> np.ndarray:
    """Truncated right-hand side of the explicit formula for G."""
    y = np.atleast_1d(np.asarray(y, dtype=np.float64))
    return zeta_zero_sum(y, gammas) + I.LOG_2PI + I.T_float(y)


def zeta_zero_side_arb(y, n_zeros: int, prec: int = 128):
    """Arb enclosure of the truncated zero side at an exact y, plus the tail budget.

    Returns (truncated value, tail budget), both arb.  The true zero side lies
    within tail*sqrt(y) of the truncated value if the unlisted zeros are on
    the line.
    """
    from flint import acb, arb, ctx

    old = ctx.prec
    ctx.prec = prec
    try:
        ya = I._as_arb(y)
        u = ya.log()
        acc = arb(0)
        part = arb(0)
        done = 0
        while done < n_zeros:
            m = min(1000, n_zeros - done)
            for z in acb.zeta_zeros(done + 1, m):
                g = z.imag
                w = 2 / (arb(1) / 4 + g * g)
                acc += w * (g * u).cos()
                part += w
            done += m
        c0 = 2 + arb.const_euler() - (4 * arb.pi()).log()
        val = ya.sqrt() * acc + (2 * arb.pi()).log() + I.T_arb(ya)
        return val, c0 - part
    finally:
        ctx.prec = old


# ---------------------------------------------------------------------------
# Dirichlet L-functions
# ---------------------------------------------------------------------------


def l_zero_ordinates(chi: I.Char, t_max: float, step: float = 0.02, prec: int = 64) -> np.ndarray:
    """Ordinates gamma in [-t_max, t_max] of zeros 1/2 + i gamma of L(s, chi).

    Sign changes of the Hardy Z function on a grid, refined by bisection.  A
    sign-change count is a lower bound: two zeros inside one grid cell are
    missed.  The caller checks the result against the closed form of
    sum 1/(rho(1-rho)).
    """
    from flint import arb, ctx

    fc = chi.flint()
    old = ctx.prec
    ctx.prec = prec
    try:
        def z(t: float) -> float:
            return float(fc.hardy_z(arb(t)).real.mid())

        n = int(math.ceil(2 * t_max / step))
        ts = [-t_max + 2 * t_max * i / n for i in range(n + 1)]
        vals = [z(t) for t in ts]
        zeros = []
        for i in range(n):
            a, b = ts[i], ts[i + 1]
            fa, fb = vals[i], vals[i + 1]
            if fa == 0.0:
                zeros.append(a)
                continue
            if fa * fb < 0:
                for _ in range(60):
                    mid = 0.5 * (a + b)
                    fm = z(mid)
                    if fa * fm <= 0:
                        b, fb = mid, fm
                    else:
                        a, fa = mid, fm
                zeros.append(0.5 * (a + b))
        return np.array(zeros, dtype=np.float64)
    finally:
        ctx.prec = old


def l_partial(gammas: np.ndarray) -> float:
    """sum over listed zeros of 1/(rho(1-rho)) = 1/(1/4 + gamma^2)."""
    return math.fsum((1.0 / (0.25 + gammas * gammas)).tolist())


def l_zero_sum(y, gammas: np.ndarray) -> np.ndarray:
    """sum over listed zeros of y^rho/(rho(1-rho)) for L(s, chi): complex, array in y."""
    y = np.atleast_1d(np.asarray(y, dtype=np.float64))
    u = np.log(y)
    w = 1.0 / (0.25 + gammas * gammas)
    ph = np.exp(1j * np.outer(u, gammas))
    return np.sqrt(y) * (ph @ w)


def l_zero_side(chi: I.Char, y, gammas: np.ndarray, const0: complex) -> np.ndarray:
    """Truncated right-hand side of the explicit formula for Gchi (complex)."""
    y = np.atleast_1d(np.asarray(y, dtype=np.float64))
    s = l_zero_sum(y, gammas)
    if chi.parity() == 1:
        return s + const0 + I.T_odd_float(y)
    return s + np.log(y) + 1.0 + const0 + I.T_float(y)


def riemann_von_mangoldt_main(q: int, t: float) -> float:
    """Main term of the count of zeros of L(s, chi) with |gamma| <= t."""
    return (t / math.pi) * math.log(q * t / (2 * math.pi * math.e))
