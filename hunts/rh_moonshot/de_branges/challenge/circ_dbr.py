"""Circularity challenger's recomputation for de_branges (hunt #150).

Written by the circularity challenger; shares no code with ``dbr_common.py``.

1. Epstein zeta of Q = x^2 + xy + 6y^2 by this module's own Chowla-Selberg
   series (Poisson summation in m, re-derived here: the Bessel-sum prefactor is
   2^(s + 5/2) pi^s / (sqrt(a) Gamma(s)) Delta^((1/2 - s)/2)), calibrated against a
   direct lattice sum and against ``zeta.epstein``. The builder's two routes are
   ``zeta.epstein``'s Mellin/lattice route and hunt #120's Bessel route on Arb.
2. The "second off-line zero" 0.7979971571787 + 29.5517610986291 i: Newton on
   this route, and argument-principle counts (own implementation, every step's
   argument increment checked below pi/4) on small squares around it, around
   the mirror 1 - conj(rho), and on a displaced square.
3. A census of zeros of zeta_Q in 0.55 <= Re s <= 1.6, 0.5 <= Im s <= 60.5, the
   region hunt #120's D = -23 census did not cover below Re s = 0.8751.
4. Conrey and Li's two printed numbers by this module's own xi.
5. A run-time zero trap around the builder's defect evaluation.

Writes nothing into the tree.
"""
from __future__ import annotations

import sys
from contextlib import contextmanager
from pathlib import Path

from mpmath import mp

HERE = Path(__file__).resolve().parent
MECH = HERE.parent
ROOT = HERE.parents[3]
for _p in (str(MECH), str(ROOT)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

FORM = (1, 1, 6)
BUILDER_ROOT = ("0.7979971571787", "29.5517610986291")
#: Off-line zeros of zeta_Q found by this session's census and ``locate`` (2026-10-26),
#: in [0.55, 1.6] x [30.5, 50.5]; none is in the tree's record.
NEW_ZEROS = (
    ("0.66365167885959860983", "33.650100582527335123"),
    ("0.8099915314971334217", "43.858664365004478179"),
    ("0.78237857667772956412", "46.960993669907468078"),
)


def _sigma(n: int, a):
    return mp.fsum(mp.mpf(d) ** a for d in range(1, n + 1) if n % d == 0)


def epstein_cs(s, form=FORM, terms: int = 30, pre_power=None):
    """zeta_Q(s) for Q = a x^2 + b x y + c y^2 by the Chowla-Selberg series.

    ``pre_power`` other than 5/2 is a planted fault (the Bessel-sum prefactor
    2^(s + 3/2) of a common statement of the formula is off by a factor 2)."""
    pre_power = mp.mpf(5) / 2 if pre_power is None else mp.mpf(pre_power)
    a, b, c = form
    s = mp.mpc(s)
    D = mp.mpf(4 * a * c - b * b)
    a_ = mp.mpf(a)
    t1 = 2 * mp.zeta(2 * s) * a_ ** (-s)
    t2 = (mp.mpf(2) ** (2 * s) * mp.sqrt(mp.pi) * a_ ** (s - 1) * mp.gamma(s - mp.mpf(1) / 2)
          / mp.gamma(s) * mp.zeta(2 * s - 1) * D ** (mp.mpf(1) / 2 - s))
    pre = mp.mpf(2) ** (s + pre_power) * mp.pi ** s / (mp.sqrt(a_) * mp.gamma(s)) * D ** ((mp.mpf(1) / 2 - s) / 2)
    tail = mp.fsum(mp.mpf(n) ** (s - mp.mpf(1) / 2) * _sigma(n, 1 - 2 * s) * mp.cos(n * mp.pi * b / a)
                   * mp.besselk(s - mp.mpf(1) / 2, mp.pi * n * mp.sqrt(D) / a_) for n in range(1, terms + 1))
    return t1 + t2 + pre * tail


def direct_sum(s, R: int, form=FORM):
    """sum over 0 < max(|m|, |n|) <= R of Q(m, n)^(-s) (real s > 1, calibration only)."""
    a, b, c = form
    return mp.fsum(mp.mpf(a * m * m + b * m * n + c * n * n) ** (-s)
                   for m in range(-R, R + 1) for n in range(-R, R + 1) if (m, n) != (0, 0))


def newton_root(start, dps: int = 50):
    with mp.workdps(dps):
        return mp.findroot(epstein_cs, mp.mpc(*start), tol=mp.mpf(10) ** (-(dps - 10)))


def winding(f, center, half, steps_per_side: int = 16, max_inc=None) -> dict:
    """Argument-principle count on the square of half-side ``half``; each side is
    refined until every argument increment is below pi/4."""
    max_inc = max_inc if max_inc is not None else mp.pi / 4
    c = mp.mpc(center)
    h = mp.mpf(half)
    corners = [c + mp.mpc(-h, -h), c + mp.mpc(h, -h), c + mp.mpc(h, h), c + mp.mpc(-h, h)]
    total = mp.mpf(0)
    worst = mp.mpf(0)
    evals = 0
    for k in range(4):
        z0, z1 = corners[k], corners[(k + 1) % 4]
        n = steps_per_side
        while True:
            pts = [z0 + (z1 - z0) * j / n for j in range(n + 1)]
            vals = [f(z) for z in pts]
            evals += len(vals)
            incs = [mp.arg(vals[j + 1] / vals[j]) for j in range(n)]
            m = max(abs(x) for x in incs)
            if m < max_inc or n >= 4096:
                break
            n *= 2
        worst = max(worst, m)
        total += mp.fsum(incs)
    w = total / (2 * mp.pi)
    return {"winding": int(mp.nint(w)), "winding_raw": w, "max_increment": worst, "evals": evals}


def census(re0="0.55", re1="1.6", t0=0.5, t1=60.5, window=10, dps: int = 30, progress=False) -> list:
    out = []
    with mp.workdps(dps):
        t = mp.mpf(t0)
        while t < t1:
            top = min(t + window, mp.mpf(t1))
            ctr = mp.mpc((mp.mpf(re0) + mp.mpf(re1)) / 2, (t + top) / 2)
            hx, hy = (mp.mpf(re1) - mp.mpf(re0)) / 2, (top - t) / 2
            out.append((float(t), float(top), _rect_count(epstein_cs, ctr, hx, hy)))
            if progress:
                print("    window", out[-1], flush=True)
            t = top
    return out


def _rect_count(f, c, hx, hy, per_unit: int = 24):
    corners = [c + mp.mpc(-hx, -hy), c + mp.mpc(hx, -hy), c + mp.mpc(hx, hy), c + mp.mpc(-hx, hy)]
    total = mp.mpf(0)
    for k in range(4):
        z0, z1 = corners[k], corners[(k + 1) % 4]
        n = max(8, int(abs(z1 - z0) * per_unit))
        while True:
            vals = [f(z0 + (z1 - z0) * j / n) for j in range(n + 1)]
            incs = [mp.arg(vals[j + 1] / vals[j]) for j in range(n)]
            if max(abs(x) for x in incs) < mp.pi / 4 or n >= 8192:
                break
            n *= 2
        total += mp.fsum(incs)
    return int(mp.nint(total / (2 * mp.pi)))


def locate(re0, re1, t0, t1, min_height=0.6, dps: int = 30, progress=False) -> list:
    """Every zero of zeta_Q in the box, by recursive bisection of argument-principle
    counts down to boxes of height ``min_height``, then Newton from the box centre;
    each root is accepted only if Newton stays inside its box."""
    out = []
    with mp.workdps(dps):
        stack = [(mp.mpf(re0), mp.mpf(re1), mp.mpf(t0), mp.mpf(t1))]
        while stack:
            a, b, c, d = stack.pop()
            n = _rect_count(epstein_cs, mp.mpc((a + b) / 2, (c + d) / 2), (b - a) / 2, (d - c) / 2)
            if n == 0:
                continue
            if d - c > min_height:
                m = (c + d) / 2
                stack += [(a, b, c, m), (a, b, m, d)]
                continue
            if n == 1:
                r = mp.findroot(epstein_cs, mp.mpc((a + b) / 2, (c + d) / 2), tol=mp.mpf(10) ** (-(dps - 8)))
                inside = a <= mp.re(r) <= b and c <= mp.im(r) <= d
                out.append((r, inside, abs(epstein_cs(r))))
            else:
                ma = (a + b) / 2
                stack += [(a, ma, c, d), (ma, b, c, d)]
            if progress:
                print("    box", [float(x) for x in (a, b, c, d)], "count", n, flush=True)
    return sorted(out, key=lambda x: float(mp.im(x[0])))


def completed_own(s):
    """s (s - 1) Lambda_Q(s), Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s), d = 23/4."""
    s = mp.mpc(s)
    d = mp.mpf(23) / 4
    return s * (s - 1) * (mp.sqrt(d) / mp.pi) ** s * mp.gamma(s) * epstein_cs(s)


def defect_own(h, x, y):
    """D_h(z) = log|E_h(conj z)| - log|E_h(z)| for E_h(z) = completed(1/2 + h - i z), z = x + i y."""
    h, x, y = mp.mpf(h), mp.mpf(x), mp.mpf(y)
    half = mp.mpf(1) / 2
    return mp.log(abs(completed_own(half + h - y - 1j * x))) - mp.log(abs(completed_own(half + h + y - 1j * x)))


def xi_own(s):
    """xi(s) = s(s - 1) pi^(-s/2) Gamma(s/2) zeta(s), Conrey and Li's normalization."""
    return s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def conrey_li_numbers(dps: int = 40):
    with mp.workdps(dps):
        rho = mp.zetazero(34)
        n1 = -mp.re(mp.diff(xi_own, rho) * xi_own(1 + rho))
        n2 = mp.re(xi_own(1 + 282j) / xi_own(2 + 282j))
        return rho, n1, n2


@contextmanager
def zero_trap():
    import mpmath
    import zeta.zeros as ZZ

    log, saved = [], []

    def trap(label):
        def f(*a, **k):
            log.append(label)
            raise RuntimeError(label)
        return f

    for obj in (mp, mpmath):
        for name in ("zetazero", "siegelz", "siegeltheta", "grampoint", "nzeros"):
            saved.append((obj, name, getattr(obj, name)))
            setattr(obj, name, trap(name))
    for name in dir(ZZ):
        v = getattr(ZZ, name)
        if not name.startswith("_") and callable(v) and getattr(v, "__module__", "") == ZZ.__name__:
            saved.append((ZZ, name, v))
            setattr(ZZ, name, trap("zeta.zeros." + name))
    try:
        yield log
    finally:
        for obj, name, v in reversed(saved):
            setattr(obj, name, v)


def defect_under_trap() -> dict:
    import dbr_common as D

    out = {}
    with zero_trap() as log:
        for kind in ("zeta", "dh", "epstein"):
            try:
                out[kind] = D.defect_mp(kind, mp.mpf(1) / 4, mp.mpf(20), mp.mpf(1) / 5, dps=20)
            except RuntimeError as e:
                out[kind] = "trapped: %s" % e
    out["log"] = list(log)
    return out


def main() -> int:
    with mp.workdps(30):
        print("calibration s = 3: CS", mp.nstr(epstein_cs(3), 20), "| zeta.epstein",
              mp.nstr(__import__("zeta.epstein", fromlist=["x"]).epstein_zeta(mp.mpf(3), FORM, dps=30), 20))
    with mp.workdps(50):
        r = newton_root(BUILDER_ROOT)
        print("root by own Chowla-Selberg Newton:", mp.nstr(r, 25))
        print("distance to the builder's printed root:", mp.nstr(abs(r - mp.mpc(*BUILDER_ROOT)), 5))
        print("|zeta_Q| at root:", mp.nstr(abs(epstein_cs(r)), 5), " at root + 0.01:", mp.nstr(abs(epstein_cs(r + mp.mpf("0.01"))), 5))
    with mp.workdps(30):
        for label, ctr in (("around rho", r), ("around 1 - conj(rho)", 1 - mp.conj(r)), ("displaced by 0.1", r + mp.mpf("0.1"))):
            w = winding(epstein_cs, ctr, "0.02")
            print("winding %-22s %d (raw %s, max increment %s, %d evaluations)" % (label, w["winding"], mp.nstr(w["winding_raw"], 8), mp.nstr(w["max_increment"], 3), w["evals"]))
    print("census of zeta_Q zeros in [0.55, 1.6] x [0.5, 60.5], by windows of height 10:", flush=True)
    census(progress=True)
    rho, n1, n2 = conrey_li_numbers()
    print("Conrey-Li (3.1) at rho_34 =", mp.nstr(rho, 15), ":", mp.nstr(n1, 16), "| (3.3) at 282:", mp.nstr(n2, 9))
    print("builder defect under a zero trap:", defect_under_trap())
    return 0


if __name__ == "__main__":
    sys.exit(main())
