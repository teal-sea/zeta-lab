"""Route B of the zero census: python-flint (Arb) only, with the segment
decision rule of ``hunts/lambda_dh_bounds/winding.py``.

Code-disjoint from route A (``rivals.py``, mpmath): this module computes its own
least primitive root, takes chi from flint's Conrey table (``dirichlet_char``),
computes k = tan(theta/2) as an Arb ball from its own Gauss sum, and evaluates
F_k(s) = q^{-s} sum_a b(a) zeta(s, a/q) with Arb's Hurwitz zeta.  It shares no
function with ``rivals.py``.  Window boundaries and box centres may come from
route A: they steer placement only, exactly as winding.py's measured locating
pass does, and a wrong placement can make a decision fail, never pass.

The segment rule (winding.py, ``winding_rectangle``).  On an axis-parallel
segment [z_a, z_b] of half-length h, let p be the affine interpolant of F
between the endpoint values.  |F - p| <= M2 h^2 / 2 along the segment when M2
bounds |F''| there.  If the Arb lower bound for dist(0, chord) exceeds the tube
radius M2 h^2 / 2 (winding.py's ``_chord_clearance``, imported), the image lies
in a convex set missing 0, so the continuous change of arg is below pi in
absolute value; a decided Re(F(z_b)/F(z_a)) > 0 then makes it equal Arg of the
quotient.  Undecided segments are halved; a budget overrun returns "undecided",
never an integer.

M2 (the analytic step, cited, then guarded).  winding.py derives its M2 from a
shifted contour of its integral; here it comes from Cauchy's estimate on a
convexity bound.  For every z within h of the midpoint m, the circle
|w - z| = r lies in the disc D = D(m, h + r), so |F''(z)| <= 2 sup_D |F| / r^2,
and the tube radius is sup_D |F| h^2 / r^2.  sup_D |F| <= 2 |A| sup_D |L(w, chi)|
with A = (1 - i k)/2 (chi-bar is primitive too), and

    |L(s, chi)| <= (q |1 + s| / (2 pi))^{(1 + eta - sigma)/2} zeta(1 + eta),
    -eta <= sigma <= 1 + eta,  0 < eta <= 1/2,

for chi primitive mod q > 1 (Rademacher, Math. Z. 72 (1959) 192-204,
Theorem 3; cited from memory, not re-derived).  The right side decreases in
sigma, so its value at the disc's least real part bounds the whole disc; for
sigma > 1 + eta, |L| <= zeta(sigma) <= zeta(1 + eta) is below it.  Several
(eta, r) are tried and the smallest valid tube is kept.  Because a wrong
derivation of M2 would make this route return a wrong integer with status
"decided" (winding.py's control 5 records exactly that), two measured guards
run before the census trusts it: :func:`rademacher_guard` checks the cited
bound against Arb values of |L| at sample points, and :func:`m2_guard` checks
the M2 actually used against Arb jets of F'' along sample legs.

Grade: the counts are enclosure-carrying given (i) the classical functional
equation of Dirichlet L-functions and the Gauss-sum root number, (ii) the
cited Rademacher bound, (iii) winding.py's decision rule.  The guards are
measured.  The reserved enclosure word is not used.
"""

from __future__ import annotations

import math
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
LDB = os.path.join(REPO, "hunts", "lambda_dh_bounds")
if LDB not in sys.path:
    sys.path.insert(0, LDB)

from flint import acb, acb_series, arb, ctx, dirichlet_char, fmpq  # noqa: E402

from winding import _chord_clearance  # noqa: E402  (winding.py's decision rule)

BACKEND = "python-flint (Arb)"
ETAS = (Fraction(1, 2), Fraction(7, 20), Fraction(1, 4), Fraction(9, 50), Fraction(3, 25))
RADII = (Fraction(1, 20), Fraction(1, 10), Fraction(1, 5), Fraction(3, 10), Fraction(9, 20))


class _prec:
    """Set ctx.prec for a block and restore it."""

    def __init__(self, prec: int):
        self.prec = int(prec)

    def __enter__(self):
        self.old = ctx.prec
        ctx.prec = self.prec
        return self

    def __exit__(self, *exc):
        ctx.prec = self.old
        return False


def _arbq(x: Fraction) -> arb:
    return arb(fmpq(x.numerator, x.denominator))


def _acbq(x: Fraction, y: Fraction) -> acb:
    return acb(_arbq(x), _arbq(y))


def _frac(x) -> Fraction:
    return x if isinstance(x, Fraction) else Fraction(x)


def _dyadic(x: arb, den: int) -> Fraction:
    """The multiple of 1/den nearest the exact midpoint of the arb x."""
    m, e = x.mid().man_exp()
    v = Fraction(int(m)) * (Fraction(2) ** int(e))
    return Fraction(round(v * den), den)


def _least_primitive_root(q: int) -> int:
    phi = q - 1
    ps = []
    m = phi
    d = 2
    while d * d <= m:
        if m % d == 0:
            ps.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        ps.append(m)
    for g in range(2, q):
        if all(pow(g, phi // p, q) != 1 for p in ps):
            return g
    raise ValueError(q)


class ArbRival:
    """F_k in Arb, with k from the Gauss sum of flint's character."""

    def __init__(self, q: int, prec: int = 64):
        self.q = q
        self.prec = prec
        g = _least_primitive_root(q)
        with _prec(prec + 64):
            target = acb(0, 1)
            found = None
            for idx in range(1, q):
                try:
                    ch = dirichlet_char(q, idx)
                except Exception:  # noqa: BLE001 - non-coprime index
                    continue
                if ch.order() != 4:
                    continue
                if abs(ch(g) - target) < arb("1e-30"):
                    found = ch
                    break
            if found is None:
                raise ArithmeticError("no order-4 character with chi(g) = i")
            self.char = found
            self.conrey_index = idx
            self.parity = int(found.parity())
            vals = [found(a) for a in range(q)]
            tau = acb(0)
            for a in range(1, q):
                tau += vals[a] * (acb(0, 2) * arb.pi() * a / q).exp()
            eps = tau / (acb(0, 1) ** self.parity * arb(q).sqrt())
            self.eps = eps
            self.theta_root = eps.arg()
            self.k = (self.theta_root / 2).tan()
            self.absA_upper = float(((1 + self.k * self.k).sqrt() / 2).upper())
            self.weights = []
            self.dom_weights = []
            for a in range(1, q):
                re, im = vals[a].real, vals[a].imag
                b = re + self.k * im
                if not (b == 0):
                    self.weights.append((a, b))
                self.dom_weights.append((a, abs(re) + abs(self.k) * abs(im)))
            self._zeta_eta = {eta: _arbq(1 + eta).zeta() for eta in ETAS}
        self.n_evals = 0

    # -- evaluation --------------------------------------------------------

    def F(self, s: acb) -> acb:
        self.n_evals += 1
        q = self.q
        tot = acb(0)
        for a, b in self.weights:
            tot += b * s.zeta(acb(fmpq(a, q)))
        return tot * (-s * arb(q).log()).exp()

    def F_at(self, x: Fraction, y: Fraction) -> acb:
        with _prec(self.prec):
            return self.F(_acbq(x, y))

    def theta(self, t: Fraction) -> arb:
        with _prec(self.prec):
            tt = _arbq(t)
            z = acb(arb(1) / 2 + self.parity, tt) / 2
            return tt / 2 * (arb(self.q) / arb.pi()).log() + z.lgamma().imag

    def Z_sign(self, t: Fraction) -> int:
        """Decided sign of Z(t) = e^{i theta} F(1/2 + it), or 0 if undecided."""
        with _prec(self.prec):
            th = self.theta(t)
            v = acb(th.cos(), th.sin()) * self.F(_acbq(Fraction(1, 2), t))
            if not v.imag.contains(arb(0)):
                raise ArithmeticError(f"Z({t}) has an imaginary part excluding 0")
            r = v.real
            if r > 0:
                return 1
            if r < 0:
                return -1
            return 0

    # -- the analytic step: tube radius from Rademacher + Cauchy -------------

    def tube_radius(self, mx: Fraction, my: Fraction, h: Fraction) -> float:
        """Upper bound for sup |F - p| on the segment of half-length h at m."""
        best = math.inf
        for r in RADII:
            rho = h + r
            sig_min = mx - rho
            sig_max = mx + rho
            im_max = abs(my) + rho
            re1 = max(abs(1 + sig_min), abs(1 + sig_max))
            with _prec(self.prec):
                absz1 = (_arbq(re1) ** 2 + _arbq(im_max) ** 2).sqrt()
                X = arb(self.q) * absz1 / (2 * arb.pi())
                for eta in ETAS:
                    if sig_min < -eta:
                        continue
                    if sig_min > 1 + eta:
                        bound_L = _arbq(sig_min).zeta()
                    else:
                        expo = (1 + _arbq(eta) - _arbq(sig_min)) / 2
                        bound_L = self._zeta_eta[eta] * X ** expo
                    supF = 2 * self.absA_upper * bound_L
                    tube = supF * _arbq(h) ** 2 / _arbq(r) ** 2
                    best = min(best, float(tube.upper()) * (1 + 1e-12))
        return best

    # -- one segment, and a path of axis-parallel segments --------------------

    def arg_change(self, za: tuple, zb: tuple, max_segments: int = 20000,
                   min_half: Fraction = Fraction(1, 2 ** 30), cache: dict | None = None,
                   max_wall: float = 3600.0) -> dict:
        """Decided continuous change of arg F along the segment za -> zb."""
        t0 = time.time()
        if cache is None:
            cache = {}

        def val(z):
            got = cache.get(z)
            if got is None:
                got = self.F_at(z[0], z[1])
                cache[z] = got
            return got

        stack = [(tuple(map(_frac, za)), tuple(map(_frac, zb)))]
        args = []
        n_seg = 0
        min_margin = math.inf
        while stack:
            if n_seg + len(stack) > max_segments or time.time() - t0 > max_wall:
                return {"status": "undecided", "reason": "budget", "segment": stack[-1]}
            a, b = stack.pop()
            h = (abs(b[0] - a[0]) + abs(b[1] - a[1])) / 2
            mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
            A = val(a)
            B = val(b)
            with _prec(self.prec):
                tube = self.tube_radius(mx, my, h)
                d = _chord_clearance(A, B)
                qt = B / A
                ok = (d.lower() > tube) and (qt.real > 0)
                if ok:
                    args.append(qt.arg())
                    n_seg += 1
                    dl = float(d.lower())
                    if tube > 0:
                        min_margin = min(min_margin, math.log10(dl / tube))
                    continue
            if h / 2 < min_half:
                return {"status": "undecided", "reason": "min_half", "segment": (a, b)}
            mid = ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)
            stack.append((mid, b))
            stack.append((a, mid))
        with _prec(self.prec):
            tot = arb(0)
            for g in args:
                tot += g
        return {"status": "decided", "arg": tot, "n_segments": n_seg,
                "min_margin_digits": min_margin}

    def domination_holds(self, sR: Fraction) -> bool:
        """Decided sum_{n>=2} |b(n)| n^{-sR} < 1 (strip.py's g(sR) < 0)."""
        with _prec(self.prec + 32):
            s = acb(_arbq(sR))
            tot = arb(0)
            for a, w in self.dom_weights:
                if w == 0:
                    continue
                z = s.zeta(acb(fmpq(a, self.q)))
                tot += w * z.real
            g = tot * (arb(self.q) ** (-_arbq(sR))) - 2
            return bool(g < 0)

    def psi(self, T: Fraction, sR: Fraction, cache: dict | None = None) -> dict:
        """Decided Psi(T)/pi and the count N(0, T) (folded argument principle)."""
        T = _frac(T)
        sR = _frac(sR)
        FR = self.F_at(sR, T)
        with _prec(self.prec):
            if not (FR.real > 0):
                return {"status": "undecided", "reason": "Re F(sR + iT) not decided positive"}
            argR = FR.arg()
        leg = self.arg_change((sR, T), (Fraction(1, 2), T), cache=cache)
        if leg["status"] != "decided":
            return {"status": "undecided", "reason": "leg", "leg": leg}
        with _prec(self.prec):
            x = (self.theta(T) + argR + leg["arg"]) / arb.pi()
            lo = math.ceil(float(x.lower()))
            hi = math.floor(float(x.upper()))
            out = {"T": str(T), "psi_over_pi_lower": float(x.lower()),
                   "psi_over_pi_upper": float(x.upper()),
                   "n_segments": leg["n_segments"],
                   "min_margin_digits": leg["min_margin_digits"]}
            if lo == hi and float(x.upper() - x.lower()) < 0.5:
                out.update(status="decided", N=lo)
            else:
                out.update(status="undecided", reason="ball does not pin an integer")
            return out

    def winding_box(self, x0, x1, y0, y1, cache: dict | None = None) -> dict:
        """Decided winding number of F around [x0, x1] x [y0, y1]."""
        x0, x1, y0, y1 = map(_frac, (x0, x1, y0, y1))
        cs = [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]
        if cache is None:
            cache = {}
        side = min(x1 - x0, y1 - y0)
        min_half = min(Fraction(1, 2 ** 30), side / 2 ** 16)
        tot = None
        nseg = 0
        margin = math.inf
        for i in range(4):
            r = self.arg_change(cs[i], cs[(i + 1) % 4], cache=cache, min_half=min_half)
            if r["status"] != "decided":
                return {"status": "undecided", "edge": i, "detail": r}
            tot = r["arg"] if tot is None else tot + r["arg"]
            nseg += r["n_segments"]
            margin = min(margin, r["min_margin_digits"])
        with _prec(self.prec):
            w = tot / (2 * arb.pi())
            lo = math.ceil(float(w.lower()))
            hi = math.floor(float(w.upper()))
        out = {"box": [str(x0), str(x1), str(y0), str(y1)],
               "winding_lower": float(w.lower()), "winding_upper": float(w.upper()),
               "n_segments": nseg, "min_margin_digits": margin}
        if lo == hi:
            out.update(status="decided", N=lo)
        else:
            out.update(status="undecided", reason="winding ball does not pin an integer")
        return out

    def F_jet(self, s: acb, order: int = 2) -> list:
        """[F(s), F'(s), F''(s)/2, ...] at the point s (Arb series)."""
        ser = acb_series([s, 1], prec=order + 1)
        tot = None
        for a, b in self.weights:
            term = acb_series.zeta(ser, acb(fmpq(a, self.q))) * b
            tot = term if tot is None else tot + term
        lq = arb(self.q).log()
        e = acb_series([-s * lq, -lq], prec=order + 1).exp()
        return (tot * e).coeffs()

    def polish(self, x0: float, y0: float, prec: int = 160, iters: int = 30) -> tuple:
        """Newton on Arb midpoints at ``prec`` bits: steers the tiny boxes only."""
        with _prec(prec):
            s = acb(x0, y0)
            for _ in range(iters):
                f, df = self.F_jet(s, 1)[:2]
                ds = f / df
                s = acb(s.mid() - ds.mid())
                if float(abs(ds).upper()) < 2.0 ** (-(prec - 20)):
                    break
            return s.real.mid(), s.imag.mid(), float(abs(self.F(s)).upper())

    def tiny_box(self, x0: float, y0: float, log2_half: int = 30) -> dict:
        """Polish, round the root to a dyadic centre, decide a box of half-width
        2^-log2_half around it.  Returns the decided winding and the box."""
        xr, yr, res = self.polish(x0, y0)
        den = 2 ** (log2_half + 8)
        cx = _dyadic(xr, den)
        cy = _dyadic(yr, den)
        w = Fraction(1, 2 ** log2_half)
        old = self.prec
        self.prec = max(self.prec, 128)
        try:
            out = self.winding_box(cx - w, cx + w, cy - w, cy + w)
        finally:
            self.prec = old
        out["centre"] = [str(cx), str(cy)]
        out["half_width"] = f"2^-{log2_half}"
        out["polish_residual"] = res
        return out

    # -- measured guards for the cited analytic step --------------------------

    def rademacher_guard(self, points) -> dict:
        """Measured: Arb |L(s, chi)| against the cited bound at sample points."""
        worst = 0.0
        rows = []
        with _prec(self.prec):
            for (x, y) in points:
                s = _acbq(_frac(x), _frac(y))
                Lv = acb.dirichlet_l(s, self.char)
                absz1 = abs(1 + s)
                X = arb(self.q) * absz1 / (2 * arb.pi())
                bounds = []
                for eta in ETAS:
                    if -eta <= _frac(x) <= 1 + eta:
                        expo = (1 + _arbq(eta) - _arbq(_frac(x))) / 2
                        bounds.append(float((self._zeta_eta[eta] * X ** expo).lower()))
                if not bounds:
                    continue
                ratio = float(abs(Lv).upper()) / min(bounds)
                worst = max(worst, ratio)
                rows.append({"s": [float(x), float(y)], "ratio_L_over_bound": ratio})
        return {"max_ratio": worst, "passed": worst < 1.0, "rows": rows}

    def m2_guard(self, mx, my, h, n: int = 9) -> dict:
        """Measured: max Arb |F''| at n points of a segment against the M2 used."""
        mx, my, h = map(_frac, (mx, my, h))
        tube = self.tube_radius(mx, my, h)
        m2_used = 2 * tube / float(h) ** 2
        worst = 0.0
        with _prec(self.prec):
            for j in range(n):
                off = -h + 2 * h * Fraction(j, n - 1)
                for (x, y) in ((mx + off, my), (mx, my + off)):
                    s = _acbq(x, y)
                    ser = acb_series([s, 1], prec=3)
                    tot = None
                    for a, b in self.weights:
                        term = acb_series.zeta(ser, acb(fmpq(a, self.q))) * b
                        tot = term if tot is None else tot + term
                    e = acb_series([-s * arb(self.q).log(), -arb(self.q).log()], prec=3).exp()
                    full = tot * e
                    d2 = 2 * full.coeffs()[2]
                    worst = max(worst, float(abs(d2).upper()))
        return {"m2_used": m2_used, "max_measured_F2": worst,
                "ratio": worst / m2_used, "passed": worst < m2_used}
