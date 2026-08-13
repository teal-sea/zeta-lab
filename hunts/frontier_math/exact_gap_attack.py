"""The retention gap as ONE functional, and what closes it.

Companion to ``spectral_gap.py`` (which found the one-functional form) and
to the kernel-checked identity ``Retention.retention_gap`` in
``zeta23ext/Zeta23Ext/EForm3/Gap.lean``.  This module answers the question
the form poses: *does the identity close as a single inequality, with no
near/far split and no separation hypothesis?*

THE OBJECT.  With ``g u = cos(sqrt 2 u)`` on ``|u| <= 1/2``, ``A = int g``,
``c2 = g * g`` the autocorrelation (nonnegative, supported in ``[-1,1]``),
``phiR s = Qre 0 s``, ``K = phiR^2`` and ``W_y s = Qre y s ^2 - Qim y s ^2``,
the retention gap of a configuration ``x_1..x_n`` at damage centre ``t``,
``gap = E[F+P] - (199/200) E[F] - n/200 - 4``, satisfies ``gap = S / A^2``
with

    S(x; y, t) = (1/200) * sum_{j != k} K(x_j - x_k)
               + 4 * sum_j W_y(x_j - t)
               + 2 * Shq(y),            Shq y = Qre (2y) 0 ^2 - A^2.

(The diagonal of the double sum is exactly ``n K(0) = n A^2``, which is what
the ``- n A^2`` of the identity cancels; ``2 Shq = 8 A Shq_int + 8 Shq_int^2``
in the ``Shq_int = int g sinh^2(y u)`` normalisation, see FAR-FIELD-EXCHANGE
section 5.)

THE THREE STRUCTURAL FACTS, all measured here:

1. ``K`` and ``W_y`` are cosine transforms of the SAME nonnegative weight:
   ``K u = int c2 w cos(u w) dw`` and ``W_y s = int c2 w cosh(y w) cos(s w) dw``
   (the master identity), and ``2 Shq y = 4 int c2 w sinh^2(y w) dw``.  So the
   whole gap is one integral against ``c2 dw`` — ``gap_spectral`` below.
2. ``K`` is positive definite (its spectral density is ``c2 >= 0``) AND
   pointwise nonnegative, because it is a square.  The second fact is the
   load-bearing one: EVERY off-diagonal pair contributes ``>= 0``, so pairs
   may be discarded one at a time without sign bookkeeping.
3. ``K`` is bounded BELOW on short distances: ``K u >= K(w) > 0`` for
   ``|u| <= w < 2 pi``.  Two points close together therefore pay a definite
   positive price into the quadratic term.

WHAT THE CONVEX RELAXATION SAYS: NO.  Relaxing the n unit atoms to a
nonnegative measure of mass n gives a convex QP whose minimum lower-bounds
the truth.  Mass may be sent to infinity as dust — spread thin it pays no
energy, and ``W_y -> 0`` so it collects no damage — which makes the infimum
over the line exactly

    inf gap = [C*(n) + 2 Shq y]/A^2 - n/200,  C*(n) = inf over nu >= 0, |nu| <= n.

``C*(n)`` saturates at ``C* = -0.038776`` once ``n >= 5.99``, so from ``n = 6``
the relaxed infimum is the straight line ``0.114022 - n/200``: it crosses zero
at ``n = 23`` and falls without bound.  The minimiser is not a configuration —
peak mass ``2.07819``, fractional, with the excess as dust.  The mechanism is
structural, not numerical: ``- n A^2`` is the self-energy of n unit atoms, and
a diffuse measure of the same mass keeps the subtraction while paying none of
the self-energy.  Since the convex hull of the n-unit-atom measures contains
the diffuse ones, NO convex relaxation of the atom constraint can close this.
Integrality is not a technicality here; it is the whole content.

WHAT DOES CLOSE IT: integrality used per damage window.  The damage
``D_y s = max(0, -W_y s)`` is supported on narrow windows (width ``<= 0.986``
at ``y = 1/2``) recurring near ``2 pi k``, and ``D_y = 0`` on ``|s| <= 6.065``.
Two points inside one window are within the window width of each other, so
``m`` points in one window pay ``>= (kappa/200) m (m-1)`` into the quadratic
term while collecting at most ``4 D_k m`` of damage — and ``m`` is an INTEGER.
Maximising ``4 D_k m - (kappa/200) m (m-1)`` over integers and summing over
windows gives, with no separation hypothesis and no dependence on n:

    S >= 2 Shq(y) - sum_k P_k(y) > 0     for every n, every x, every t,

margin ``1.724x`` at the worst y (= 1/2) and ``2.51x`` as ``y -> 0`` on the
measured constants (``window_bound``), ``1.634x`` on the rational constants a
prover would use (``rational_certificate``, exact Fractions, Lean's own
``Shq_half_lower`` and far-field majorant ``Wt``).  In gap units the bound is
``+0.0672`` measured, ``+0.0597`` rational, against a measured infimum over all
configurations and all n of ``+0.0748``.  ``PROBLEM.md`` in the session
scratchpad states the whole thing for a prover, with the obligations listed.

Nothing here is a proof: the window table, the window width and ``kappa`` are
measured, not enclosed, and the tail beyond the scan is bounded by a measured
envelope.

Run ``.venv/bin/python hunts/frontier_math/exact_gap_attack.py`` (~5 min).
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction as F
from typing import Sequence

import numpy as np

__all__ = [
    "A",
    "A2",
    "c2",
    "qre",
    "qim",
    "phi_r",
    "K",
    "damage_profile",
    "damage",
    "shq",
    "gap_kernel",
    "gap_spectral",
    "gap_energy",
    "energy",
    "gram_matrix",
    "gram_eigenvalues",
    "kernel_is_decreasing",
    "relaxed_minimum",
    "diffuse_value",
    "atomic_minimum",
    "damage_windows",
    "window_bound",
    "rational_certificate",
    "integer_deficit_exact",
    "Wt",
    "audit",
]

S2 = math.sqrt(2.0)
#: ``A = int g = sqrt 2 sin(1/sqrt 2)``.
A = S2 * math.sin(1 / S2)
A2 = A * A
#: the quadratic coefficient of the identity, ``1 - theta`` with ``theta = 199/200``.
COEF = 1.0 / 200.0


# ---------------------------------------------------------------------------
# closed forms (every one of them checked against quadrature in the tests)
# ---------------------------------------------------------------------------


def c2(w):
    """``c2 w = int g u g(u+w) du``: even, supported in ``[-1,1]``, ``>= 0``.

    Closed form: ``(1-|w|) cos(sqrt2 |w|)/2 + sin(sqrt2 (1-|w|))/(2 sqrt2)``.
    """
    w = np.abs(np.asarray(w, dtype=float))
    out = (1.0 - w) * np.cos(S2 * w) / 2.0 + np.sin(S2 * (1.0 - w)) / (2.0 * S2)
    return np.where(w >= 1.0, 0.0, out)


def qre(a, b):
    """``Qre a b = int g u cosh(a u) cos(b u) du`` (``EForm3.Qre_closed``)."""
    b = np.asarray(b, dtype=float)
    p, m = b + S2, b - S2
    return ((a * math.sinh(a / 2) * np.cos(p / 2) + p * math.cosh(a / 2) * np.sin(p / 2))
            / (a * a + p * p)
            + (a * math.sinh(a / 2) * np.cos(m / 2) + m * math.cosh(a / 2) * np.sin(m / 2))
            / (a * a + m * m))


def qim(a, b):
    """``Qim a b = int g u sinh(a u) sin(b u) du`` (``EForm3.Qim_closed``)."""
    b = np.asarray(b, dtype=float)
    p, m = b + S2, b - S2
    return ((a * math.cosh(a / 2) * np.sin(p / 2) - p * math.sinh(a / 2) * np.cos(p / 2))
            / (a * a + p * p)
            + (a * math.cosh(a / 2) * np.sin(m / 2) - m * math.sinh(a / 2) * np.cos(m / 2))
            / (a * a + m * m))


def phi_r(u):
    """``phiR u = Qre 0 u``, the transform whose square is the pair kernel."""
    return qre(0.0, u)


def K(u):
    """The pair kernel ``K = phiR^2``.  A square, hence ``>= 0`` pointwise;
    also positive definite, its spectral density being ``c2 >= 0``."""
    return phi_r(u) ** 2


def damage_profile(y, s):
    """``W_y s = Qre y s ^2 - Qim y s ^2 = int c2 w cosh(y w) cos(s w) dw``."""
    return qre(y, s) ** 2 - qim(y, s) ** 2


def damage(y, s):
    """``D_y s = max(0, -W_y s)``, the part of the profile that costs."""
    return np.maximum(0.0, -damage_profile(y, s))


def shq(y):
    """``Shq y = Qre (2y) 0 ^2 - A^2`` (the prover normalisation)."""
    return float(qre(2.0 * y, 0.0)) ** 2 - A2


# ---------------------------------------------------------------------------
# three independent routes to the same gap
# ---------------------------------------------------------------------------


def gap_kernel(xs: Sequence[float], y: float, t: float) -> float:
    """The gap straight from the identity: closed forms, no quadrature."""
    x = np.asarray(xs, dtype=float)
    n = len(x)
    rep = float(K(x[:, None] - x[None, :]).sum()) - n * A2
    dam = float(np.sum(damage_profile(y, x - t)))
    return (COEF * rep + 4.0 * dam + 2.0 * shq(y)) / A2


def _gauss(nodes: int = 600):
    """Gauss-Legendre nodes for ``[-1,0]`` and ``[0,1]`` (``c2`` kinks at 0)."""
    z, wt = np.polynomial.legendre.leggauss(nodes)
    left = (z - 1.0) / 2.0, wt / 2.0
    right = (z + 1.0) / 2.0, wt / 2.0
    w = np.concatenate([left[0], right[0]])
    m = np.concatenate([left[1], right[1]])
    return w, m


_W_NODES, _W_WEIGHTS = _gauss()


def gap_spectral(xs: Sequence[float], y: float, t: float, nodes: int = 600) -> float:
    """The gap as ONE integral against ``c2 dw`` — the single-functional form.

    ``gap = (1/A^2) int c2 w [ (|F w|^2 - n)/200 + 4 cosh(y w) Re(F w e^{-i t w})
    + 4 sinh^2(y w) ] dw`` with ``F w = sum_j e^{i x_j w}``.
    """
    x = np.asarray(xs, dtype=float)
    n = len(x)
    w, m = (_W_NODES, _W_WEIGHTS) if nodes == 600 else _gauss(nodes)
    F = np.exp(1j * np.outer(x, w)).sum(axis=0)
    integrand = (c2(w) * ((np.abs(F) ** 2 - n) * COEF
                          + 4.0 * np.cosh(y * w) * (F * np.exp(-1j * t * w)).real
                          + 4.0 * np.sinh(y * w) ** 2))
    return float(integrand @ m) / A2


def energy(xs: Sequence[float], y: float | None, t: float, nodes: int = 600) -> float:
    """``E[G] = (1/A^2) int_{-1}^{1} c2 w |G w|^2 dw`` for ``G = F`` (``y`` None)
    or ``G = F + P`` with ``P w = 2 cosh(y w) e^{i t w}``."""
    x = np.asarray(xs, dtype=float)
    w, m = (_W_NODES, _W_WEIGHTS) if nodes == 600 else _gauss(nodes)
    G = np.exp(1j * np.outer(x, w)).sum(axis=0) if len(x) else np.zeros_like(w, dtype=complex)
    if y is not None:
        G = G + 2.0 * np.cosh(y * w) * np.exp(1j * t * w)
    return float((c2(w) * np.abs(G) ** 2) @ m) / A2


def gap_energy(xs: Sequence[float], y: float, t: float, nodes: int = 600) -> float:
    """The gap from the two energies, i.e. from the statement being proved."""
    n = len(xs)
    return (energy(xs, y, t, nodes) - (199.0 / 200.0) * energy(xs, None, t, nodes)
            - n / 200.0 - 4.0)


# ---------------------------------------------------------------------------
# the quadratic form and its spectrum
# ---------------------------------------------------------------------------


def gram_matrix(grid: np.ndarray) -> np.ndarray:
    """``[K(u_i - u_l)]``, the Gram matrix of the pair kernel on a grid."""
    grid = np.asarray(grid, dtype=float)
    return K(grid[:, None] - grid[None, :])


def gram_eigenvalues(grid: np.ndarray) -> np.ndarray:
    return np.linalg.eigvalsh(gram_matrix(grid))


def kernel_is_decreasing(upper: float = 2 * math.pi, step: float = 1e-4) -> float:
    """Worst increase of ``K`` on ``[0, upper]``; ``<= 0`` means monotone."""
    u = np.arange(0.0, upper + step, step)
    return float(np.max(np.diff(K(u))))


# ---------------------------------------------------------------------------
# the convex relaxation: nonnegative measures of mass n
# ---------------------------------------------------------------------------


@dataclass
class Relaxed:
    n: int
    y: float
    half_width: float
    step: float
    value: float
    grid_points: int
    peak_mass: float
    effective_support: int
    mass_within_8: float
    diffuse: float


def diffuse_value(n: int, y: float) -> float:
    """The value approached by dust: mass n smeared to zero density.

    ``S -> 2 Shq(y) - n A^2 / 200`` (the quadratic term and the linear term
    both vanish), so ``gap -> (2 Shq - n A^2/200)/A^2``.  This is an upper
    bound for the relaxed minimum, and it decreases without bound in n.
    """
    return (2.0 * shq(y) - n * A2 * COEF) / A2


def relaxed_minimum(n: int, y: float, half_width: float = 60.0, step: float = 0.1,
                    solver: str | None = None) -> Relaxed:
    """Minimise the gap over nonnegative measures of mass ``n`` on a grid.

    Convex QP (``K`` is PSD, the quadratic coefficient ``+1/200`` is positive),
    so the value is a genuine lower bound for the minimum over integer
    configurations supported on the same grid.
    """
    import cvxpy as cp

    u = np.arange(-half_width, half_width + step / 2, step)
    Km = gram_matrix(u)
    w = damage_profile(y, u)
    m = cp.Variable(len(u), nonneg=True)
    obj = cp.Minimize(cp.quad_form(m, cp.psd_wrap(Km)) * COEF + 4.0 * (w @ m))
    prob = cp.Problem(obj, [cp.sum(m) == n])
    prob.solve(solver=solver or cp.CLARABEL)
    mv = np.asarray(m.value).ravel()
    value = (prob.value - n * A2 * COEF + 2.0 * shq(y)) / A2
    peak = float(mv.max())
    return Relaxed(n=n, y=y, half_width=half_width, step=step, value=float(value),
                   grid_points=len(u), peak_mass=peak,
                   effective_support=int((mv > 1e-4 * max(peak, 1e-12)).sum()),
                   mass_within_8=float(mv[np.abs(u) < 8.0].sum()),
                   diffuse=diffuse_value(n, y))


def relaxed_infimum(n: int, y: float, half_width: float = 45.0, step: float = 0.05,
                    solver: str | None = None):
    """The relaxation's true infimum over nonnegative measures on the LINE.

    Mass may be sent to infinity as dust: it pays no energy (spread thin) and
    collects no damage (``W -> 0``), so the infimum over measures of mass
    exactly ``n`` equals the infimum over measures of mass ``<= n`` supported
    near the origin.  Hence

        inf gap = [C*(n) + 2 Shq(y)] / A^2 - n/200,
        C*(n) = inf { (1/200)<nu,K nu> + 4<nu,W> : nu >= 0, |nu| <= n },

    and since ``C*(n)`` saturates at a finite ``C*`` once ``n`` exceeds the
    optimal mass, the infimum decreases in ``n`` at exactly ``-1/200`` per
    atom, without bound.  Returns ``(value, C_star, masses, grid)``.
    """
    import cvxpy as cp

    u = np.arange(-half_width, half_width + step / 2, step)
    Km = gram_matrix(u)
    w = damage_profile(y, u)
    m = cp.Variable(len(u), nonneg=True)
    prob = cp.Problem(cp.Minimize(cp.quad_form(m, cp.psd_wrap(Km)) * COEF + 4.0 * (w @ m)),
                      [cp.sum(m) <= n])
    prob.solve(solver=solver or cp.CLARABEL)
    c_star = float(prob.value)
    value = (c_star + 2.0 * shq(y)) / A2 - n * COEF
    return value, c_star, np.asarray(m.value).ravel(), u


def grid_objective(masses: Sequence[float], grid: Sequence[float], y: float,
                   t: float = 0.0) -> float:
    """The same objective as ``relaxed_minimum`` evaluated at given masses.

    For integer masses this equals ``gap_kernel`` of the configuration that
    repeats each grid point that many times — which is what makes the relaxed
    value a lower bound for the integer one.
    """
    mv = np.asarray(masses, dtype=float)
    u = np.asarray(grid, dtype=float)
    n = float(mv.sum())
    quad = float(mv @ gram_matrix(u) @ mv)
    lin = float(damage_profile(y, u - t) @ mv)
    return (COEF * (quad - n * A2) + 4.0 * lin + 2.0 * shq(y)) / A2


# ---------------------------------------------------------------------------
# the true (atomic) minimum
# ---------------------------------------------------------------------------


def _grad(x: np.ndarray, y: float, t: float, eps: float = 1e-6) -> np.ndarray:
    d = x[:, None] - x[None, :]
    dK = (K(d + eps) - K(d - eps)) / (2 * eps)
    s = x - t
    dW = (damage_profile(y, s + eps) - damage_profile(y, s - eps)) / (2 * eps)
    return (2.0 * COEF * dK.sum(axis=1) + 4.0 * dW) / A2


def adversary_design(n: int, y: float, t: float = 0.0, reach: float = 60.0) -> np.ndarray:
    """The configuration the structure predicts the adversary wants.

    Fill the damage windows outward from the centre, giving window ``k`` the
    multiplicity that maximises ``4 D_k m - (A^2/200) m (m-1)`` — the integer
    trade with coincident points, whose pair price is ``K(0) = A^2``.
    """
    wins = damage_windows(y, s_max=reach)
    out: list[float] = []
    for w in wins:
        _, mult = integer_deficit(w.cap, A2 * COEF)
        peak = 0.5 * (w.lo + w.hi)
        for sign in (1.0, -1.0):
            out += [t + sign * peak] * max(mult, 1)
    return np.array(out[:n], dtype=float)


def atomic_minimum(n: int, y: float, t: float = 0.0, seed: int = 0,
                   n_random: int = 40, reach: float = 60.0,
                   warm: Sequence[float] | None = None):
    """Minimise the gap over n-point configurations (multistart L-BFGS).

    Structured starts place points on the damage peaks with the multiplicity
    the integer trade prefers — the family the adversary actually wants —
    plus random starts and, optionally, a warm start grown from the best
    ``n-1`` point configuration.
    """
    from scipy.optimize import minimize

    rng = np.random.default_rng(seed)
    peaks = [0.5 * (w.lo + w.hi) for w in damage_windows(y, s_max=reach)]
    pool = [p + t for p in peaks] + [-p + t for p in peaks]
    starts = [adversary_design(n, y, t, reach)] if n else []
    if warm is not None and len(warm) == n - 1:
        for p in pool[:6]:
            starts.append(np.r_[np.asarray(warm, dtype=float), p])
    for rep in range(1, 9):
        base: list[float] = []
        for p in pool:
            base += [p + 0.02 * j for j in range(rep)]
        base.sort(key=lambda v: abs(v - t))
        if len(base) >= n:
            starts.append(np.array(base[:n]))
    for _ in range(n_random):
        starts.append(rng.uniform(t - reach, t + reach, n))
    for _ in range(n_random // 2):
        starts.append(np.array(rng.choice(pool, size=n)) + rng.normal(0, 0.25, n))
    best, bx = math.inf, None
    for x0 in starts:
        if len(x0) != n:
            continue
        res = minimize(lambda z: gap_kernel(z, y, t), x0,
                       jac=lambda z: _grad(np.asarray(z), y, t), method="L-BFGS-B",
                       options=dict(maxiter=500, ftol=1e-15, gtol=1e-12))
        if res.fun < best:
            best, bx = float(res.fun), np.asarray(res.x)
    return best, np.sort(bx)


# ---------------------------------------------------------------------------
# the integrality-aware bound: damage windows and cluster prices
# ---------------------------------------------------------------------------


@dataclass
class Window:
    lo: float
    hi: float
    cap: float

    @property
    def width(self) -> float:
        return self.hi - self.lo


def damage_windows(y: float, s_max: float = 400.0, step: float = 1e-4,
                   safety: float = 1e-6) -> list[Window]:
    """The intervals of ``s > 0`` on which ``D_y > 0``, with a cap on each.

    Edges are refined by bisection, the cap is the local maximum found by a
    bounded search and then inflated by ``safety`` (relative).  Windows on the
    negative axis are the mirror images (``D_y`` is even).
    """
    from scipy.optimize import brentq, minimize_scalar

    s = np.arange(0.0, s_max, step)
    d = -damage_profile(y, s)
    pos = d > 0
    ch = np.diff(pos.astype(np.int8))
    starts = np.flatnonzero(ch == 1)
    ends = np.flatnonzero(ch == -1) + 1
    if pos[0]:
        starts = np.r_[0, starts]
    if pos[-1]:
        ends = np.r_[ends, len(pos) - 1]
    out: list[Window] = []
    f = lambda v: -float(damage_profile(y, v))
    for i0, i1 in zip(starts, ends):
        lo = brentq(f, s[i0], s[i0 + 1], xtol=1e-13) if i0 + 1 < len(s) else s[i0]
        hi = brentq(f, s[i1 - 1], s[i1], xtol=1e-13) if i1 < len(s) else s[i1]
        res = minimize_scalar(lambda v: damage_profile(y, v), bounds=(lo, hi),
                              method="bounded", options=dict(xatol=1e-12))
        cap = max(float(-res.fun), float(d[i0:i1 + 1].max()))
        out.append(Window(lo=float(lo), hi=float(hi), cap=cap * (1.0 + safety)))
    return out


def qim_envelope(y: float, s_from: float, s_to: float | None = None,
                 step: float = 1e-3) -> float:
    """``sup |Qim y s| * s / y`` over ``s >= s_from`` (measured to ``s_to``).

    ``|Qim| <= env * y / s`` is the far-field majorant used for the tail; it
    decreases in ``s_from`` (measured), so a value read off a finite range is
    used as the majorant for the whole tail.
    """
    s_to = s_to or (s_from + 8.0 * math.pi)
    s = np.arange(s_from, s_to, step)
    return float(np.max(np.abs(qim(y, s)) * s / y))


def integer_deficit(cap: float, q: float) -> tuple[float, int]:
    """``max_{m in Z>=0} [4 cap m - q m (m-1)]`` and the maximising ``m``.

    This is where integrality enters: over the reals the maximum sits at
    ``m* = 1/2 + 2 cap/q`` and the relaxation may take any mass it likes; over
    the integers the price ``q m (m-1)`` is paid in full from the second point on.
    """
    mstar = 0.5 + 2.0 * cap / q
    best, arg = 0.0, 0
    for m in {0, 1, 2, int(math.floor(mstar)), int(math.ceil(mstar))}:
        if m < 0:
            continue
        v = 4.0 * cap * m - q * m * (m - 1)
        if v > best:
            best, arg = v, m
    return best, arg


@dataclass
class WindowBound:
    y: float
    width: float
    kappa: float
    q: float
    windows: int
    deficit: float
    tail: float
    budget: float
    bound_S: float
    bound_gap: float
    margin: float
    worst_window: tuple = field(default=())

    def __str__(self) -> str:  # pragma: no cover - display only
        return (f"y={self.y:.3f} width={self.width:.5f} kappa={self.kappa:.6f} "
                f"deficit={self.deficit:.6e} (+tail {self.tail:.2e}) "
                f"budget={self.budget:.6e} bound_gap={self.bound_gap:+.6e} "
                f"margin={self.margin:.4f}x")


def window_bound(y: float, s_max: float = 400.0, step: float = 1e-4,
                 damage_scale: float = 1.0, kappa_override: float | None = None,
                 width_override: float | None = None) -> WindowBound:
    """A lower bound on the gap, uniform in n, with no separation hypothesis.

    ``S >= 2 Shq(y) - sum_k P_k`` where ``P_k`` is the integer deficit of
    window ``k`` at price ``q = kappa/200``, ``kappa = min_{|u| <= width} K u``
    and ``width`` the widest damage window.  ``damage_scale`` and the two
    overrides exist for the lesion controls: inflating the damage or degrading
    the price must turn the bound negative.
    """
    wins = damage_windows(y, s_max=s_max, step=step)
    width = width_override if width_override is not None else max(w.width for w in wins)
    kappa = kappa_override if kappa_override is not None else float(K(width))
    q = kappa / 200.0
    total, worst = 0.0, (0, 0.0, 0)
    for k, win in enumerate(wins):
        p, m = integer_deficit(win.cap * damage_scale, q)
        total += p
        if p > worst[1]:
            worst = (k, p, m)
    env = qim_envelope(y, s_max)
    # windows beyond the scan: peaks <= (env y / s)^2, left edges >= s_max and
    # spaced >= 6 (measured spacing -> 2 pi from below), single points optimal there.
    tail = 4.0 * (env * y) ** 2 * damage_scale * (1.0 / s_max ** 2 + 1.0 / (6.0 * s_max))
    deficit = 2.0 * (total + tail)          # both sides of the origin
    budget = 2.0 * shq(y)
    return WindowBound(y=y, width=width, kappa=kappa, q=q, windows=2 * len(wins),
                       deficit=deficit, tail=2.0 * tail, budget=budget,
                       bound_S=budget - deficit, bound_gap=(budget - deficit) / A2,
                       margin=budget / deficit if deficit > 0 else math.inf,
                       worst_window=worst)


# ---------------------------------------------------------------------------
# the same bound with exact rational constants, as a prover would state it
# ---------------------------------------------------------------------------

#: ``Wt`` of ``EForm3/FarField.lean``: ``Qim y s ^2 <= y^2 * Wt (s^2 - 2)`` for
#: ``|s| >= 28/5`` and ``y in [0,1/2]``.
def Wt(w):
    return F(5, 8) / w + F(611, 50) / w ** 2 + F(6711, 100) / w ** 3 + F(2583, 25) / w ** 4


#: ``Shq_half_lower`` of ``EForm3/Estimates.lean``, doubled: ``2 Shq y >= this * y^2``.
LEAN_BUDGET = F(51944, 100000)
#: a rational lower bound for ``K`` on ``|u| <= 1`` (true value 0.78066657).
KAPPA_NEAR = F(39, 50)
#: a rational lower bound for ``K`` on ``|u| <= 6`` (true value 0.00834800).
KAPPA_FAR = F(1, 125)


@dataclass
class RationalCertificate:
    windows: list                 # (lo, hi, cap/y^2) as Fractions
    near: F
    far: F
    tail: F
    deficit: F
    budget: F
    surplus: F
    margin: float
    gap_bound: float


def rational_certificate(s_far: int = 60, s_tail: int = 400, scan: float = 70.0,
                         step: float = 1e-4, kappa: F = KAPPA_NEAR,
                         kappa_far: F = KAPPA_FAR) -> RationalCertificate:
    """The bound of ``window_bound`` re-run in exact rational arithmetic.

    Window endpoints are widened and caps rounded up at the 8th decimal; the
    near price is ``kappa/200``, the far price ``kappa_far/200``; the far field
    is the width-6 partition of ``[s_far, inf)`` capped by ``Wt``, explicit to
    ``s_tail`` and closed-form beyond.  Everything after the table is exact, so
    ``surplus > 0`` is a statement about rationals.
    """
    q, q_far, v = kappa / 200, kappa_far / 200, F(1, 4)   # v = y^2 at y = 1/2
    table = []
    for w in damage_windows(0.5, s_max=scan, step=step):
        if w.hi > s_far:
            break
        table.append((F(math.floor(w.lo * 10 ** 4), 10 ** 4),
                      F(math.ceil(w.hi * 10 ** 4), 10 ** 4),
                      F(math.ceil(w.cap * 4 * 10 ** 8), 10 ** 8)))
    near = sum((F(integer_deficit_exact(c * v, q)[0]) for _, _, c in table), F(0))
    far, j = F(0), 0
    while F(s_far) + 6 * j < s_tail:
        cap = Wt((F(s_far) + 6 * j) ** 2 - 2) * v
        far += integer_deficit_exact(cap, q_far)[0]
        j += 1
    s = F(s_tail)
    tail = 4 * v * F(637, 1000) * (1 / (s ** 2 - 2) + F(1, 6) / (s - 2))
    deficit = 2 * (near + far + tail)
    budget = LEAN_BUDGET * v
    surplus = budget - deficit
    return RationalCertificate(
        windows=table, near=2 * near, far=2 * far, tail=2 * tail, deficit=deficit,
        budget=budget, surplus=surplus, margin=float(budget / deficit),
        gap_bound=float(surplus) / A2)


def integer_deficit_exact(cap: F, q: F):
    """``integer_deficit`` in exact rational arithmetic."""
    mstar = F(1, 2) + 2 * cap / q
    best, arg = F(0), 0
    for m in {0, 1, 2, math.floor(mstar), math.ceil(mstar)}:
        if m < 0:
            continue
        val = 4 * cap * m - q * m * (m - 1)
        if val > best:
            best, arg = val, m
    return best, arg


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------

CONFIGS = (
    ([0.0], 0.49, 3.2),
    ([0.0, 6.28], 0.3, 3.1),
    ([0.0, 3.1, 7.7, 11.2], 0.5, 5.5),
    ([0.0, 0.5, 1.0], 0.45, 6.5),
    ([0.0, 6.28, 12.57, 18.85, 25.13], 0.49, 9.4),
    ([6.5, 6.5, 6.5, 6.5], 0.5, 0.0),
    ([-6.517, 6.517, 12.72, -12.72], 0.5, 0.0),
    ([0.01, 0.02, 0.03, 0.04, 0.05, 0.06], 0.5, 6.517),
)


def identity_defects(configs=CONFIGS):
    """Worst disagreement between the three routes on each configuration."""
    out = []
    for xs, y, t in configs:
        a = gap_kernel(xs, y, t)
        b = gap_spectral(xs, y, t)
        c = gap_energy(xs, y, t)
        out.append((len(xs), a, max(abs(a - b), abs(a - c))))
    return out


def audit() -> None:  # pragma: no cover - console output
    print("= the gap by three routes (kernel / one-functional / two energies) =")
    for n, val, defect in identity_defects():
        print(f"  n={n}: gap = {val:+.9f}   worst defect {defect:.2e}")

    grid = np.arange(-20.0, 20.0001, 0.25)
    ev = gram_eigenvalues(grid)
    print(f"= the pair kernel = ")
    print(f"  Gram matrix on {len(grid)} points: min eigenvalue {ev.min():+.3e}, "
          f"max {ev.max():.4f}  (PSD: it is a square of a transform)")
    print(f"  pointwise minimum of K on [0, 40]: "
          f"{float(K(np.arange(0, 40, 1e-4)).min()):.3e}  (a square, so >= 0)")
    print(f"  worst increase of K on [0, 2 pi]: {kernel_is_decreasing():.3e} "
          f"(<= 0 means min over |u| <= w is K(w))")

    print("= the convex relaxation over nonnegative measures of mass n =")
    print(f"  {'n':>3} {'on a grid':>12} {'inf over R':>12} {'C*(n)':>12} "
          f"{'peak mass':>10} {'mass used':>10}")
    for n in (1, 2, 3, 5, 10, 20, 23, 40):
        r = relaxed_minimum(n, 0.5, half_width=45.0, step=0.1)
        val, cstar, masses, _ = relaxed_infimum(n, 0.5)
        print(f"  {n:>3} {r.value:>12.6f} {val:>12.6f} {cstar:>12.6f} "
              f"{masses.max():>10.5f} {masses.sum():>10.4f}")
    print("  'on a grid' is mass exactly n on a finite grid — a valid lower bound")
    print("  for on-grid configurations; 'inf over R' lets the excess mass leave as")
    print("  dust, which is what the relaxation is really worth.  From n = 6 it is")
    print("  the straight line 0.114022 - n/200: negative from n = 23, no floor.")
    print("  The minimiser has fractional peak mass, so it is not a configuration;")
    print("  and every convex relaxation of 'n unit atoms' contains these measures.")

    print("= the true minimum over n-point configurations, y = 1/2 =")
    for n in (1, 2, 3, 4, 6, 8, 12):
        v, x = atomic_minimum(n, 0.5, seed=n)
        print(f"  n={n:>3}: min gap = {v:+.6f}   support {np.round(x, 3)}")

    print("= the integrality-aware bound, uniform in n =")
    for y in (0.5, 0.4, 0.3, 0.2, 0.1):
        print("  " + str(window_bound(y)))
    print("  the bound never mentions n, so it holds for every n at once.")

    rc = rational_certificate()
    print("= the same bound in exact rationals, on Lean's constants =")
    print(f"  {len(rc.windows)} windows per side to s = 60, then the width-6 partition")
    print(f"  deficit {float(rc.deficit):.8e}  budget {float(rc.budget):.8e}  "
          f"surplus {float(rc.surplus):.8e}  margin {rc.margin:.4f}x")
    print(f"  gap >= {rc.gap_bound:.8f} for every n, every x, every t, at y = 1/2")
    print(f"  surplus is positive as an exact rational: {rc.surplus > 0}")


if __name__ == "__main__":  # pragma: no cover
    audit()
