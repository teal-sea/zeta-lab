"""The certificate class for the T1 Cohn-Elkies-style LP, and its exact transform.

The route (`hunts/r_b9552d/RESULTS-37fb06a9.md` §5).  With

    ghat(z) = int_{-1/2}^{1/2} cos(sqrt2 t) e^{zt} dt,
    Kpair(s) = [Re ghat(i s)]^2,   D(s) = -Re[ghat(1 + i s)^2],
    f(s)     = max(0, D(s)) - Kpair(s),

a certificate is a `G` with `G >= f` off the origin and `Ghat <= 0`.  Writing
`G(s) = - int_0^W mu(w) cos(s w) dw` with `mu >= 0` makes `Ghat <= 0`
structural and `-G(0) = int mu`, so the route's value is

    V = min int mu   s.t.   G(s) >= f(s)  for all s > 0,

and T1 follows for every `k` at once as soon as a feasible `mu` has
`int mu < Shq(1/2) = 0.06750840786062762`.

**Why the measure class is the whole problem.**  Integrating by parts twice,
for `mu` supported on `[0, W]` with `mu(W) = mu'(W) = 0`,

    G(s) = [ mu'(0+) - int mu''(w) cos(s w) dw ] / s^2.

`f` decays like `1/s^2` with a positive `2*pi`-periodic envelope, so a
certificate has to hold a *positive* `1/s^2` floor.  That floor is
`mu'(0+)/s^2`, and it survives only if `int mu'' cos` decays.  Therefore:

* a piecewise-**constant** `mu` (run `37fb06a9`'s class) has `G = O(1/s)`
  with an almost-periodic, sign-changing numerator: it is infeasible at large
  `s` no matter how the grid is refined, which is a property of the class and
  not of the solver;
* a piecewise-**linear** `mu` has `s^2 G(s)` almost-periodic and again
  sign-changing;
* a piecewise-**cubic** `mu` that is `C^2` away from the origin has, exactly,

      G(s) = mu'(0+)/s^2 - Theta(s) / (2 s^4),
      Theta(s) = 2 mu'''(0+) + 2 sum_k J_k cos(s v_k),

  with `J_k` the jump of `mu'''` at knot `v_k`.  The leading term is a
  positive constant over `s^2`, so the class can hold the floor, and the
  correction is `O(1/s^4)` with an explicitly bounded numerator.  That is the
  class used here.

Both identities above are exact, not asymptotic, and both are checked against
adaptive quadrature by :func:`transform_residual`.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np

SQ2 = math.sqrt(2.0)

#: `Shq(1/2)`, the per-centre budget T1 must fit inside.
SHQ_HALF = 0.06750840786062762
#: the achievability floor: the uniform `2*pi` lattice's gas row, `L/2`.
LATTICE_ROW = 0.05716501969327026
#: `4 cos^2(sqrt2/2) sinh^2(1/2)`, the limsup of `s^2 f(s)` (derived below).
TAIL_ENVELOPE = 4.0 * math.cos(SQ2 / 2.0) ** 2 * math.sinh(0.5) ** 2


def TAIL_ENVELOPE_AT(twoy: float = 1.0) -> float:
    """`limsup s^2 f(s)` at depth `2y = twoy`: `4 cos^2(sqrt2/2) sinh^2(y)`.

    From `ghat(2y + i s) = (2 cos(sqrt2/2)/(i s))[sinh(y) cos(s/2)
    + i cosh(y) sin(s/2)] + O(1/s^2)`, so `s^2 Dam -> 4 cos^2(sqrt2/2)
    max(0, sinh^2(y) cos^2(s/2) - cosh^2(y) sin^2(s/2))`, maximised at
    `s in 2*pi*Z` where the `Kpair` term vanishes.
    """
    return 4.0 * math.cos(SQ2 / 2.0) ** 2 * math.sinh(twoy / 2.0) ** 2


# -- the kernel -------------------------------------------------------------

def ghat(z: np.ndarray) -> np.ndarray:
    """`int_{-1/2}^{1/2} cos(sqrt2 t) e^{zt} dt`, vectorized over complex `z`."""
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return np.sinh(zp / 2.0) / zp + np.sinh(zm / 2.0) / zm


def kpair(s: np.ndarray) -> np.ndarray:
    s = np.asarray(s, dtype=float)
    return ghat(1j * s).real ** 2


def damage(s: np.ndarray, twoy: float = 1.0) -> np.ndarray:
    s = np.asarray(s, dtype=float)
    g = ghat(twoy + 1j * s)
    return -(g * g).real


def f_gas(s: np.ndarray, twoy: float = 1.0) -> np.ndarray:
    """`f(s) = Dam(2y, s) - Kpair(s)`, the per-pair gas charge."""
    return np.maximum(0.0, damage(s, twoy)) - kpair(s)


def f_envelope(s: np.ndarray) -> np.ndarray:
    """The leading term of `s^2 f(s)` at large `s`, derived in closed form.

    `ghat(1 + i s) = (2 cos(sqrt2/2)/(i s))[sinh(1/2) cos(s/2)
    + i cosh(1/2) sin(s/2)] + O(1/s^2)` and `Re ghat(i s) = (2 cos(sqrt2/2)/s)
    sin(s/2) + O(1/s^2)`, whence

        s^2 f(s) -> 4 cos^2(sqrt2/2) [ max(0, sinh^2(1/2) cos^2(s/2)
                                           - cosh^2(1/2) sin^2(s/2))
                                       - sin^2(s/2) ],

    which is `2*pi`-periodic with its maximum `4 cos^2(sqrt2/2) sinh^2(1/2)`
    exactly at `s in 2*pi*Z` -- the critical lattice.
    """
    s = np.asarray(s, dtype=float)
    c2 = math.cos(SQ2 / 2.0) ** 2
    co, si = np.cos(s / 2.0) ** 2, np.sin(s / 2.0) ** 2
    d = math.sinh(0.5) ** 2 * co - math.cosh(0.5) ** 2 * si
    return 4.0 * c2 * (np.maximum(0.0, d) - si)


# -- the measure class ------------------------------------------------------

@dataclass
class CubicBasis:
    """Nonnegative cubic B-spline basis on `[0, W]`, clamped left, flat right.

    `mu = sum_j x_j B_j` with `x_j >= 0` is nonnegative because every `B_j`
    is.  The last two basis functions are dropped so that every `mu` in the
    class has `mu(W) = mu'(W) = 0`; the left end is clamped, so `mu(0)` and
    `mu'(0+)` are free -- and `mu'(0+)` is exactly the quantity the tail of
    the certificate needs to be large.
    """

    W: float
    n_int: int

    def __post_init__(self) -> None:
        from scipy.interpolate import BSpline
        self.v = np.linspace(0.0, self.W, self.n_int + 1)          # breakpoints
        t = np.concatenate([[0.0] * 3, self.v, [self.W] * 3])      # clamped knots
        self.t = t
        n_full = len(t) - 4
        # Drop the last three: every `mu` in the class then has
        # `mu(W) = mu'(W) = mu''(W) = 0`, so the even extension is `C^2` at
        # `+/- W` and the transform identity below carries no endpoint term.
        self.n = n_full - 3
        eye = np.eye(n_full)
        self.splines = [BSpline(t, eye[j], 3, extrapolate=False)
                        for j in range(self.n)]
        # exact integrals (2-point Gauss is exact for cubics)
        g = 1.0 / math.sqrt(3.0)
        mid = 0.5 * (self.v[:-1] + self.v[1:])
        half = 0.5 * np.diff(self.v)
        nodes = np.concatenate([mid - half * g, mid + half * g])
        wts = np.concatenate([half, half])
        self.mass = np.array([float(np.dot(wts, np.nan_to_num(sp(nodes))))
                              for sp in self.splines])
        # derivative at 0+
        self.d1_zero = np.array([float(sp.derivative(1)(1e-13))
                                 for sp in self.splines])
        # third derivative: piecewise constant, sampled at interval midpoints
        d3 = np.array([np.nan_to_num(sp.derivative(3)(mid))
                       for sp in self.splines])                    # (n, n_int)
        # jumps of mu''' at v_0=0 (using the even extension), v_1..v_{n_int}
        jump = np.zeros((self.n, self.n_int + 1))
        jump[:, 0] = 2.0 * d3[:, 0]                 # even extension: 2*mu'''(0+)
        jump[:, 1:-1] = d3[:, 1:] - d3[:, :-1]
        jump[:, -1] = -d3[:, -1]                    # mu''' drops to 0 past W
        self.jump = jump

    def theta(self, s: np.ndarray) -> np.ndarray:
        """`Theta_j(s)`: shape `(len(s), n)`.  `Theta(s) = sum_j x_j Theta_j`."""
        s = np.atleast_1d(np.asarray(s, dtype=float))
        cos = np.cos(np.outer(s, self.v))                          # (S, n_int+1)
        out = 2.0 * cos @ self.jump.T                              # (S, n)
        out -= self.jump[:, 0][None, :]     # v_0 = 0 is counted once, not twice
        return out

    def G_matrix(self, s: np.ndarray) -> np.ndarray:
        """`G(s_i) = (Phi @ x)_i`, exactly, for every `s_i != 0`."""
        s = np.atleast_1d(np.asarray(s, dtype=float))
        return (self.d1_zero[None, :] / s[:, None] ** 2
                - self.theta(s) / (2.0 * s[:, None] ** 4))

    def s2G_matrix(self, s: np.ndarray) -> np.ndarray:
        """`s^2 G(s_i)`: the same rows scaled to `O(1)` entries."""
        s = np.atleast_1d(np.asarray(s, dtype=float))
        return self.d1_zero[None, :] - self.theta(s) / (2.0 * s[:, None] ** 2)

    def mu(self, x: np.ndarray, w: np.ndarray) -> np.ndarray:
        w = np.clip(np.asarray(w, dtype=float), 0.0, self.W)
        return sum(x[j] * np.nan_to_num(self.splines[j](w))
                   for j in range(self.n))

    def theta_bound(self, x: np.ndarray) -> float:
        """`sup_s |Theta(s)|` from the coefficients: the tail's only unknown."""
        j = self.jump.T @ x                       # jumps of mu''' at each v_k
        return float(2.0 * np.sum(np.abs(j)) - abs(j[0]))


def transform_residual(basis: CubicBasis, x: np.ndarray,
                       s_test=(0.7, 2.0, 6.283185307179586, 13.0, 41.0,
                               97.3, 311.7)) -> float:
    """Control: the exact `G` against adaptive quadrature of its definition."""
    from scipy.integrate import quad
    worst = 0.0
    for s in s_test:
        num = -quad(lambda w: float(basis.mu(x, np.array([w]))[0])
                    * math.cos(s * w), 0.0, basis.W,
                    limit=400, epsabs=1e-13, epsrel=1e-13)[0]
        exact = float((basis.G_matrix(np.array([s])) @ x)[0])
        worst = max(worst, abs(num - exact))
    return worst
