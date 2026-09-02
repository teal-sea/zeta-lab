"""Shared machinery for ARM A-PRIME: the T1 Cohn-Elkies-style certificate LP.

Everything the probe needs, kept in one importable module so the probe script
and the a-posteriori verifier share exactly one implementation of `f`.

Conventions (taken from the brief, cross-checked against
`hunts/frontier_math/gram_form.py`):

    ghat(z) = int_{-1/2}^{1/2} cos(sqrt2 t) e^{zt} dt
            = sinh((z+i r)/2)/(z+i r) + sinh((z-i r)/2)/(z-i r),  r = sqrt(2)

    Kpair(s) = [Re ghat(i s)]^2      (this is gram_form.phi_r(s)**2)
    D(s)     = -Re[ghat(1 + i s)^2]  (this is gram_form.damage(1.0, s))
    f(s)     = max(0, D(s)) - Kpair(s)

The certificate class is `G(s) = -int_0^inf mu(w) cos(s w) dw` with `mu >= 0`;
the route's value is `V = int mu = -G(0)`.
"""

from __future__ import annotations

import math

import numpy as np

R2 = math.sqrt(2.0)
C_W = math.cos(1.0 / R2)          # cos(sqrt2/2), the window constant
A_CONST = R2 * math.sin(1.0 / R2)  # = ghat(0)
Q_ASY = 2.0 * C_W ** 2
P_ASY = Q_ASY * math.cosh(1.0)

SHQ_HALF = 0.06750840786062762     # Shq(1/2): the route works iff V < this
LATTICE_FLOOR = 0.05716501969327026  # forced lower bound on V


# --------------------------------------------------------------------------
# f and its asymptotic envelope
# --------------------------------------------------------------------------

def _sinh_over(z):
    """sinh(z/2)/z, stable through z = 0 (removable)."""
    z = np.asarray(z, dtype=complex)
    small = np.abs(z) < 1e-6
    out = np.empty_like(z)
    zs = np.where(small, 1.0, z)
    out = np.sinh(zs / 2.0) / zs
    # series: sinh(z/2)/z = 1/2 + z^2/48 + z^4/3840
    ser = 0.5 + z ** 2 / 48.0 + z ** 4 / 3840.0
    return np.where(small, ser, out)


def ghat(z):
    """ghat(z) for complex array z."""
    z = np.asarray(z, dtype=complex)
    return _sinh_over(z + 1j * R2) + _sinh_over(z - 1j * R2)


def phi_r(s):
    """Re ghat(i s) -- real, even, ~ 2 C_W sin(s/2)/s."""
    return np.real(ghat(1j * np.asarray(s, dtype=float)))


def kpair(s):
    return phi_r(s) ** 2


def damage1(s):
    """D(s) = -Re[ghat(1 + i s)^2]."""
    g = ghat(1.0 + 1j * np.asarray(s, dtype=float))
    return -np.real(g * g)


def f_target(s):
    """f(s) = max(0, D(s)) - Kpair(s)."""
    return np.maximum(0.0, damage1(s)) - kpair(s)


def F_env(theta):
    """The 2*pi-periodic limit of s^2 f(s)."""
    c = np.cos(np.asarray(theta, dtype=float))
    return np.maximum(0.0, P_ASY * c - Q_ASY) - Q_ASY * (1.0 - c)


def s2f(s):
    s = np.asarray(s, dtype=float)
    return s * s * f_target(s)


# --------------------------------------------------------------------------
# the achievability floor, recomputed independently
# --------------------------------------------------------------------------

def gas_row(lam, dmax=400000):
    """2 * sum_{d>=1} f(lam d): the gas row of the uniform lattice of gap lam."""
    d = np.arange(1, dmax + 1, dtype=float)
    return 2.0 * float(np.sum(f_target(lam * d)))


# --------------------------------------------------------------------------
# the certificate class
# --------------------------------------------------------------------------
# mu is C^0 on [0, W], supported there, mu(W) = 0, piecewise quadratic on a
# uniform fine grid of step h = 1/K, with slope jumps allowed ONLY at the
# integers 1..W.  Then, exactly (two integrations by parts),
#
#     s^2 G(s) = Pi(s) + R(s)/s,
#     Pi(s)    = d0 + sum_{j=1}^{W} kappa_j cos(j s),          (2*pi-periodic)
#     R(s)     = sum_l psi_l [ sin(s b_{l+1}) - sin(s b_l) ],  (|R| bounded)
#
# with d0 = mu'(0+), kappa_j the slope jump at the integer j (kappa_W being the
# drop to slope 0 at the right endpoint), psi_l = mu'' on cell l, b_l = l h.
#
# Free LP variables:  x = [mu_0, d_0, psi_0..psi_{N-1}, kappa_1..kappa_{W-1}]
# with kappa_W determined by the state and mu(W) = 0 imposed as an equality.


class Klass:
    def __init__(self, W: int, K: int):
        self.W, self.K = W, K
        self.h = 1.0 / K
        self.N = W * K
        self.nvar = 2 + self.N + (W - 1)
        self.i_mu0, self.i_d0 = 0, 1
        self.i_psi = 2
        self.i_kap = 2 + self.N
        self._build()

    # -- forward integration, as linear maps on x ---------------------------
    def _build(self):
        h, N, K, W = self.h, self.N, self.K, self.W
        nv = self.nvar
        mu = np.zeros((N + 1, nv))      # mu at knot l
        d = np.zeros((N + 1, nv))       # mu'(knot l, from the right)
        mu[0, self.i_mu0] = 1.0
        d[0, self.i_d0] = 1.0
        for l in range(N):
            mu[l + 1] = mu[l] + h * d[l]
            mu[l + 1, self.i_psi + l] += h * h / 2.0
            d[l + 1] = d[l]
            d[l + 1, self.i_psi + l] += h
            b = (l + 1) * h
            if abs(b - round(b)) < 1e-12 and 1 <= round(b) <= W - 1:
                d[l + 1, self.i_kap + int(round(b)) - 1] += 1.0
        self.mu_knot, self.d_knot = mu, d
        # midpoint values, for the nonnegativity constraints
        mid = np.zeros((N, nv))
        for l in range(N):
            mid[l] = mu[l] + (h / 2.0) * d[l]
            mid[l, self.i_psi + l] += (h / 2.0) ** 2 / 2.0
        self.mu_mid = mid
        # objective V = int mu
        obj = np.zeros(nv)
        for l in range(N):
            obj += h * mu[l] + h * h / 2.0 * d[l]
            obj[self.i_psi + l] += h ** 3 / 6.0
        self.obj = obj
        # kappa_W = -mu'(W^-)
        self.kapW = -d[N]
        self.endval = mu[N]              # must be 0

    # -- Pi and R as linear maps -------------------------------------------
    def Pi_rows(self, s):
        """rows A with Pi(s) = A @ x."""
        s = np.atleast_1d(np.asarray(s, dtype=float))
        A = np.zeros((s.size, self.nvar))
        A[:, self.i_d0] = 1.0
        for j in range(1, self.W):
            A[:, self.i_kap + j - 1] = np.cos(j * s)
        A += np.cos(self.W * s)[:, None] * self.kapW[None, :]
        return A

    def R_rows(self, s):
        s = np.atleast_1d(np.asarray(s, dtype=float))
        A = np.zeros((s.size, self.nvar))
        b = np.arange(self.N + 1) * self.h
        sn = np.sin(np.outer(s, b))
        A[:, self.i_psi:self.i_psi + self.N] = sn[:, 1:] - sn[:, :-1]
        return A

    def G_rows(self, s):
        """rows A with s^2 G(s) = A @ x (exact)."""
        s = np.atleast_1d(np.asarray(s, dtype=float))
        return self.Pi_rows(s) + self.R_rows(s) / s[:, None]

    # -- evaluation for a concrete solution ---------------------------------
    def s2G(self, x, s):
        return self.G_rows(s) @ x

    def G(self, x, s):
        s = np.asarray(s, dtype=float)
        return self.s2G(x, s) / (s * s)

    def Pi(self, x, theta):
        return self.Pi_rows(theta) @ x

    def R(self, x, s):
        return self.R_rows(s) @ x

    def mu_of(self, x):
        return self.mu_knot @ x, self.d_knot @ x, x[self.i_psi:self.i_psi + self.N]

    def value(self, x):
        return float(self.obj @ x)
