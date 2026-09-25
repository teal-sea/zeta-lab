"""Delta_T in the Mellin variable: the consumption path for kernel/'s data.

Half-line picture of CC arXiv:2006.13771 (even functions, <f, g> =
int_0^inf conj(f) g dv, eq. (16)); Mellin transform on the critical line

    h^(s) := int_0^inf h(v) v^{-1/2 - is} dv,    ||h||^2 = (1/2pi) int |h^(s)|^2 ds.

The scaling theta(e^t) h(v) = e^{-t/2} h(v e^{-t}) becomes multiplication by
e^{-ist}, so theta(g) is multiplication by g^(s) = int g(t) e^{-ist} dt, and
for a projection Q onto span{w_i} with Gram matrix G_ij = <w_i, w_j>,

    Tr(theta(g) Q theta(g)^*) = (1/2pi) int |g^(s)|^2 rho_Q(s) ds,
    rho_Q(s) = sum_ij (G^{-1})_ij w_i^(s) conj(w_j^(s)).

For a mode xi on [0, 1] (kernel/'s xi_n, or a synthetic polynomial here),
zeta := (1 - P) F xi lives on v >= 1, and b := (1 - P) Theta^{*-1} zeta is

    b(v) = sum_{k >= 0} conj(alpha)^k (F xi)(2^k v),   v >= 1,
    b^(s) = sum_{k >= 0} r^k T(2^k; s),   r = conj(alpha) 2^{-1/2 + is},
    T(W; s) := int_W^inf (F xi)(w) w^{-1/2 - is} dw,   zeta^(s) = T(1; s).

T(W; s) is computed as a Gauss-Legendre sum over [W, W_max] (panels sized to
the local frequency 2 pi + |s|/w) plus an asymptotic tail beyond W_max from
the exact expansion (F xi)(w) = sum_m (-1)^m p^(m)(1) [e^{i om}/(i om)^{m+1}
+ e^{-i om}/(-i om)^{m+1}], om = 2 pi w (finite for a polynomial p; odd
derivatives at 0 drop out because p is even), each term integrated by the
asymptotic series of int_W^inf e^{i a w} w^beta dw. Float64 (numpy): every
output of this module is of measured grade.

Checks. test_ta_mellin.py pins zeta^ against Tate's local functional
equation, M[F xi](z) = 2 Gamma(z) cos(pi z/2) (2 pi)^{-z} M[xi](1-z), in
mpmath, for xi = (1 - y^2)^2. Run once and recorded in RESULTS.md s5b (too
slow for the suite, about 150 s): Plancherel for ||zeta||^2 (relative
6.7e-7 at S = 400) and ||theta(g) w||^2 / ||w||^2 against a direct v-domain
quadrature (2.7e-8 for zeta, 2.2e-7 for b). gram_v does not resolve the
dilates D^{-k} of b beyond k of about 3 (its ||b||^2 is off by 1.2e-3);
ta_prolate therefore takes Gram matrices on the s side.

rho (follow-up 3, 2026-09-24). Every Gram matrix here is G = F^* F for a
factor F of weighted samples (gram_factor_v; ta_prolate.gram_factor_s adds
two tail rows), so cond(G) = cond(F)^2. rho takes F, never forms G, and
solves against the R of a Householder QR of F: its arithmetic error grows
like eps cond(F). rho_inv is the route before 2026-09-24 (np.linalg.inv of
the formed G, error growing like eps cond(F)^2), kept as the reference.
Neither can do better than the samples: with a relative sample error delta,
the discretized projection is determined only while cond(F) delta << 1
(RESULTS.md s10).
"""

from __future__ import annotations

import math

import numpy as np
from scipy.linalg import solve_triangular

__all__ = [
    "EvenPoly",
    "w_nodes",
    "hats",
    "window_hat",
    "gram_v",
    "gram_factor_v",
    "rho",
    "rho_inv",
    "T_from_rho",
    "delta_T_mellin",
]

TWO_PI = 2.0 * math.pi


class EvenPoly:
    """p(y) = sum_j a_j y^{2j} on [0, 1] (an even function on [-1, 1])."""

    def __init__(self, a):
        self.a = [float(x) for x in a]
        c = np.zeros(2 * len(self.a) - 1)
        c[::2] = self.a
        self.poly = np.polynomial.Polynomial(c)
        deg = 2 * (len(self.a) - 1)
        q = self.poly
        self.derivs_at_1 = []
        for _ in range(deg + 1):
            self.derivs_at_1.append(float(q(1.0)))
            q = q.deriv()

    def F(self, w):
        """(F xi)(w) = 2 int_0^1 p(y) cos(2 pi w y) dy, exact IBP sum, w >= 1."""
        w = np.asarray(w, dtype=float)
        om = TWO_PI * w
        out = np.zeros_like(om, dtype=complex)
        e = np.exp(1j * om)
        for m, d in enumerate(self.derivs_at_1):
            if d == 0.0:
                continue
            out += (-1) ** m * d * (e / (1j * om) ** (m + 1) + np.conj(e) / (-1j * om) ** (m + 1))
        return out.real


def _asym_int(a: float, beta: np.ndarray, W: float, terms: int = 30) -> np.ndarray:
    """int_W^inf e^{i a w} w^beta dw ~ -e^{i a W} sum_j (-1)^j (beta)_j^down W^{beta-j} / (i a)^{j+1}."""
    tot = np.zeros_like(beta, dtype=complex)
    fall = np.ones_like(beta, dtype=complex)
    ia = 1j * a
    for j in range(terms):
        tot += (-1) ** j * fall * W ** (beta - j) / ia ** (j + 1)
        fall = fall * (beta - j)
    return -np.exp(ia * W) * tot


def _tail(xi: EvenPoly, W: float, s: np.ndarray) -> np.ndarray:
    """T(W; s) from the exact IBP expansion of F xi and the asymptotic series (W >> |s|)."""
    out = np.zeros_like(s, dtype=complex)
    for m, d in enumerate(xi.derivs_at_1):
        if d == 0.0:
            continue
        beta = -(m + 1) - 0.5 - 1j * s
        c = (-1) ** m * d * TWO_PI ** (-(m + 1))
        out += c * (1j ** (-(m + 1)) * _asym_int(TWO_PI, beta, W) + (-1j) ** (-(m + 1)) * _asym_int(-TWO_PI, beta, W))
    return out


def w_nodes(Kmax: int, s_max: float, per_panel: int = 12):
    """Gauss nodes on [1, 2^Kmax], panels about one local oscillation wide.

    Returns (w, weights, level) with level[i] = k such that w in [2^k, 2^{k+1}).
    """
    xg, wg = np.polynomial.legendre.leggauss(per_panel)
    ws, wts = [], []
    left = 1.0
    right_end = 2.0**Kmax
    while left < right_end:
        freq = TWO_PI + s_max / left
        h = min(TWO_PI / freq, right_end - left)
        mid, half = left + h / 2, h / 2
        ws.append(mid + half * xg)
        wts.append(half * wg)
        # never let a panel straddle a power of 2
        nxt = left + h
        p2 = 2.0 ** math.floor(math.log2(left) + 1e-12)
        if left < 2 * p2 < nxt:
            ws.pop()
            wts.pop()
            h = 2 * p2 - left
            mid, half = left + h / 2, h / 2
            ws.append(mid + half * xg)
            wts.append(half * wg)
            nxt = 2 * p2
        left = nxt
    w = np.concatenate(ws)
    wt = np.concatenate(wts)
    level = np.floor(np.log2(w)).astype(int)
    return w, wt, level


def hats(xi: EvenPoly, s: np.ndarray, alpha: complex, Kmax: int = 12, per_panel: int = 12, chunk: int = 256):
    """(zeta^(s), b^(s)) for the mode xi, over the array s."""
    s = np.asarray(s, dtype=float)
    smax = float(np.abs(s).max()) if s.size else 0.0
    w, wt, level = w_nodes(Kmax, smax, per_panel)
    Fw = xi.F(w) * wt
    logw = np.log(w)
    Wmax = 2.0**Kmax
    zeta_h = np.zeros(s.size, dtype=complex)
    b_h = np.zeros(s.size, dtype=complex)
    for i0 in range(0, s.size, chunk):
        ss = s[i0 : i0 + chunk]
        ph = np.exp(np.outer(-0.5 - 1j * ss, logw))  # (ns, nw)
        contrib = ph * Fw  # integrand samples times weights
        # partial integrals over dyadic levels [2^k, 2^{k+1})
        lev = np.stack([contrib[:, level == k].sum(axis=1) for k in range(Kmax)], axis=1)
        tailK = _tail(xi, Wmax, ss)
        # T(2^k) = tail + sum_{j >= k} lev_j
        Tk = np.cumsum(lev[:, ::-1], axis=1)[:, ::-1] + tailK[:, None]
        r = np.conj(alpha) * 2.0 ** (-0.5 + 1j * ss)
        rk = r[:, None] ** np.arange(Kmax)[None, :]
        bh = (rk * Tk).sum(axis=1)
        # k >= Kmax: T(2^k) from the asymptotic series directly
        k = Kmax
        rpow = r**Kmax
        while True:
            term = rpow * _tail(xi, 2.0**k, ss)
            bh += term
            if np.abs(term).max() < 1e-17 * max(1.0, np.abs(bh).max()) or k > Kmax + 80:
                break
            k += 1
            rpow = rpow * r
        zeta_h[i0 : i0 + chunk] = Tk[:, 0]
        b_h[i0 : i0 + chunk] = bh
    return zeta_h, b_h


def window_hat(L: float, N: int, s: np.ndarray) -> np.ndarray:
    """V_n^(s) = int_{-L/2}^{L/2} L^{-1/2} e^{2 pi i n (t + L/2)/L} e^{-ist} dt, rows n = -N..N."""
    s = np.asarray(s, dtype=float)
    ns = np.arange(-N, N + 1)[:, None]
    k = TWO_PI * ns / L - s[None, :]
    with np.errstate(divide="ignore", invalid="ignore"):
        val = np.exp(1j * s[None, :] * L / 2) * (np.exp(1j * k * L) - 1) / (1j * k)
    at = np.abs(k) < 1e-12
    val[at] = (np.exp(1j * s[None, :] * L / 2) * L * np.ones_like(k))[at]
    return val / math.sqrt(L)


def gram_v(fns, Kmax: int = 14, per_panel: int = 12, tail_terms=None):
    """G_ij = int_1^inf conj(f_i) f_j dv by Gauss panels on [1, 2^Kmax] (tail neglected).

    fns: callables of a float array v >= 1. The neglected tail is bounded by
    the caller (for (1 - y^2)^2, |F xi| <= C v^-3, so it is below 1e-20 at Kmax = 14).
    """
    F = gram_factor_v(fns, Kmax, per_panel)
    return np.conj(F.T) @ F


def gram_factor_v(fns, Kmax: int = 14, per_panel: int = 12) -> np.ndarray:
    """F with gram_v(fns) = F^* F: rows sqrt(weight) f_j(w) on gram_v's nodes."""
    w, wt, _ = w_nodes(Kmax, 0.0, per_panel)
    V = np.stack([f(w) for f in fns])
    return (V * np.sqrt(wt)).T


def rho(hat_rows: np.ndarray, *, factor: np.ndarray) -> np.ndarray:
    """rho_Q(s) = sum_ij (G^{-1})_ij w_i^(s) conj(w_j^(s)) for G = F^* F, without forming G.

    factor: F, shape (m, n) with m >= n and G = F^* F (gram_factor_v, or
    ta_prolate.gram_factor_s). With G = R^* R from a Householder QR of F,
    rho(s) = ||y(s)||^2 where R^* y(s) = conj(w^(s)), a triangular solve.
    Keyword-only on purpose: a Gram matrix passed where F is expected would
    otherwise be accepted silently. Raises LinAlgError if R is exactly singular.
    """
    R = np.linalg.qr(np.asarray(factor), mode="r")
    Y = solve_triangular(R, np.conj(hat_rows), trans="C", lower=False, check_finite=False)
    return np.sum(np.abs(Y) ** 2, axis=0)


def rho_inv(hat_rows: np.ndarray, G: np.ndarray) -> np.ndarray:
    """The route before 2026-09-24, kept as the reference: np.linalg.inv of the formed G."""
    Gi = np.linalg.inv(G)
    return np.real(np.einsum("is,ij,js->s", hat_rows, Gi, np.conj(hat_rows)))


def T_from_rho(rho_s: np.ndarray, s: np.ndarray, ds_w: np.ndarray, L: float, N: int) -> np.ndarray:
    """M_mn = (1/2pi) int rho(s) conj(V_m^(s)) V_n^(s) ds (quadrature weights ds_w)."""
    V = window_hat(L, N, s)
    return (np.conj(V) * (rho_s * ds_w)) @ V.T / TWO_PI


def s_grid(S: float, width: float = 2.0, per_panel: int = 8):
    """Gauss-Legendre panels on [-S, S]."""
    xg, wg = np.polynomial.legendre.leggauss(per_panel)
    edges = np.arange(-S, S + 1e-12, width)
    s = (edges[:-1, None] + width / 2 + width / 2 * xg[None, :]).ravel()
    w = np.tile(width / 2 * wg, edges.size - 1)
    return s, w


def delta_T_mellin(xis, alpha: complex, L: float, N: int, S: float = 400.0, Kmax: int = 12):
    """(Delta_T, M_inf, M_S) for a finite family of modes xi (EvenPoly), Mellin route."""
    s, sw = s_grid(S)
    Z, B = [], []
    for xi in xis:
        zh, bh = hats(xi, s, alpha, Kmax)
        Z.append(zh)
        B.append(bh)
    Z, B = np.array(Z), np.array(B)
    zf = [lambda v, xi=xi: xi.F(v) for xi in xis]
    bf = [lambda v, xi=xi: b_values(xi, v, alpha) for xi in xis]
    M_inf = T_from_rho(rho(Z, factor=gram_factor_v(zf)), s, sw, L, N)
    M_S = T_from_rho(rho(B, factor=gram_factor_v(bf)), s, sw, L, N)
    return M_inf - M_S, M_inf, M_S


def b_values(xi: EvenPoly, v: np.ndarray, alpha: complex, kmax: int = 80) -> np.ndarray:
    """b(v) = sum_k conj(alpha)^k (F xi)(2^k v) for v >= 1."""
    v = np.asarray(v, dtype=float)
    out = np.zeros_like(v, dtype=complex)
    ac = np.conj(alpha)
    for k in range(kmax + 1):
        out += ac**k * xi.F(2.0**k * v)
    return out
