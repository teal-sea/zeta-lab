"""Delta_T = T_S - T_inf from kernel/'s S_inf data, Mellin route (float64, measured grade).

Consumes kernel/ read-only through its INTERFACE.md s3 (routed by the
coordinator 2026-09-23): S_inf = 1_{u >= 1} - sum_n |z_n><z_n| on
L^2(R*_+, d*u), z_n = u^{1/2} eta_n(u) 1_{u >= 1} / sqrt(1 - lam_n^2),
eta_n = F xi_n = sum_i coef[n][i] 2 (-1)^{k_i/2} j_{k_i}(2 pi u) (kernel's
eta_all, here in float64 via scipy's spherical Bessel functions).

With zeta_n := z_n (half-line picture) and b_n := (1 - P) Theta^{*-1} zeta_n
(ta_ts.py docstring), Q_inf and Q_S are the projections onto the spans of
the first nvec of each, and

    Delta_T = (1/2pi) int (rho_inf(s) - rho_S(s)) conj(V_m^(s)) V_n^(s) ds,

rho from the Mellin transforms and Gram matrices (ta_mellin.rho). Gram
matrices are taken on the same s-quadrature as rho (Plancherel), with the
leading jump tail 2 J_i J_j / S added (J = value at u = 1+), so that each
rho is the density of an actual projection in the discretized inner product.
Since 2026-09-24 (RESULTS.md s10) rho receives the factor F of that Gram
matrix (gram_factor_s, G = F^* F) and never forms G; delta_T_cells reports
cond(F) for both families, since that Gram's condition is set by the cutoff
S against nvec^2 (not by the functions: G_z = I exactly), and a build whose
cond(F) times the samples' relative error is not small is not determined
by its samples.
Truncations: nvec modes, s in [-S, S], w in [1, 2^Kmax] plus asymptotic
tails, Kmax from kmax_for(nvec) (guarded); nvec and S are varied in
RESULTS s5b and the spread is the error bar.
"""

from __future__ import annotations

import math
import os
import sys

import numpy as np
from mpmath import mp
from scipy.special import spherical_jn

HERE = os.path.dirname(os.path.abspath(__file__))
KERNEL = os.path.normpath(os.path.join(HERE, "..", "kernel"))
for p in (HERE, KERNEL):
    if p not in sys.path:
        sys.path.insert(0, p)

import sonin  # noqa: E402  (kernel/, read-only)
import ta_mellin as TM  # noqa: E402

TWO_PI = 2.0 * math.pi


class ProlateModes:
    """kernel/'s even prolate data as float64 arrays."""

    def __init__(self, nvec: int = 120, dps: int = 20, mderiv: int = 14):
        pv = sonin.prolate_vectors(dps, 0, nvec)
        pd = sonin.prolate_data(dps, 0)
        self.nvec = nvec
        self.ks = np.array(pv["ks"], dtype=int)
        self.coef = np.array([[float(x) for x in c] for c in pv["coef"]])
        lam = [float(x) for x in pd["lam"]]
        lam = lam + [0.0] * (nvec - len(lam))
        self.lam = np.array(lam[:nvec])
        self.norm = 1.0 / np.sqrt(1.0 - self.lam**2)
        # derivatives of phi~_n at y = 1 from P_k^(m)(1) = (k+m)!/(2^m m! (k-m)!)
        with mp.workdps(dps + 20):
            D = np.zeros((nvec, mderiv + 1))
            for m in range(mderiv + 1):
                pk = [mp.factorial(k + m) / (2**m * mp.factorial(m) * mp.factorial(k - m)) if k >= m else mp.mpf(0) for k in pv["ks"]]
                for n in range(nvec):
                    D[n, m] = float(mp.fsum(cf * p for cf, p in zip(pv["coef"][n], pk)))
        self.derivs = D  # phi~_n^(m)(1)

    def zeta(self, w):
        """zeta_n(w) = eta_n(w) / sqrt(1 - lam_n^2), rows n, for w >= 1."""
        x = TWO_PI * np.asarray(w, dtype=float)
        sgn = 2.0 * (-1.0) ** (self.ks // 2)
        J = np.stack([spherical_jn(int(k), x) for k in self.ks])
        return (self.coef @ (sgn[:, None] * J)) * self.norm[:, None]


def _tail_modes(pm: ProlateModes, W: float, s: np.ndarray, mmax: int, terms: int) -> np.ndarray:
    """T_n(W; s) = int_W^inf zeta_n(w) w^{-1/2-is} dw, asymptotic, shape (ns, nvec)."""
    out = np.zeros((s.size, pm.nvec), dtype=complex)
    for m in range(mmax + 1):
        d = pm.derivs[:, m] * pm.norm
        if not np.any(d):
            continue
        beta = -(m + 1) - 0.5 - 1j * s
        c = (-1) ** m * TWO_PI ** (-(m + 1))
        g = c * (1j ** (-(m + 1)) * TM._asym_int(TWO_PI, beta, W, terms) + (-1j) ** (-(m + 1)) * TM._asym_int(-TWO_PI, beta, W, terms))
        out += g[:, None] * d[None, :]
    return out


def kmax_for(nvec: int) -> int:
    """Smallest Kmax >= 10 with 2^Kmax >= n_max^2 / (2 pi).

    The tail series in 1/w built from phi~_n^(m)(1) has term ratio about
    (2n)^2 / (4 pi (m+1) W) (phi~_n is close to sqrt(4n+1) P_2n); at
    W = 2^10 and n = 199 its terms grow to 1e4 times the first before
    turning, and a 15-term truncation returns O(1) garbage. The rule keeps
    the ratio below 2/(m+1).
    """
    return max(10, int(math.ceil(math.log2(max(nvec - 1, 1) ** 2 / (2 * math.pi)))))


def hats_modes(pm: ProlateModes, s: np.ndarray, alpha: float = 1.0, Kmax: int | None = None, per_panel: int = 12, chunk: int = 128):
    """(zeta^_n(s), b^_n(s)) for all modes, arrays (nvec, ns)."""
    if Kmax is None:
        Kmax = kmax_for(pm.nvec)
    if (2 * (pm.nvec - 1)) ** 2 / (4 * math.pi * 2.0**Kmax) > 2.0:
        raise ValueError(f"Kmax = {Kmax} too small for {pm.nvec} modes: the asymptotic tail diverges; use kmax_for(nvec)")
    s = np.asarray(s, dtype=float)
    w, wt, level = TM.w_nodes(Kmax, float(np.abs(s).max()), per_panel)
    Fw = pm.zeta(w) * wt[None, :]  # (nvec, nw)
    logw = np.log(w)
    idx = [np.where(level == k)[0] for k in range(Kmax)]
    Wmax = 2.0**Kmax
    Z = np.zeros((pm.nvec, s.size), dtype=complex)
    B = np.zeros((pm.nvec, s.size), dtype=complex)
    for i0 in range(0, s.size, chunk):
        ss = s[i0 : i0 + chunk]
        ph = np.exp(np.outer(-0.5 - 1j * ss, logw))
        lev = np.stack([ph[:, ik] @ Fw[:, ik].T for ik in idx], axis=2)  # (ns, nvec, Kmax)
        tail = _tail_modes(pm, Wmax, ss, mmax=pm.derivs.shape[1] - 1, terms=25)
        Tk = np.cumsum(lev[:, :, ::-1], axis=2)[:, :, ::-1] + tail[:, :, None]
        r = alpha * 2.0 ** (-0.5 + 1j * ss)
        rk = r[:, None] ** np.arange(Kmax)[None, :]
        bh = np.einsum("sk,snk->sn", rk, Tk)
        k, rpow = Kmax, r**Kmax
        while k < Kmax + 70:
            term = rpow[:, None] * _tail_modes(pm, 2.0**k, ss, mmax=4, terms=8)
            bh += term
            if np.abs(term).max() < 1e-18:
                break
            k += 1
            rpow = rpow * r
        Z[:, i0 : i0 + chunk] = Tk[:, :, 0].T
        B[:, i0 : i0 + chunk] = bh.T
    return Z, B


def jumps(pm: ProlateModes, alpha: float = 1.0, kmax: int = 70):
    """(zeta_n(1+), b_n(1+) = sum_k alpha^k zeta_n(2^k))."""
    ws = 2.0 ** np.arange(kmax + 1)
    Zw = pm.zeta(ws)  # (nvec, kmax+1)
    return Zw[:, 0], Zw @ (alpha ** np.arange(kmax + 1))


def gram_s(H: np.ndarray, sw: np.ndarray, J: np.ndarray, S: float, A: np.ndarray, dil: float) -> np.ndarray:
    """G_ij = (1/2pi) sum_s w_s conj(H_i) H_j + (J_i J_j + dil A_i A_j) / (pi S).

    The two tails beyond |s| = S at order 1/S: the jump J at u = 1
    (|h^(s)|^2 ~ J^2 / s^2) and the oscillation A sin(2 pi v)/(pi v) at large
    v, whose Mellin energy beyond S is the energy of h on v > S/(2 pi),
    A^2/(pi S); for b the dilates k contribute 2^-k of it each (dil = 2 for
    alpha = 1, dil = 1 for zeta).
    """
    return (np.conj(H) * sw) @ H.T / TWO_PI + (np.outer(J, J) + dil * np.outer(A, A)) / (math.pi * S)


def gram_factor_s(H: np.ndarray, sw: np.ndarray, J: np.ndarray, S: float, A: np.ndarray, dil: float) -> np.ndarray:
    """F with gram_s(H, sw, J, S, A, dil) = F^* F: the weighted samples and the two tail rows."""
    return np.vstack([(H * np.sqrt(sw / TWO_PI)).T, math.sqrt(1.0 / (math.pi * S)) * np.asarray(J, dtype=complex)[None, :],
                      math.sqrt(dil / (math.pi * S)) * np.asarray(A, dtype=complex)[None, :]])


def delta_T_cells(pm: ProlateModes, cells, N: int, S: float = 300.0, alpha: float = 1.0, Kmax: int | None = None, width: float = 1.0, per_panel: int = 8):
    """{c: (Delta_T, M_inf, M_S)} on the shared basis for each c in cells, plus diagnostics."""
    s, sw = TM.s_grid(S, width=width, per_panel=per_panel)
    Z, B = hats_modes(pm, s, alpha, Kmax)
    jz, jb = jumps(pm, alpha)
    A = pm.derivs[:, 0] * pm.norm
    dil_b = 1.0 / (1.0 - abs(alpha) ** 2 / 2.0)
    Fz = gram_factor_s(Z, sw, jz, S, A, 1.0)
    Fb = gram_factor_s(B, sw, jb, S, A, dil_b)
    Gz, Gb = np.conj(Fz.T) @ Fz, np.conj(Fb.T) @ Fb
    rz = TM.rho(Z, factor=Fz)
    rb = TM.rho(B, factor=Fb)
    out = {}
    for c in cells:
        L = math.log(float(c))
        Mi = TM.T_from_rho(rz, s, sw, L, N)
        Ms = TM.T_from_rho(rb, s, sw, L, N)
        out[c] = (Mi - Ms, Mi, Ms)
    sz, sb = (np.linalg.svd(F, compute_uv=False) for F in (Fz, Fb))
    diag = {"gram_z_offI": float(np.abs(Gz - np.eye(pm.nvec)).max()), "cond_Gb": float(np.linalg.cond(Gb)),
            "cond_Fz": float(sz[0] / sz[-1]), "cond_Fb": float(sb[0] / sb[-1])}
    return out, diag
