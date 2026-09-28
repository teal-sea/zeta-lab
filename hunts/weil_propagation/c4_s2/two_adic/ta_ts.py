"""Assembly of T_S for S = {inf, 2} on the module/quotient form.

The object (coordinator decision on milestone 1; CCM arXiv:2310.18423 s4):
on L^2(X_S)^{K_S} = L^2(R*_+, d*u), written in the log variable x = log u
(so the scaling action is translation, T_t b(x) = b(x - t)),

    Pi_S := orthogonal projection onto Theta(range S_inf),
    Theta = prod_j (1 - alpha_j 2^{-1/2} D),   D = T_{log 2},

and T_S(g) := Tr(theta(g) Pi_S theta(g)^*) for window functions g. The
semilocal Sonin space is Theta(range S_inf) by CCM Thm 4.6 (alpha = 1 there).

Composition with kernel/'s data. kernel/ delivers S_inf through its
complement (CC arXiv:2006.13771 Prop 4.5, eq. (81)):
1 - S_inf = P + Q_inf, P = time limiting to u <= 1 (x <= 0), Q_inf the
projection onto span{zeta_n} (zeta_n supported in x >= 0). Since Theta^* maps
range P onto itself (D^{-1} moves support towards x = -inf),

    1 - Pi_S = P + Q_S,    Q_S = projection onto span{(1 - P) Theta^{*-1} zeta_n},
    Theta^{*-1} = sum_{k >= 0} (conj(alpha) 2^{-1/2})^k T_{-k log 2}          (degree 1),

so that, with Delta_T := T_S - T_inf,

    Delta_T(g) = Tr(theta(g) (Q_inf - Q_S) theta(g)^*).

Grade of these identities: derivation (unreviewed), from CCM Thm 4.6 and
bounded invertibility of Theta. This module implements Delta_T for a finite
family of mode functions on a uniform x-grid with spacing log 2 / m (so that
D is an exact grid shift). It is exercised in tests on SYNTHETIC smooth mode
families only: no number produced from a synthetic family is a value of T_S.

T_S_matrix(c, N, dps, local_data, arch_type) validates the local data first
(refusal of non-unitary data, mission kill-control 2), then the archimedean
type, then builds T_S = T_inf (kernel/) + Delta_T (ta_prolate.py, the Mellin
route, float64). KernelUnavailable is kept for a provider that cannot supply
S_inf. It never returns a number it cannot compute.
"""

from __future__ import annotations

import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_data  # noqa: E402

__all__ = [
    "KernelUnavailable",
    "FrameworkLimit",
    "arch_components",
    "T_S_matrix",
    "Grid",
    "window_basis",
    "theta_star_inv",
    "delta_T_matrix",
    "trace_matrix_direct",
]


class KernelUnavailable(NotImplementedError):
    """kernel/ has not delivered S_inf (its prolate data) through INTERFACE.md."""


class FrameworkLimit(NotImplementedError):
    """The requested data cannot be realized in L^2(X_S)^{K_S} for S = {inf, 2}."""


GAMMA_C_LIMIT = (
    "arch_type Gamma_C (the degree-2 data of Dedekind zeta_{Q(sqrt -23)}, "
    "Gamma_C(s) = Gamma_R(s) Gamma_R(s+1): one even and one odd archimedean "
    "component, both unramified at 2 with alpha = 1) cannot be realized over Q "
    "with S = {inf, 2}. A component of L^2(X_S) with archimedean parity "
    "eps is an idele class character chi = chi_inf (x) chi_2 trivial on "
    "Gamma_S = {+-2^n}; on -1 this forces (-1)^eps chi_2(-1) = 1, so an odd "
    "component needs chi_2 ramified at 2 and has no Satake parameter there. "
    "The odd piece L(s, chi_{-23}) needs 23 in S (or the construction over "
    "K = Q(sqrt -23) with its complex place). Positive control not exercised "
    "in this framework."
)


def arch_components(arch_type: str, local: ta_data.LocalData) -> list[tuple[str, object]]:
    """[(parity, alpha_j)] for the archimedean type, or FrameworkLimit."""
    t = arch_type.replace("_", "").replace(" ", "").lower()
    if t in ("gammar", "r", "real", "even"):
        return [("even", a) for a in local.alphas]
    if t in ("gammac", "c", "complex"):
        raise FrameworkLimit(GAMMA_C_LIMIT)
    raise ValueError(f"unknown arch_type {arch_type!r}")


class KernelProvider:
    """kernel/'s S_inf (read-only import, routed 2026-09-23) plus this folder's Delta_T.

    T_inf_matrix: kernel/'s moments JSON (cells_dps40.json / cells_dps60.json)
    for the mission cells, else sonin.T_inf_matrix. delta_T: ta_prolate's
    Mellin route (float64). Both returned as numpy float arrays.
    """

    def __init__(self, nvec: int | None = None, S: float | None = None):
        self.nvec = nvec
        self.S = S

    def T_inf_matrix(self, c, N: int, dps: int):
        import json

        import numpy as np
        from mpmath import mp

        kdir = os.path.normpath(os.path.join(HERE, "..", "kernel"))
        if kdir not in sys.path:
            sys.path.insert(0, kdir)
        import sonin

        path = os.path.join(kdir, f"cells_dps{60 if dps > 40 else 40}.json")
        key = str(c)
        with mp.workdps(max(dps, 40)):
            try:
                with open(path) as fh:
                    m = json.load(fh)["moments"][key]
                s = [mp.mpf(a) + mp.mpf(b) for a, b in zip(m["A_even"]["s"], m["E_even"]["s"])][: N + 1]
                d = [mp.mpf(a) + mp.mpf(b) for a, b in zip(m["A_even"]["d"], m["E_even"]["d"])][: N + 1]
                T = sonin.form_from_moments(s, d, N)
            except (OSError, KeyError):
                T = sonin.T_inf_matrix(float(c), N, dps)
            return np.array([[float(T[i, j]) for j in range(2 * N + 1)] for i in range(2 * N + 1)])

    def delta_T(self, c, N: int, dps: int, alpha, parity: str):
        import math

        import numpy as np

        import ta_prolate as TP

        if parity != "even":
            raise FrameworkLimit("only the even sector is wired")
        a = complex(alpha)
        if abs(a.imag) > 0 or abs(abs(a.real) - 1) > 1e-12:
            raise NotImplementedError("Delta_T is wired for real unitary alpha only (all mission data)")
        L = math.log(float(c))
        nvec = self.nvec or max(80, int(8 * N / L) + 40)
        S = self.S or max(1200.0, 12.0 * 2 * math.pi * N / L)
        pm = TP.ProlateModes(nvec=nvec, dps=20)
        out, _ = TP.delta_T_cells(pm, [str(c)], N, S=S, alpha=a.real)
        dT = out[str(c)][0]
        return ((dT + dT.conj().T) / 2).real


def _kernel_provider():
    """kernel/'s S_inf through its INTERFACE.md s3 (routed by the coordinator)."""
    return KernelProvider()


def T_S_matrix(c, N: int, dps: int, local_data, arch_type: str = "Gamma_R", s_inf=None, dry_run: bool = False):
    """T_S on the shared basis, (2N+1) x (2N+1), S = {inf, 2}.

    local_data: ("satake", alphas) or ("tower", {k: s_k}, degree).
    Order of checks: (1) local data at 2 (NonUnitaryLocalData for W_a, the
    Epstein tower, any |alpha| != 1); local_data=None switches the place 2
    off and returns T_inf; (2) archimedean type (FrameworkLimit for Gamma_C);
    (3) kernel/ data (read-only import of kernel/sonin.py). dry_run=True
    stops after the checks and returns "ok". The returned matrix is float64
    (Delta_T is of measured grade; see RESULTS.md s5b).
    """
    if local_data is None:
        provider = s_inf if s_inf is not None else _kernel_provider()
        return "ok" if dry_run else provider.T_inf_matrix(c, N, dps)
    degree = None
    if isinstance(local_data, (tuple, list)) and len(local_data) == 3 and local_data[0] == "tower":
        local_data, degree = local_data[:2], int(local_data[2])
    local = ta_data.validate(local_data, degree=degree)
    comps = arch_components(arch_type, local)
    provider = s_inf if s_inf is not None else _kernel_provider()
    if dry_run:
        return "ok"
    T = None
    for parity, alpha in comps:
        Tinf = provider.T_inf_matrix(c, N, dps)
        dT = provider.delta_T(c, N, dps, complex(alpha), parity)
        term = Tinf + dT
        T = term if T is None else T + term
    return T


# ---------------------------------------------------------------------------
# the composition, on a grid (float64, measured grade)
# ---------------------------------------------------------------------------


class Grid:
    """Uniform grid x_i = x_min + i dx with dx = log 2 / m and x_min a multiple of dx."""

    def __init__(self, m: int, x_min: float, x_max: float):
        self.m = int(m)
        self.dx = np.log(2.0) / self.m
        i0 = int(np.floor(x_min / self.dx))
        i1 = int(np.ceil(x_max / self.dx))
        self.i0 = i0
        self.x = self.dx * np.arange(i0, i1 + 1)
        self.n = self.x.size

    def shift(self, v: np.ndarray, k_grid: int) -> np.ndarray:
        """(T_t v)(x) = v(x - t) with t = k_grid dx, zero filled."""
        out = np.zeros_like(v)
        if abs(k_grid) >= v.size:
            return out
        if k_grid >= 0:
            out[k_grid:] = v[: v.size - k_grid]
        else:
            out[: v.size + k_grid] = v[-k_grid:]
        return out


def window_basis(grid: Grid, L: float, N: int) -> np.ndarray:
    """V_n(t) = L^{-1/2} exp(2 pi i n (t + L/2) / L) on t in [-L/2, L/2], rows n = -N..N.

    Sampled on the grid offsets t = j dx; returned with the trapezoid weights
    folded in so that theta(V_n) b = sum_j V_n(t_j) T_{t_j} b dx.
    """
    j0 = int(np.ceil(-L / 2 / grid.dx))
    j1 = int(np.floor(L / 2 / grid.dx))
    t = grid.dx * np.arange(j0, j1 + 1)
    ns = np.arange(-N, N + 1)
    V = np.exp(2j * np.pi * np.outer(ns, t + L / 2) / L) / np.sqrt(L)
    w = np.full(t.size, grid.dx)
    return V * w, np.arange(j0, j1 + 1)


def theta_star_inv(grid: Grid, v: np.ndarray, alpha: complex, kmax: int = 80) -> np.ndarray:
    """Theta^{*-1} v = sum_k (conj(alpha) 2^{-1/2})^k v(x + k log 2)."""
    a = np.conj(alpha) / np.sqrt(2.0)
    out = np.zeros_like(v, dtype=complex)
    for k in range(kmax + 1):
        out += a**k * grid.shift(v, -k * grid.m)
    return out


def _proj_onb(grid: Grid, B: np.ndarray) -> np.ndarray:
    """Orthonormal basis (rows) of span of the rows of B, L^2(dx) on the grid."""
    W = np.sqrt(grid.dx)
    Q, R = np.linalg.qr((B * W).T)
    keep = np.abs(np.diag(R)) > 1e-12 * np.abs(np.diag(R)).max()
    return (Q[:, keep].T) / W


def trace_matrix_direct(grid: Grid, onb: np.ndarray, L: float, N: int) -> np.ndarray:
    """M_mn = sum_k <theta(V_m) e_k, theta(V_n) e_k> for an ONB {e_k} of a range.

    Direct route (convolution on the grid); T(g) = v^* M v = Tr(theta(g) Q theta(g)^*).
    """
    V, js = window_basis(grid, L, N)
    M = np.zeros((2 * N + 1, 2 * N + 1), dtype=complex)
    for e in onb:
        # theta(V_n) e = sum_j V_n(t_j) dx T_{t_j} e
        shifts = np.stack([grid.shift(e, j) for j in js])  # (nt, nx)
        TE = V @ shifts  # (2N+1, nx)
        M += np.conj(TE) @ TE.T * grid.dx
    return M


def delta_T_matrix(grid: Grid, zetas: np.ndarray, alpha: complex, L: float, N: int, kmax: int = 80):
    """Delta_T = Tr(theta(g)(Q_inf - Q_S) theta(g)^*) as a matrix, for a finite mode family.

    zetas: rows = mode functions on the grid, supported in x >= 0 (not
    necessarily orthonormal; Q_inf is the projection onto their span).
    Returns (Delta_T, M_inf, M_S) with M_* the two PSD pieces.
    """
    Pmask = grid.x <= 0.0
    onb_inf = _proj_onb(grid, zetas)
    b = np.stack([theta_star_inv(grid, z, alpha, kmax) for z in zetas])
    b[:, Pmask] = 0.0
    onb_S = _proj_onb(grid, b)
    M_inf = trace_matrix_direct(grid, onb_inf, L, N)
    M_S = trace_matrix_direct(grid, onb_S, L, N)
    return M_inf - M_S, M_inf, M_S
