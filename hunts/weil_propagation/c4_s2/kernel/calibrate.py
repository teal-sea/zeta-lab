"""Calibration of T_inf against Connes-Consani arXiv:2006.13771 Thm 6.11.

R_inf = Q_inf - T_inf = P - E (sonin.R_inf_matrix).  The statements tested:

* Thm 4.7: T_inf = A + E is positive semidefinite on every window.
* Thm 1 / eq. (4): on the class C2 = {ghat(-i/2) = 0, ghat(0) = 0}, R_inf >= 0
  (support in [2^-1/2, 2^1/2], i.e. c <= 2).
* Thm 6.11 / eq. (141): on C1 = {ghat(-i/2) = 0}, R_inf + c0 |ghat(0)|^2 >= 0
  with c0 = 4 gamma / log 2, gamma ~ 2.94355 (so c0 ~ 16.987), and the best
  constant c* lies in (13, 17) (Rem 6.12).  Here c*(N) = sup over C1 in the
  band of E(F) / |int F|^2 (a Galerkin lower bound for c* at c = 2).
* s6.1-6.2: lam_max(K_I) ~ 1.05158 (within 0.00122, eq. 134) and the next
  eigenvalue ~ 0.687925 for |I| = log 2, where E(F) = 2 eps'(1+) (<h|K_I h> -
  |h|^2) with F = h/2 - h' (Prop 5.5, Lemma 3.3).  The Rayleigh-Ritz values
  on {h : h/2 - h' in C1 and the band} are lower bounds increasing in N.
"""

from __future__ import annotations

from mpmath import mp

import sonin as S

__all__ = ["h_gram", "analyze_cell", "inertia", "C0_THM611"]


def _gamma_cc():
    return mp.mpf("2.94355")


def C0_THM611():
    """c = 4 gamma / log 2 of CC eq. (141), gamma ~ 2.94355 (Lemma 6.10)."""
    return 4 * _gamma_cc() / mp.log(2)


def inertia(evals, tol):
    neg = sum(1 for x in evals if x < -tol)
    pos = sum(1 for x in evals if x > tol)
    return [neg, len(evals) - neg - pos, pos]


def h_gram(c, N: int):
    """Gram matrix of h_n, where h_n/2 - h_n' = U_n, h_n(0) = 0:
    h_n(y) = -L^{-1/2} (e^{i w_n y} - e^{y/2}) / (i w_n - 1/2).
    On C1 these h vanish at y = L, so this is |h|^2 on L^2[0, L]."""
    L = mp.log(mp.mpf(c))
    eh = mp.exp(L / 2) - 1
    e1 = mp.exp(L) - 1
    H = mp.matrix(2 * N + 1)
    for i in range(2 * N + 1):
        m = i - N
        wm = 2 * mp.pi * m / L
        for j in range(2 * N + 1):
            n = j - N
            wn = 2 * mp.pi * n / L
            num = (L if m == n else 0) - eh * (1 / (mp.mpf(1) / 2 - 1j * wm) + 1 / (mp.mpf(1) / 2 + 1j * wn)) + e1
            H[i, j] = num / (L * (mp.mpf(1) / 2 + 1j * wm) * (mp.mpf(1) / 2 - 1j * wn))
    return H


def _eigs(M):
    return sorted(mp.eigsy(M, eigvals_only=True))


def _cstar(Q1, u):
    """sup_{z: u.z = 1} of -Q1(z) = sup E / |ell|^2 on C1, given Q1 = R|C1
    and ell(z) = u.z; requires Q1 > 0 on u-perp (checked by caller)."""
    dim = Q1.rows
    nu2 = mp.fsum(x * x for x in u)
    w0 = mp.matrix([x / nu2 for x in u])
    W2 = S.null_basis([u], dim)
    G = W2.T * Q1 * W2
    b = W2.T * Q1 * w0
    q00 = (w0.T * Q1 * w0)[0, 0]
    sol = mp.lu_solve(G, b)
    minval = q00 - (b.T * sol)[0, 0]
    return -minval


def analyze_cell(c, N: int, dps: int = 40, kI: bool | None = None, nlow: int = 3):
    """Everything the calibration reports at one (c, N, dps).

    Returns a dict of mpf values (converted to strings by the caller).
    Tolerance for inertia: 10^-(dps-10) (values here are O(1e-4) or larger).
    """
    win = S.Window(c, N, dps)
    wd = dps + S.GUARD
    out = {"c": c, "N": N, "dps": dps}
    with mp.workdps(wd):
        A, _, _ = S.arch_matrix(c, N, dps, 0, win, raw=True)
        E, _, _ = S.eps_matrix(c, N, dps, 0, win, raw=True)
        P, _, _ = S.pole_matrix(c, N, dps, win, raw=True)
        T = S.to_real(A + E, N)
        R = S.to_real(P - E, N)
        Er = S.to_real(E, N)
    with mp.workdps(dps):
        tol = mp.mpf(10) ** (-(dps - 10))
        T = +T
        R = +R
        evT = _eigs(T)
        out["T_low"] = evT[:nlow]
        out["T_inertia"] = inertia(evT, tol)
        evR = _eigs(R)
        out["R_full_low"] = evR[:nlow]
        out["R_full_inertia"] = inertia(evR, tol)
        rows1 = S.constraint_rows(c, N, ("minus",))
        rows2 = S.constraint_rows(c, N, ("minus", "zero"))
        B1 = S.null_basis(rows1, 2 * N + 1)
        B2 = S.null_basis(rows2, 2 * N + 1)
        R1 = S.restrict(R, B1)
        R2 = S.restrict(R, B2)
        ev1 = _eigs(R1)
        ev2 = _eigs(R2)
        out["R_C1_low"] = ev1[:nlow]
        out["R_C1_inertia"] = inertia(ev1, tol)
        out["R_C2_low"] = ev2[:nlow]
        out["R_C2_inertia"] = inertia(ev2, tol)
        # c*(N): ell(F) = int F = sqrt(L) * (U_0 coordinate); in C1 coordinates u = B1^T e_0 sqrt(L)
        L = mp.log(mp.mpf(c))
        u = [B1[0, j] * mp.sqrt(L) for j in range(B1.cols)]
        if out["R_C2_inertia"][0] == 0:
            out["cstar"] = _cstar(R1, u)
        else:
            out["cstar"] = None
        # Thm 6.11 inequality: R + c0 |ell|^2 on C1
        c0 = C0_THM611()
        Rc = R1 + c0 * mp.matrix(u) * mp.matrix(u).T
        evc = _eigs(Rc)
        out["thm611_low"] = evc[0]
        if kI is None:
            kI = True
        if kI:
            with mp.workdps(wd):
                H = S.to_real(h_gram(c, N), N)
                HB = B1.T * H * B1
                EB = B1.T * Er * B1
                Lc = mp.cholesky(HB)
                Li = mp.inverse(Lc)
                Mk = Li * EB * Li.T
                mu = sorted(mp.eigsy(Mk, eigvals_only=True), reverse=True)
                e1p = S.eps_right_derivative_at_1(dps)
                kap = [1 + x / (2 * e1p) for x in mu[:2]]
            out["K_top"] = [+kap[0], +kap[1]]
    return out
