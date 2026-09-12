"""Independent implementation of the CvS/CCM truncated Weil quadratic form.

Built ONLY from the definitions extracted in ``SOURCE.md`` (CCM
arXiv:2511.22755 eq. (3.10)-(3.16), Lemma 2.3, and our own re-derivation of
the archimedean entries from (3.15); CvS arXiv:2511.23257 Prop 4.1 for the
divided-difference presentation; Groskin arXiv:2607.02828 s2.1 for the
T-truncated source route).  No code from any of those projects was consulted
or ported.

Two independent routes to the same matrix are provided:

* :func:`assemble` -- the cutoff-free closed-form assembly (digamma,
  trigamma, geometric series in e^{-2L}); this is the production route.
* :func:`arch_matrix_T` -- the archimedean block at a finite cutoff T by
  direct quadrature of the Groskin source integrals; used to reproduce the
  finite-T eigenvalue flow and as a cross-check of the closed forms.

Both the zeta assembly and the Davenport-Heilbronn assembly (same Galerkin
scheme, DH explicit-formula data; see SOURCE.md s4) are supported.

House rules: mpmath only, explicit dps via mp.workdps at call sites, no
global state left modified.  All closed forms are validated against direct
quadrature by ``run_replication.py`` before anything downstream trusts them.
"""

from __future__ import annotations

import math
from mpmath import mp

# ---------------------------------------------------------------------------
# arithmetic helpers
# ---------------------------------------------------------------------------


def prime_powers_upto(c: float) -> list[tuple[int, str]]:
    """[(q, p)] for prime powers q = p^a <= c; Lambda(q) = log p."""
    out = []
    limit = int(math.floor(c + 1e-9))
    sieve = [True] * (limit + 1)
    for p in range(2, limit + 1):
        if sieve[p]:
            for m in range(2 * p, limit + 1, p):
                sieve[m] = False
            q = p
            while q <= limit:
                out.append((q, p))
                q *= p
    return sorted(out)


def dh_kappa():
    """kappa for the Davenport-Heilbronn function, closed form.

    kappa = (sqrt(10 - 2 sqrt 5) - 2) / (sqrt 5 - 1) (Titchmarsh s10.25).
    ``run_replication.py`` checks this against zeta.epstein.KAPPA_REF (the
    lab derives kappa numerically from the functional equation defect).
    """
    s5 = mp.sqrt(5)
    return (mp.sqrt(10 - 2 * s5) - 2) / (s5 - 1)


def dh_lambda_coeffs(cmax: int):
    """Lambda_f(n) for the DH Dirichlet series, n = 2..cmax.

    From -f'/f: a_n log n = sum_{d | n} Lambda_f(d) a_{n/d}, a_1 = 1, so
    Lambda_f(n) = a_n log n - sum_{d | n, 1 < d < n} Lambda_f(d) a_{n/d}.
    a_n is the period-5 pattern (1, kappa, -kappa, -1, 0).  Supported on all
    n >= 2 (the DH function has no Euler product), unlike Lambda.
    """
    k = dh_kappa()
    pat = [mp.mpf(1), k, -k, mp.mpf(-1), mp.mpf(0)]

    def a(n):
        return pat[(n - 1) % 5]

    lam = {1: mp.mpf(0)}
    for n in range(2, cmax + 1):
        s = a(n) * mp.log(n)
        for d in range(2, n):
            if n % d == 0:
                s -= lam[d] * a(n // d)
        lam[n] = s
    return [(n, lam[n]) for n in range(2, cmax + 1) if lam[n] != 0]


# ---------------------------------------------------------------------------
# archimedean closed forms (our derivation from CCM (3.15); see SOURCE.md)
# ---------------------------------------------------------------------------
# rho_a(y) = sum_{j>=0} exp(-mu_j y), mu_j = 2 (j + a);  a = 1/4 for zeta
# (Gamma(s/2) factor), a = 3/4 for DH (Gamma((s+1)/2) factor).
#
# Elementary building blocks, E = exp(-mu L):
#   I_sin (mu, om) = int_0^L e^{-mu y} sin(om y) dy = om (1-E) / (mu^2+om^2)
#   I_cos1(mu, om) = int_0^L e^{-mu y}(cos(om y)-1) dy
#                  = -om^2 (1-E) / (mu (mu^2+om^2))
#   I_xcos(mu, om) = int_0^L y e^{-mu y} cos(om y) dy
#                  = [(1-E)(mu^2-om^2) - mu L E (mu^2+om^2)] / (mu^2+om^2)^2
# Summing the E-free parts over j gives digamma/trigamma closed forms; the
# E parts are geometric series in z = e^{-2L}.


def _arch_sums(a, L, N, J):
    """S[k] = int_0^L sin(2 pi k y / L) rho_a(y) dy for k = 0..N, and
    diag[k] = the diagonal combination D(k) = int_0^L (q_kk - 2) rho_a dy,
    plus tail = int_L^infty rho_a dy.  J = number of geometric terms."""
    S = [mp.mpf(0)] * (N + 1)
    D = [mp.mpf(0)] * (N + 1)
    mus = [2 * (j + a) for j in range(J)]
    Es = [mp.e ** (-m * L) for m in mus]
    tail = mp.fsum(E / m for m, E in zip(mus, Es))
    for k in range(N + 1):
        om = 2 * mp.pi * k / L
        z = mp.mpc(a, om / 2)
        if k == 0:
            S[0] = mp.mpf(0)
            sum_cos1 = mp.mpf(0)
        else:
            # sum_j om/(mu_j^2+om^2) = (1/2) Im psi(a + i om/2)
            S[k] = mp.im(mp.psi(0, z)) / 2 - mp.fsum(
                E * om / (m * m + om * om) for m, E in zip(mus, Es)
            )
            # sum_j I_cos1 = -(1/2)[Re psi(a+i om/2) - psi(a)] + geometric
            sum_cos1 = -(mp.re(mp.psi(0, z)) - mp.psi(0, mp.mpf(a))) / 2 + mp.fsum(
                E * om * om / (m * (m * m + om * om)) for m, E in zip(mus, Es)
            )
        # sum_j I_xcos = (1/4) Re psi'(a+i om/2) - geometric
        sum_xcos = mp.re(mp.psi(1, z)) / 4 - mp.fsum(
            E * ((m * m - om * om) / (m * m + om * om) ** 2 + m * L / (m * m + om * om))
            for m, E in zip(mus, Es)
        )
        D[k] = 2 * sum_cos1 - (2 / L) * sum_xcos
    return S, D, tail


# ---------------------------------------------------------------------------
# the assembly
# ---------------------------------------------------------------------------


class Truncation:
    """The (2N+1)-dimensional truncated Weil form at cutoff c, band N.

    kind = "zeta": Q = W02 - WR - Wp per CCM (3.10).
    kind = "dh":   Q = -WR_dh - Wp_dh (no pole block; DH data).

    Entries are computed at the ambient mp.dps of the constructor call and
    stored as exact mpf snapshots; wrap construction in mp.workdps.
    """

    def __init__(self, c, N: int, kind: str = "zeta"):
        self.c = c
        self.N = int(N)
        self.kind = kind
        L = mp.log(c)
        self.L = L
        J = int((mp.dps + 12) * mp.log(10) / (2 * L)) + 3
        if kind == "zeta":
            a = mp.mpf(1) / 4
            const = -mp.log(mp.pi) + mp.psi(0, a)
            coeffs = [(q, mp.log(p)) for (q, p) in prime_powers_upto(float(c))]
        elif kind == "dh":
            a = mp.mpf(3) / 4
            const = -mp.log(mp.pi / 5) + mp.psi(0, a)
            coeffs = dh_lambda_coeffs(int(math.floor(float(c) + 1e-9)))
        else:
            raise ValueError(kind)
        self.a = a
        S, D, tail = _arch_sums(a, L, N, J)
        # minus-WR entries: off-diagonal -(S_m - S_n)/(pi (n-m)) with
        # S_{-k} = -S_k; diagonal const - D(|n|) + 2*tail.
        self._S = S
        self._archdiag = [const - D[k] + 2 * tail for k in range(N + 1)]
        # prime block sequences: P_k, R_k (P_{-k} = -P_k, R_{-k} = R_k)
        P = [mp.mpf(0)] * (N + 1)
        R = [mp.mpf(0)] * (N + 1)
        for q, lam in coeffs:
            y = mp.log(q)
            w = lam / mp.sqrt(q)
            for k in range(N + 1):
                om = 2 * mp.pi * k / L
                P[k] += w * mp.sin(om * y)
                R[k] += w * 2 * (1 - y / L) * mp.cos(om * y)
        self._P = P
        self._R = R

    # -- blocks -----------------------------------------------------------

    def w02(self, n: int, m: int):
        """Pole block W02(n,m); zero for DH (entire function)."""
        if self.kind != "zeta":
            return mp.mpf(0)
        L, pi2 = self.L, mp.pi**2
        num = 32 * L * mp.sinh(L / 4) ** 2 * (L * L - 16 * pi2 * m * n)
        return num / ((L * L + 16 * pi2 * m * m) * (L * L + 16 * pi2 * n * n))

    def _sgn(self, seq, k: int):
        return seq[k] if k >= 0 else -seq[-k]

    def entry(self, n: int, m: int):
        """Q(n,m), n, m in [-N, N]."""
        if n == m:
            k = abs(n)
            return self.w02(n, n) + self._archdiag[k] - self._R[k]
        # -WR - Wp = -[(S+P)_m - (S+P)_n] / (pi (n - m))
        tm = self._sgn(self._S, m) + self._sgn(self._P, m)
        tn = self._sgn(self._S, n) + self._sgn(self._P, n)
        return self.w02(n, m) - (tm - tn) / (mp.pi * (n - m))

    # -- parity sectors ---------------------------------------------------

    def even_matrix(self):
        """(N+1) x (N+1) even sector: basis e_0, (e_k + e_{-k})/sqrt2."""
        N = self.N
        E = mp.matrix(N + 1)
        E[0, 0] = self.entry(0, 0)
        for k in range(1, N + 1):
            v = mp.sqrt(2) * self.entry(0, k)
            E[0, k] = v
            E[k, 0] = v
        for j in range(1, N + 1):
            for k in range(j, N + 1):
                v = self.entry(j, k) + self.entry(j, -k)
                E[j, k] = v
                E[k, j] = v
        return E

    def odd_matrix(self):
        """N x N odd sector: basis (e_k - e_{-k})/sqrt2, k = 1..N."""
        N = self.N
        O = mp.matrix(N)
        for j in range(1, N + 1):
            for k in range(j, N + 1):
                v = self.entry(j, k) - self.entry(j, -k)
                O[j - 1, k - 1] = v
                O[k - 1, j - 1] = v
        return O


# ---------------------------------------------------------------------------
# finite-T archimedean block (Groskin source route), for cross-validation
# ---------------------------------------------------------------------------


def _hplus(r, a, logqpi):
    """Archimedean density: Re psi(a + i r/2) - log(pi/Q0)."""
    return mp.re(mp.psi(0, mp.mpc(a, r / 2))) - logqpi


def arch_matrix_T(c, N: int, T, kind: str = "zeta", npanels: int | None = None):
    """Q_arch,T source-route matrix values: (psi(n), psi'(n)) for n = 0..N.

    psi_{R,T}(x) = (1/(2 pi^2)) int_{-T}^{T} h(r) S(r,x,L) dr with
    S(r,x,L) = int_0^L sin(2 pi x (1-y/L)) cos(r y) dy  (G2 eq. (3)).
    At integer nodes (G2 Thm 3.2 proof, re-derived here):
      S(r,n,L)  = 2 n rho sin^2(L(r - rho n)/2) / ((r - rho n)(r + rho n))
      S_x(r,n,L)= 2 rho sin^2(L(r - rho n)/2) (r^2 + rho^2 n^2)
                  / ((r - rho n)^2 (r + rho n)^2)
    with rho = 2 pi / L; the shifted sine kills the spurious singularity.
    Returns (psi_vals, psi_der) lists for n = 0..N.
    """
    L = mp.log(c)
    rho = 2 * mp.pi / L
    if kind == "zeta":
        a, logqpi = mp.mpf(1) / 4, mp.log(mp.pi)
    else:
        a, logqpi = mp.mpf(3) / 4, mp.log(mp.pi / 5)
    if npanels is None:
        npanels = max(8, int(mp.ceil(T / rho)) * 2)
    pts = [T * mp.mpf(i) / npanels for i in range(npanels + 1)]
    psi_vals, psi_der = [], []
    for n in range(N + 1):
        b = rho * n

        def f_val(r, b=b):
            if n == 0:
                return mp.mpf(0)
            s = mp.sin(L * (r - b) / 2)
            return _hplus(r, a, logqpi) * 2 * n * rho * s * s / ((r - b) * (r + b))

        def f_der(r, b=b):
            s = mp.sin(L * (r - b) / 2)
            num = 2 * rho * s * s * (r * r + b * b)
            return _hplus(r, a, logqpi) * num / ((r - b) ** 2 * (r + b) ** 2)

        # (1/(2 pi^2)) int_{-T}^{T} = (1/pi^2) int_0^T  (even integrand)
        v = mp.quad(f_val, pts) / mp.pi**2 if n > 0 else mp.mpf(0)
        d = mp.quad(f_der, pts) / mp.pi**2
        psi_vals.append(v)
        psi_der.append(d)
    return psi_vals, psi_der


def total_matrix_T(trunc: Truncation, T, npanels: int | None = None):
    """Even-sector matrix of Q_tot,T = Q_prime + Q_pole + Q_arch,T.

    Uses the closed-form prime and pole blocks from ``trunc`` and replaces
    the cutoff-free archimedean block with the finite-T source route.
    """
    N = trunc.N
    pv, pd = arch_matrix_T(trunc.c, N, T, kind=trunc.kind, npanels=npanels)

    def arch_entry(n, m):
        if n == m:
            return pd[abs(n)]
        an = pv[abs(n)] * (1 if n >= 0 else -1)
        am = pv[abs(m)] * (1 if m >= 0 else -1)
        return (am - an) / (m - n)

    def q_entry(n, m):
        if n == m:
            k = abs(n)
            return trunc.w02(n, n) + arch_entry(n, n) - trunc._R[k]
        pm = trunc._sgn(trunc._P, m)
        pn = trunc._sgn(trunc._P, n)
        wp = (pm - pn) / (mp.pi * (n - m))
        return trunc.w02(n, m) + arch_entry(n, m) - wp

    E = mp.matrix(N + 1)
    E[0, 0] = q_entry(0, 0)
    for k in range(1, N + 1):
        v = mp.sqrt(2) * q_entry(0, k)
        E[0, k] = v
        E[k, 0] = v
    for j in range(1, N + 1):
        for k in range(j, N + 1):
            v = q_entry(j, k) + q_entry(j, -k)
            E[j, k] = v
            E[k, j] = v
    return E


# ---------------------------------------------------------------------------
# spectra, ground state, zero extraction
# ---------------------------------------------------------------------------


def eigsy_sorted(M):
    """(eigenvalues ascending, eigenvector matrix columns to match)."""
    E, V = mp.eigsy(M)
    pairs = sorted(range(M.rows), key=lambda i: E[i])
    evals = [E[i] for i in pairs]
    evecs = [[V[r, i] for r in range(M.rows)] for i in pairs]
    return evals, evecs


def embed_even(v):
    """Even-sector coordinates v_0..v_N -> full u_{-N}..u_N (dict k->u_k)."""
    N = len(v) - 1
    u = {0: v[0]}
    for k in range(1, N + 1):
        u[k] = v[k] / mp.sqrt(2)
        u[-k] = v[k] / mp.sqrt(2)
    return u


def F_even(v, L):
    """The ground-state transform F_v(z) (SOURCE.md s2), real for real z."""
    N = len(v) - 1
    u = embed_even(v)

    def F(z):
        s = u[0] / z
        for k in range(1, N + 1):
            om = 2 * mp.pi * k / L
            s += u[k] * (1 / (z - om) + 1 / (z + om))
        return 2 * mp.sin(z * L / 2) * s

    return F


def find_zeros(F, zmin, zmax, step=None):
    """Real zeros of F on [zmin, zmax] by sign change + bisection refine."""
    step = step or mp.mpf("0.2")
    zs = []
    z0 = mp.mpf(zmin)
    f0 = F(z0)
    z = z0 + step
    while z <= zmax:
        f1 = F(z)
        if f0 * f1 < 0:
            lo, hi, flo = z - step, z, f0
            for _ in range(mp.prec + 8):
                mid = (lo + hi) / 2
                fm = F(mid)
                if fm == 0:
                    lo = hi = mid
                    break
                if flo * fm < 0:
                    hi = mid
                else:
                    lo, flo = mid, fm
            zs.append((lo + hi) / 2)
        f0 = f1
        z += step
    return zs


# ---------------------------------------------------------------------------
# the dictionary test function g_v (G2 Thm 2.5), for the zero-side check
# ---------------------------------------------------------------------------


def g_even(v, L):
    """g_v(r) = sum_{m,n} u_m u_n int_0^L q_{nm}(y) cos(r y) dy, closed form.

    Works for complex r (needed for the pole identity g_v(i/2))."""
    N = len(v) - 1
    u = embed_even(v)
    idx = list(range(-N, N + 1))

    def Tsin(k, r):
        om = 2 * mp.pi * k / L
        s = mp.sin(L * (r - om) / 2)
        return 2 * s * s * om / ((om - r) * (om + r)) if k != 0 else mp.mpf(0) * r

    def g(r):
        tot = mp.mpf(0)
        Ts = {k: Tsin(k, r) for k in range(-N, N + 1)}
        for i, n in enumerate(idx):
            for m in idx[i:]:
                w = u[n] * u[m] * (1 if m == n else 2)
                if n == m:
                    om = 2 * mp.pi * n / L
                    sm = mp.sin(L * (r - om) / 2)
                    sp = mp.sin(L * (r + om) / 2)
                    val = (2 / L) * (sm * sm / (r - om) ** 2 + sp * sp / (r + om) ** 2)
                else:
                    val = (Ts[m] - Ts[n]) / (mp.pi * (n - m))
                tot += w * val
        return tot

    return g
