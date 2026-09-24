"""The archimedean Sonin projection S_inf on windows, Galerkin-computable.

Gap (a) of the c4_s2 mission.  Source: Connes-Consani arXiv:2006.13771
(cited below as CC with their equation numbers).  Mission notation: a window
function F lives on [0, L], L = log c, and g = F * F~ is its autocorrelation.
CC's test function g is our F.

The objects, from the source
----------------------------
* L^2(R)_ev with <eta|xi> = int_0^inf conj(eta) xi dx (CC eq. 16), the
  unitary scaling (theta(lam) xi)(v) = lam^{-1/2} xi(v/lam) (CC eq. 61) and
  F_{e_R} xi(y) = int xi(x) exp(-2 pi i x y) dx (CC eq. 24).
* Sonin's space S(1,1): even xi with xi = 0 on [-1,1] and F xi = 0 on
  [-1,1] (CC Def 4.4, eq. 72).  S_inf is its orthogonal projection.
* Prolate data (CC eq. 66-70, Prop 4.5): phi_n = PS_{2n,0}(2 pi, .) with
  int_{-1}^{1} phi_n(x) exp(2 pi i x w) dx = lam_n phi_n(w); xi_n = phi_n on
  [-1,1] normalized, eta_n = F xi_n = lam_n phi_n (entire),
  zeta_n = eta_n 1_{|x|>=1} / sqrt(1 - lam_n^2).  Then (CC eq. 81)

      S_inf = 1 - sum_n ( |xi_n><xi_n| + |zeta_n><zeta_n| ).

* Trace term (CC Thm 4.7, eq. 83-84): for every test function h on R_+^*,

      Tr(theta(h) S_inf) = W_inf(h) + int h(rho) eps(rho) d*rho,
      eps(rho) = sum_n lam_n / sqrt(1 - lam_n^2) <xi_n | theta(rho^{-1}) zeta_n>,

  rho >= 1, eps(1/rho) = eps(rho).  W_inf = -W_R is CC eq. 53; in the
  mission normalization it is the block A(f) of theory RESULTS s0.
* delta(rho) (CC eq. 49) = 2 rho^{1/2} [Si(2pi(1+rho))/(2pi(1+rho))
  + Si(2pi(rho-1))/(2pi(rho-1))], rho >= 1, and delta = sum lam_n^2
  <zeta_n|theta zeta_n> + eps (CC eq. 89).

The representation used here (derived in this session, graded in RESULTS.md)
-----------------------------------------------------------------------------
With eta_n entire, eps(rho) = rho^{1/2} A(rho) - rho^{-1/2} A(1/rho) for
rho >= 1, where

    A(y) = sum_n 1/(1 - lam_n^2) int_0^1 eta_n(t) eta_n(y t) dt
         = A0(y) + A1(y),
    A0(y) = 2 [ Si(2pi(1-y))/(2pi(1-y)) + Si(2pi(1+y))/(2pi(1+y)) ]
            (completeness of {xi_n} in L^2[0,1]),
    A1(y) = sum_n v_n int_0^1 eta_n(t) eta_n(y t) dt,  v_n = lam_n^2/(1-lam_n^2).

A0 is closed form and rho^{1/2} A0(rho) = delta(rho) exactly; A1 is a
series whose weights v_n decay super-exponentially, evaluated here as an even
polynomial in y from the Taylor moments of eta_n.  No numerically identified
data enter S_inf.

Parity: ``parity=0`` is the case of the source (even functions, Gamma_R(s),
zeta).  ``parity=1`` is the odd analogue (sine transform, odd prolates,
Gamma_R(s+1)); the trace identity for it is a derivation by analogy in this
session, not in the source.  The Gamma_C type is parity 0 plus parity 1.

House rules: mpmath only, explicit precision via mp.workdps, guard digits
internal, no global state left modified.
"""

from __future__ import annotations

import functools

from mpmath import mp

__all__ = [
    "GUARD",
    "prolate_data",
    "delta",
    "eps",
    "eps_right_derivative_at_1",
    "Window",
    "form_from_moments",
    "pole_matrix",
    "arch_matrix",
    "eps_matrix",
    "delta_matrix",
    "T_inf_matrix",
    "R_inf_matrix",
    "real_basis",
    "constraint_rows",
    "restrict",
    "prolate_vectors",
    "phi_tilde",
    "eta_all",
    "sonin_z_all",
    "S_inf_window_matrix",
]

#: Guard digits carried internally above the caller's dps.
GUARD = 25

#: Bandwidth of the Sonin pair for Lambda = 1 (CC eq. 66: (2 pi x)^2).
def _bw():
    return 2 * mp.pi


# ---------------------------------------------------------------------------
# prolate data (Legendre-Galerkin for the Slepian-Pollack operator, CC eq. 66)
# ---------------------------------------------------------------------------


def _legendre_moment(m: int, k: int):
    """int_{-1}^{1} x^m P_k(x) dx for m >= k, m - k even (else 0)."""
    if k > m or (m - k) % 2:
        return mp.mpf(0)
    a = (m + k) // 2
    b = (m - k) // 2
    return (
        mp.mpf(2) ** (k + 1)
        * mp.factorial(m)
        * mp.factorial(a)
        / (mp.factorial(b) * mp.factorial(m + k + 1))
    )


def _slepian_matrix(K: int, parity: int):
    """W = -d(1-x^2)d + c^2 x^2 on orthonormal Legendre p_k, k = parity mod 2.

    x^2 P_k = a_k P_{k+2} + b_k P_k + g_k P_{k-2} with
    a_k = (k+1)(k+2)/((2k+1)(2k+3)), b_k = (2k^2+2k-1)/((2k-1)(2k+3)).
    """
    c2 = _bw() ** 2
    ks = [parity + 2 * i for i in range(K)]
    M = mp.matrix(K)
    for i, k in enumerate(ks):
        M[i, i] = k * (k + 1) + c2 * mp.mpf(2 * k * k + 2 * k - 1) / ((2 * k - 1) * (2 * k + 3))
        if i + 1 < K:
            v = c2 * mp.mpf((k + 1) * (k + 2)) / ((2 * k + 3) * mp.sqrt((2 * k + 1) * (2 * k + 5)))
            M[i, i + 1] = v
            M[i + 1, i] = v
    return ks, M


def _eigpairs(K: int, parity: int, nwant: int):
    """Lowest nwant eigenpairs of the tridiagonal Slepian matrix.

    Eigenvalues by mpmath's implicit-QL tridiag_eigen (no vectors), then each
    eigenvector by three steps of inverse iteration with the tridiagonal
    (Thomas) solver.  Returns (ks, evals ascending (all K), vectors[nwant])
    with vectors orthonormal in the p_k basis."""
    from mpmath.matrices import eigen_symmetric as es

    ks, W = _slepian_matrix(K, parity)
    d = [W[i, i] for i in range(K)]
    e = [W[i, i + 1] for i in range(K - 1)] + [mp.mpf(0)]
    ev = list(d)
    es.tridiag_eigen(mp, ev, list(e), False)
    ev = sorted(ev)
    tiny = mp.mpf(10) ** (-(mp.dps - 5))
    vecs = []
    for n in range(nwant):
        sig = ev[n] * (1 + tiny) + tiny
        x = [mp.mpf(1) / (i + 1) for i in range(K)]
        for _ in range(3):
            # solve (W - sig) y = x, Thomas algorithm
            cp, dp = [mp.mpf(0)] * K, [mp.mpf(0)] * K
            b0 = d[0] - sig
            if b0 == 0:
                b0 = tiny
            cp[0] = e[0] / b0
            dp[0] = x[0] / b0
            for i in range(1, K):
                den = d[i] - sig - e[i - 1] * cp[i - 1]
                if den == 0:
                    den = tiny
                cp[i] = e[i] / den if i < K - 1 else mp.mpf(0)
                dp[i] = (x[i] - e[i - 1] * dp[i - 1]) / den
            y = [mp.mpf(0)] * K
            y[K - 1] = dp[K - 1]
            for i in range(K - 2, -1, -1):
                y[i] = dp[i] - cp[i] * y[i + 1]
            nrm = mp.sqrt(mp.fsum(t * t for t in y))
            x = [t / nrm for t in y]
        vecs.append(x)
    return ks, ev, vecs


@functools.lru_cache(maxsize=None)
def prolate_data(dps: int, parity: int = 0, K: int = 0, ymax: int = 3):
    """Prolate data at bandwidth 2 pi, and the polynomial A1.

    Returns a dict (all mpf at working precision dps + GUARD):
      ``lam``   list of lam_n (CC eq. 68 for parity 0; for parity 1 the real
                mu_n with int phi_n sin(2 pi x w) dx = mu_n phi_n(w));
      ``v``     v_n = lam_n^2 / (1 - lam_n^2);
      ``edge``  phi~_n(1), phi~_n normalized by int_0^1 phi~_n^2 = 1;
      ``alpha`` coefficients of A1(y) = sum_l alpha_l y^(2l + 2 parity);
      ``n_max``, ``J``, ``K``: the truncations used (weights below
      10^-(dps+GUARD) are dropped; J covers Taylor terms up to y = ymax).
    Cached per (dps, parity, K, ymax).  K = 0 picks the default size.
    """
    wd = dps + GUARD
    with mp.workdps(wd):
        tol = mp.mpf(10) ** (-wd)
        c = _bw()
        # Taylor length J: (2 pi ymax)^(2j+p)/(2j+p)! * 4 < tol
        J = 1
        while True:
            m = 2 * J + parity
            if 4 * (c * ymax) ** m / mp.factorial(m) < tol and m > c * ymax:
                break
            J += 1
        J += 2
        Kdim = K if K else max(J + 2, 70)
        ks, evals, vecs = _eigpairs(Kdim, parity, 40)
        lam, v, edge, beta_list = [], [], [], []
        for idx in range(40):
            beta = vecs[idx]
            # phi~ = sqrt2 * sum beta_k p_k, p_k = sqrt(k+1/2) P_k
            coef = [mp.sqrt(2) * beta[i] * mp.sqrt(ks[i] + mp.mpf(1) / 2) for i in range(Kdim)]
            e1 = mp.fsum(coef)  # P_k(1) = 1
            if e1 < 0:
                coef = [-x for x in coef]
                e1 = -e1
            if parity == 0:
                # lam = int_{-1}^{1} phi~ / phi~(0)
                p0 = mp.fsum(
                    coef[i] * (-1) ** (ks[i] // 2) * mp.fac2(ks[i] - 1) / mp.fac2(ks[i])
                    for i in range(Kdim)
                )
                lam_n = 2 * coef[0] / p0
            else:
                # mu = [d/dw int phi~ sin(2 pi x w) dx]_{w=0} / phi~'(0)
                #    = 2 pi int x phi~ / phi~'(0);  int x P_1 = 2/3, P_k'(0) for odd k
                d0 = mp.fsum(
                    coef[i] * (-1) ** ((ks[i] - 1) // 2) * mp.fac2(ks[i]) / mp.fac2(ks[i] - 1)
                    for i in range(Kdim)
                )
                lam_n = c * coef[0] * mp.mpf(2) / 3 / d0
            vn = lam_n**2 / (1 - lam_n**2)
            lam.append(lam_n)
            v.append(vn)
            edge.append(e1)
            beta_list.append(coef)
            if vn < tol * mp.mpf(10) ** -5 and len(lam) >= 6:
                break
        n_max = len(lam)
        # Taylor coefficients of eta_n(s) = int_{-1}^{1} phi~_n(x) trig(2 pi x s) dx
        # (trig = cos for parity 0, sin for parity 1), in powers s^(2j+p):
        # e_{nj} = (-1)^j (2 pi)^(2j+p) / (2j+p)! * int x^(2j+p) phi~_n dx.
        mom = {}
        e = []
        for n in range(n_max):
            coef = beta_list[n]
            row = []
            for j in range(J):
                m = 2 * j + parity
                Mnj = mp.fsum(coef[i] * _mom_cached(m, ks[i], mom) for i in range(Kdim) if ks[i] <= m)
                row.append((-1) ** j * c**m / mp.factorial(m) * Mnj)
            e.append(row)
        # A1(y) = sum_n v_n sum_{j,l} e_nj e_nl y^(2l+p) / (2j+2l+2p+1)
        C = [[mp.fsum(v[n] * e[n][j] * e[n][l] for n in range(n_max)) for l in range(J)] for j in range(J)]
        alpha = [
            mp.fsum(C[j][l] / (2 * j + 2 * l + 2 * parity + 1) for j in range(J))
            for l in range(J)
        ]
        return {
            "dps": dps,
            "parity": parity,
            "lam": lam,
            "v": v,
            "edge": edge,
            "alpha": alpha,
            "n_max": n_max,
            "J": J,
            "K": Kdim,
            "chi": evals[:n_max],
            "ks": ks,
            "coef": beta_list,
            "e": e,
        }


def _mom_cached(m, k, cache):
    key = (m, k)
    if key not in cache:
        cache[key] = _legendre_moment(m, k)
    return cache[key]


# ---------------------------------------------------------------------------
# S_inf as a projection on L^2(R_+^*, d*u)  (the representation two_adic uses)
# ---------------------------------------------------------------------------
# Via w: L^2(R)_ev -> L^2(R_+^*, d*u), (w xi)(u) = u^{1/2} xi(u) (CC eq. 17):
#   x_n(u) = u^{1/2} phi~_n(u) 1_{u<1},  z_n(u) = u^{1/2} eta_n(u) 1_{u>=1} / sqrt(1-lam_n^2),
#   S_inf = 1 - sum_n (|x_n><x_n| + |z_n><z_n|)          (CC eq. 81)
#         = M_{1[u>=1]} - sum_n |z_n><z_n|              (range P = Sonin + span z_n).
# The second form converges super-exponentially on vectors supported in
# u <= X: z_n on [1, X] is of size |eta_n| <= |lam_n| |phi~_n(X)|.


@functools.lru_cache(maxsize=None)
def prolate_vectors(dps: int, parity: int = 0, nvec: int = 60):
    """Legendre coefficients (phi~_n = sum coef[n][i] P_ks[i]) for n < nvec.

    Same normalization and sign as prolate_data (int_0^1 phi~^2 = 1,
    phi~_n(1) > 0).  lam is returned for completeness; for n beyond
    prolate_data's n_max it is below 10^-(dps+GUARD) and only its size is
    meaningful.  Kdim = nvec + 45 Legendre functions of the given parity.
    """
    wd = dps + GUARD
    with mp.workdps(wd):
        Kdim = nvec + 45
        ks, evals, vecs = _eigpairs(Kdim, parity, nvec)
        coefs = []
        for idx in range(nvec):
            coef = [mp.sqrt(2) * vecs[idx][r] * mp.sqrt(ks[r] + mp.mpf(1) / 2) for r in range(Kdim)]
            if mp.fsum(coef) < 0:
                coef = [-x for x in coef]
            coefs.append(coef)
        return {"ks": ks, "coef": coefs, "parity": parity, "nvec": nvec}


def _sph_bessel_all(kmax: int, z):
    """[j_0(z), ..., j_kmax(z)] by Miller's downward recurrence, z > 0."""
    M = kmax + int(z) + 60
    f_next = mp.mpf(0)
    f = mp.mpf(10) ** (-mp.dps)
    vals = [mp.mpf(0)] * (kmax + 1)
    for k in range(M, 0, -1):
        f_prev = (2 * k + 1) / z * f - f_next
        f_next, f = f, f_prev
        if k - 1 <= kmax:
            vals[k - 1] = f
    j0 = mp.sin(z) / z
    j1 = mp.sin(z) / z**2 - mp.cos(z) / z
    scale = j0 / vals[0] if abs(j0) > abs(j1) else j1 / vals[1]
    return [v * scale for v in vals]


def phi_tilde(n: int, x, dps: int = 40, parity: int = 0):
    """phi~_n(x) (analytic continuation) by the Legendre three-term recurrence."""
    pv = prolate_vectors(dps, parity)
    with mp.workdps(dps + GUARD):
        x = mp.mpf(x)
        ks, coef = pv["ks"], pv["coef"][n]
        P = [mp.mpf(1), x]
        for k in range(1, ks[-1]):
            P.append(((2 * k + 1) * x * P[k] - k * P[k - 1]) / (k + 1))
        out = mp.fsum(cf * P[k] for k, cf in zip(ks, coef))
    return +out


def eta_all(s, dps: int = 40, parity: int = 0, nvec: int = 60):
    """[eta_n(s), n < nvec], eta_n = F xi_n = lam_n phi~_n (cos transform for
    parity 0, sine transform for parity 1), via int_{-1}^{1} P_k(x) e^{i w x} dx
    = 2 i^k j_k(w): eta_n(s) = sum_i coef[n][i] 2 (-1)^{floor(k_i/2)} j_{k_i}(2 pi s).
    Valid for every s >= 0 (no Taylor truncation)."""
    pv = prolate_vectors(dps, parity, nvec)
    with mp.workdps(dps + GUARD):
        s = mp.mpf(s)
        ks = pv["ks"]
        if s == 0:
            jb = [mp.mpf(1)] + [mp.mpf(0)] * ks[-1]
        else:
            jb = _sph_bessel_all(ks[-1], 2 * mp.pi * s)
        w = [2 * (-1) ** (k // 2) * jb[k] for k in ks]
        out = [mp.fsum(cf * wk for cf, wk in zip(coef, w)) for coef in pv["coef"]]
    return out


def sonin_z_all(u, dps: int = 40, parity: int = 0, nvec: int = 60):
    """[z_n(u), n < nvec] in L^2(R_+^*, d*u); zero for u < 1."""
    u = mp.mpf(u)
    if u < 1:
        return [mp.mpf(0)] * nvec
    et = eta_all(u, dps, parity, nvec)
    lam = prolate_data(dps, parity)["lam"]
    with mp.workdps(dps + GUARD):
        out = []
        for n, e in enumerate(et):
            ln = lam[n] if n < len(lam) else mp.mpf(0)
            out.append(mp.sqrt(u) * e / mp.sqrt(1 - ln**2))
    return out


def S_inf_window_matrix(c, N: int, dps: int = 40, u0=None, K: int | None = None, parity: int = 0):
    """<V_m | S_inf | V_n> for the window [u0, u0 c] in L^2(R_+^*, d*u).

    V_n(u) = U_n(log(u/u0)) = L^{-1/2} exp(2 pi i n log(u/u0) / L); default
    u0 = c^{-1/2} (the CCM placement [lambda^-1, lambda], lambda = sqrt c).
    S_inf is not scale invariant, so this matrix depends on u0 (the trace
    term T_inf does not).  Uses S_inf = M_{1[u>=1]} - sum_{k<K} |z_k><z_k|.
    Returns (S, K, tail) where tail = sum over the last 5 retained k of
    sum_n |<z_k|V_n>|^2 (the measured size of the truncation).
    Complex Hermitian (2N+1)^2 mp.matrix, index 0 = -N.
    """
    wd = dps + GUARD
    with mp.workdps(wd):
        c = mp.mpf(c)
        L = mp.log(c)
        u0 = 1 / mp.sqrt(c) if u0 is None else mp.mpf(u0)
        y1 = max(mp.mpf(0), -mp.log(u0))
        dim = 2 * N + 1
        G = mp.matrix(dim, dim)
        for i in range(dim):
            m = i - N
            for j in range(dim):
                n = j - N
                if y1 >= L:
                    G[i, j] = 0
                elif m == n:
                    G[i, j] = (L - y1) / L
                else:
                    G[i, j] = (1 - mp.exp(2j * mp.pi * (n - m) * y1 / L)) / (2j * mp.pi * (n - m))
        if y1 >= L:
            return G, 0, mp.mpf(0)
        from mpmath.calculus.quadrature import GaussLegendre

        nodes = GaussLegendre(mp).calc_nodes(7 if N <= 20 else 8, mp.prec)
        a, b = y1, L
        ys = [(b - a) / 2 * (1 + t) + a for t, _ in nodes]
        ws = [(b - a) / 2 * wt for _, wt in nodes]
        nvec = 60
        zs = [sonin_z_all(u0 * mp.exp(y), dps, parity, nvec) for y in ys]
        Un = [[mp.exp(2j * mp.pi * n * y / L) / mp.sqrt(L) for n in range(-N, N + 1)] for y in ys]
        coeff = []
        for k in range(nvec):
            coeff.append([mp.fsum(w * z[k] * U[j] for w, z, U in zip(ws, zs, Un)) for j in range(dim)])
        norms = [mp.fsum(abs(x) ** 2 for x in row) for row in coeff]
        if K is None:
            tol = mp.mpf(10) ** (-(dps + 5))
            K = next((k for k in range(nvec) if all(nm < tol for nm in norms[k : k + 5])), nvec)
        tail = mp.fsum(norms[K : K + 5]) if K < nvec else None
        S = mp.matrix(dim, dim)
        for i in range(dim):
            for j in range(dim):
                S[i, j] = G[i, j] - mp.fsum(mp.conj(coeff[k][i]) * coeff[k][j] for k in range(K))
    with mp.workdps(dps):
        out = mp.matrix(dim, dim)
        for i in range(dim):
            for j in range(dim):
                out[i, j] = +S[i, j]
    return out, K, tail


# ---------------------------------------------------------------------------
# delta, eps (scalar functions of rho)
# ---------------------------------------------------------------------------


def _si_over(z):
    """Si(z)/z, with the value 1 at z = 0."""
    if z == 0:
        return mp.mpf(1)
    return mp.si(z) / z


def _A0(y, parity: int = 0):
    """Completeness part of A (closed form)."""
    c = _bw()
    s = -1 if parity else 1
    return 2 * (_si_over(c * (1 - y)) + s * _si_over(c * (1 + y)))


def _A1(y, data):
    p = data["parity"]
    y2 = y * y
    acc = mp.mpf(0)
    for a in reversed(data["alpha"]):
        acc = acc * y2 + a
    return acc * (y**p if p else 1)


def _A(y, data):
    return _A0(y, data["parity"]) + _A1(y, data)


def delta(rho, dps: int = 40, parity: int = 0):
    """CC eq. 49 (parity 0); the sine analogue for parity 1.  delta(1/rho) = delta(rho)."""
    with mp.workdps(dps + GUARD):
        r = mp.mpf(rho)
        if r < 1:
            r = 1 / r
        out = mp.sqrt(r) * _A0(r, parity)
    return +out


def eps(rho, dps: int = 40, parity: int = 0):
    """eps(rho) of CC Thm 4.7 (eq. 84), via rho^{1/2} A(rho) - rho^{-1/2} A(1/rho)."""
    data = prolate_data(dps, parity)
    with mp.workdps(dps + GUARD):
        r = mp.mpf(rho)
        if r < 1:
            r = 1 / r
        out = mp.sqrt(r) * _A(r, data) - _A(1 / r, data) / mp.sqrt(r)
    return +out


def _eps_x(x, data):
    """eps(e^x) for x >= 0 at the ambient precision."""
    r = mp.exp(x)
    return mp.exp(x / 2) * _A(r, data) - mp.exp(-x / 2) * _A(1 / r, data)


def _delta_x(x, parity):
    return mp.exp(x / 2) * _A0(mp.exp(x), parity)


def eps_right_derivative_at_1(dps: int = 40, parity: int = 0, route: str = "series"):
    """eps'(1+) in rho.

    route="series": CC Lemma 5.4, sum_n v_n xi_n(1)^2.
    route="split":  d/drho [rho^{1/2}A(rho) - rho^{-1/2}A(1/rho)] at 1
                    = A(1) + 2 A'(1), from this module's representation.
    """
    data = prolate_data(dps, parity)
    with mp.workdps(dps + GUARD):
        if route == "series":
            out = mp.fsum(vn * en**2 for vn, en in zip(data["v"], data["edge"]))
        else:
            dA = mp.diff(lambda y: _A(y, data), 1)
            out = _A(mp.mpf(1), data) + 2 * dA
    return +out


# ---------------------------------------------------------------------------
# Galerkin forms on the shared CCM basis U_n = L^{-1/2} e^{2 pi i n y / L}
# ---------------------------------------------------------------------------


class Window:
    """Gauss-Legendre rule on [0, L] and the trigonometric weights.

    ``deg`` selects 3 * 2^(deg-1) nodes (mpmath's GaussLegendre).  The
    default is chosen from N and dps; tests measure the rule by doubling.
    """

    def __init__(self, c, N: int, dps: int, deg: int | None = None):
        self.dps = dps
        self.N = int(N)
        wd = dps + GUARD
        with mp.workdps(wd):
            self.c = mp.mpf(c)
            self.L = mp.log(self.c)
            if deg is None:
                deg = 7 if (N <= 20 and dps <= 45) else 8
            self.deg = deg
            from mpmath.calculus.quadrature import GaussLegendre

            nodes = GaussLegendre(mp).calc_nodes(deg, mp.prec)
            half = self.L / 2
            self.x = [half * (1 + t) for t, _ in nodes]
            self.w = [half * wt for _, wt in nodes]

    def moments(self, kern):
        """(s_k, k = 0..N; d_k, k = 0..N) for a kernel K on (0, L]:
        s_k = int K sin(w_k x), d_k = int K 2(1 - x/L) cos(w_k x), w_k = 2 pi k/L."""
        with mp.workdps(self.dps + GUARD):
            L, N = self.L, self.N
            Kx = [kern(x) for x in self.x]
            s, d = [], []
            for k in range(N + 1):
                om = 2 * mp.pi * k / L
                s.append(mp.fsum(w * K * mp.sin(om * x) for x, w, K in zip(self.x, self.w, Kx)))
                d.append(
                    mp.fsum(
                        w * K * 2 * (1 - x / L) * mp.cos(om * x) for x, w, K in zip(self.x, self.w, Kx)
                    )
                )
            return s, d


def form_from_moments(s, d, N: int):
    """The (2N+1)^2 matrix M(n,m) = int K q_nm (CCM Lemma 2.3), index 0 = -N.

    Off-diagonal (s_m - s_n)/(pi (n - m)) with s_{-k} = -s_k; diagonal d_|n|.
    """
    M = mp.matrix(2 * N + 1)

    def sg(k):
        return s[k] if k >= 0 else -s[-k]

    for i in range(2 * N + 1):
        n = i - N
        for j in range(i, 2 * N + 1):
            m = j - N
            if n == m:
                val = d[abs(n)]
            else:
                val = (sg(m) - sg(n)) / (mp.pi * (n - m))
            M[i, j] = val
            M[j, i] = val
    return M


def _snap(M, dps):
    with mp.workdps(dps):
        out = mp.matrix(M.rows, M.cols)
        for i in range(M.rows):
            for j in range(M.cols):
                out[i, j] = +M[i, j]
    return out


def pole_matrix(c, N: int, dps: int = 40, win: Window | None = None, raw: bool = False):
    """P(f) = 2 int g(x) cosh(x/2) dx (theory s0), kernel 2 cosh(x/2)."""
    win = win or Window(c, N, dps)
    with mp.workdps(dps + GUARD):
        s, d = win.moments(lambda x: 2 * mp.cosh(x / 2))
        M = form_from_moments(s, d, N)
    return (M, s, d) if raw else _snap(M, dps)


def _arch_moments(win: Window, parity: int = 0):
    """Moments of the archimedean block A (W_inf of CC eq. 53).

    parity 0 (Gamma_R(s)), theory s0:
      A(f) = -[gamma + log pi + log(1 - e^{-2L})] g(0)
             + int_0^L 2[e^{-2x} g(0) - e^{-x/2} g(x)] / (1 - e^{-2x}) dx.
    Both parities are written in the digamma form
      W_a(f) = (psi(a) - log pi) g(0) + int_0^inf 2 [g(0) - g(x)] rho_a(x) dx,
      rho_a(x) = e^{-2 a x} / (1 - e^{-2x}),
    a = 1/4 for Gamma_R(s) and a = 3/4 for Gamma_R(s+1), from
    Re psi(a + i r/2) = psi(a) + int_0^inf 2 rho_a(x) (1 - cos r x) dx.  For
    a = 1/4 it equals theory s0 exactly (psi(1) - psi(1/4) and the tail
    -log(1 - e^{-2L}) account for the difference; pinned in the tests).
    On [0, L] the tail int_L^inf rho_a contributes 2 T_a(L) g(0).  The
    x -> 0 limit is removable (rho_a ~ 1/(2x) against g(0) - g(x) = O(x)); the
    integrand is evaluated at interior Gauss nodes with expm1, so no finite
    difference is taken anywhere.
    """
    L, N = win.L, win.N
    a = mp.mpf(1) / 4 if parity == 0 else mp.mpf(3) / 4
    const = mp.psi(0, a) - mp.log(mp.pi)
    # tail T_a(L) = int_L^inf e^{-2 a x}/(1 - e^{-2x}) dx = sum_j e^{-2(j+a)L}/(2(j+a))
    T = mp.mpf(0)
    j = 0
    while True:
        term = mp.exp(-2 * (j + a) * L) / (2 * (j + a))
        T += term
        if term < mp.mpf(10) ** (-(mp.dps + 5)):
            break
        j += 1
    s, d = [], []
    xs, ws = win.x, win.w
    den = [-mp.expm1(-2 * x) for x in xs]
    rho = [mp.exp(-2 * a * x) / dn for x, dn in zip(xs, den)]
    for k in range(N + 1):
        om = 2 * mp.pi * k / L
        # off-diagonal: A(n,m) = -int rho_a q_nm  ->  s_k^A = -int rho_a sin(om x)
        s.append(-mp.fsum(w * r * mp.sin(om * x) for x, w, r in zip(xs, ws, rho)))
        # diagonal: const + 2 T + int_0^L [2 - 2(1-x/L) cos(om x)] rho_a dx
        #   1 - (1-x/L) cos = (x/L) cos + 2 sin^2(om x / 2)
        dd = mp.fsum(
            w * r * 2 * ((x / L) * mp.cos(om * x) + 2 * mp.sin(om * x / 2) ** 2)
            for x, w, r in zip(xs, ws, rho)
        )
        d.append(const + 2 * T + dd)
    return s, d


def arch_matrix(c, N: int, dps: int = 40, parity: int = 0, win: Window | None = None, raw=False):
    """The archimedean block A = W_inf (mission normalization, theory s0)."""
    win = win or Window(c, N, dps)
    with mp.workdps(dps + GUARD):
        s, d = _arch_moments(win, parity)
        M = form_from_moments(s, d, N)
    return (M, s, d) if raw else _snap(M, dps)


def eps_matrix(c, N: int, dps: int = 40, parity: int = 0, win: Window | None = None, raw=False):
    """E(f) = int_{-L}^{L} g(x) eps(e^{|x|}) dx, the eps-block of CC Thm 4.7."""
    win = win or Window(c, N, dps)
    data = prolate_data(dps, parity)
    with mp.workdps(dps + GUARD):
        s, d = win.moments(lambda x: _eps_x(x, data))
        M = form_from_moments(s, d, N)
    return (M, s, d) if raw else _snap(M, dps)


def delta_matrix(c, N: int, dps: int = 40, parity: int = 0, win: Window | None = None, raw=False):
    """D(f) = int g(x) delta(e^{|x|}) dx (CC eq. 56)."""
    win = win or Window(c, N, dps)
    with mp.workdps(dps + GUARD):
        s, d = win.moments(lambda x: _delta_x(x, parity))
        M = form_from_moments(s, d, N)
    return (M, s, d) if raw else _snap(M, dps)


def T_inf_matrix(c, N: int, dps: int = 40, parity: int = 0, arch_type: str | None = None):
    """T_inf(f) = Tr(theta(f) S_inf theta(f)*) = A(f) + E(f) (CC Thm 4.7).

    arch_type: None or "R" -> the source case (parity 0, Gamma_R(s));
    "R_odd" -> parity 1; "C" -> Gamma_C = Gamma_R(s) Gamma_R(s+1), the sum of
    the two parity terms (derivation by analogy for the odd part).
    """
    if arch_type in (None, "R"):
        parities = [parity]
    elif arch_type == "R_odd":
        parities = [1]
    elif arch_type == "C":
        parities = [0, 1]
    else:
        raise ValueError(arch_type)
    win = Window(c, N, dps)
    with mp.workdps(dps + GUARD):
        tot = None
        for p in parities:
            A, _, _ = arch_matrix(c, N, dps, p, win, raw=True)
            E, _, _ = eps_matrix(c, N, dps, p, win, raw=True)
            tot = A + E if tot is None else tot + A + E
    return _snap(tot, dps)


def R_inf_matrix(c, N: int, dps: int = 40):
    """R_inf = Q_inf - T_inf = P - E (source case, parity 0)."""
    win = Window(c, N, dps)
    with mp.workdps(dps + GUARD):
        P, _, _ = pole_matrix(c, N, dps, win, raw=True)
        E, _, _ = eps_matrix(c, N, dps, 0, win, raw=True)
        out = P - E
    return _snap(out, dps)


# ---------------------------------------------------------------------------
# real basis, the function class of Thm 6.11, restriction
# ---------------------------------------------------------------------------


def real_basis(N: int):
    """Columns of the unitary V: complex coefficients (index 0 = -N) of the
    real orthonormal basis [U_0, C_1..C_N, S_1..S_N], C_k = (U_k + U_-k)/sqrt2,
    S_k = (U_k - U_-k)/(i sqrt2).  V^* M V is real for the forms here."""
    dim = 2 * N + 1
    V = mp.matrix(dim, dim)
    V[N, 0] = 1
    r = 1 / mp.sqrt(2)
    for k in range(1, N + 1):
        V[N + k, k] = r
        V[N - k, k] = r
        V[N + k, N + k] = -1j * r
        V[N - k, N + k] = 1j * r
    return V


def to_real(M, N: int):
    """V^* M V as a real mp.matrix."""
    V = real_basis(N)
    R = V.H * M * V
    out = mp.matrix(R.rows)
    for i in range(R.rows):
        for j in range(R.cols):
            out[i, j] = mp.re(R[i, j])
    return out


def constraint_rows(c, N: int, which=("minus",)):
    """Real row vectors (in the real basis) of the class conditions.

    "minus": ghat(-i/2) = 0, i.e. int_0^L F(y) e^{-y/2} dy = 0 (CC Thm 6.11);
    "plus":  int F e^{+y/2} = 0 (the reflected condition);
    "zero":  ghat(0) = int F = 0 (CC Thm 1 / eq. 4).
    int U_n e^{s y} dy = L^{-1/2} (e^{sL} - 1)/(s + i w_n).
    """
    L = mp.log(mp.mpf(c))
    rows = []
    for w in which:
        if w == "zero":
            kappa = {n: (mp.sqrt(L) if n == 0 else mp.mpf(0)) for n in range(-N, N + 1)}
        else:
            sg = mp.mpf(-1) / 2 if w == "minus" else mp.mpf(1) / 2
            kappa = {
                n: (mp.exp(sg * L) - 1) / (sg + 2j * mp.pi * n / L) / mp.sqrt(L)
                for n in range(-N, N + 1)
            }
        row = [mp.re(kappa[0])]
        for k in range(1, N + 1):
            row.append(mp.sqrt(2) * mp.re(kappa[k]))
        for k in range(1, N + 1):
            row.append(mp.sqrt(2) * mp.im(kappa[k]))
        rows.append(row)
    return rows


def null_basis(rows, dim: int):
    """Orthonormal basis (columns) of the orthogonal complement of the rows."""
    Q = []
    for r in rows:
        v = [mp.mpf(x) for x in r]
        for _ in range(2):
            for q in Q:
                pr = mp.fsum(a * b for a, b in zip(q, v))
                v = [a - pr * b for a, b in zip(v, q)]
        nv = mp.sqrt(mp.fsum(a * a for a in v))
        Q.append([a / nv for a in v])
    basis = []
    for i in range(dim):
        v = [mp.mpf(0)] * dim
        v[i] = mp.mpf(1)
        for _ in range(2):
            for q in Q + basis:
                pr = mp.fsum(a * b for a, b in zip(q, v))
                v = [a - pr * b for a, b in zip(v, q)]
        nv = mp.sqrt(mp.fsum(a * a for a in v))
        if nv > mp.mpf("0.1"):
            basis.append([a / nv for a in v])
        if len(basis) == dim - len(rows):
            break
    B = mp.matrix(dim, len(basis))
    for j, v in enumerate(basis):
        for i in range(dim):
            B[i, j] = v[i]
    return B


def restrict(Mreal, B):
    """B^T M B."""
    return B.T * Mreal * B
