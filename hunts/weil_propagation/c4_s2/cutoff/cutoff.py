"""Gap (c) for S = {inf, 2}: the product-ball cutoff against the module cutoff.

Everything here is a check of a statement in ``RESULTS.md``; nothing here
builds a trace term.  Sources (read 2026-09-23, PDFs in the session
scratchpad, not committed):

* Connes, arXiv:math/9811068, s VII eq. (5), (12), (13), Theorem 4: the
  Hilbert space L2(X_S), X_S = A_S / Gamma_S, and the cutoff by the module.
* Connes, arXiv:2602.04022, s7.4 eq. (22) and footnote 11: the semilocal
  trace formula with the projections "defined using the module".
* Connes, Consani, Moscovici, arXiv:2310.18423 s4: w_S, E_S, eta_S (Prop
  4.1, eq. (46)-(47)), the local 2-adic Sonin vector sigma_p (Prop 4.5),
  the module Sonin space (Def 4.5), theta_S (Prop 4.6, eq. (57)-(58)) and
  Theorem 4.6 (theta_S maps the archimedean Sonin space onto the module
  Sonin space, bounded with bounded inverse).

Sections:

1. ``BallModel``: exact rational model of radial functions on Q_2, in the
   basis of ball indicators b_k = 1{|x|_2 <= 2^k}, k = -K..K.  It is the
   space of radial functions on the finite group 2^-K Z_2 / 2^K Z_2, closed
   under the Fourier transform and under both ball cutoffs, so the local
   statements about time and frequency limiting at 2 are exact in it.
2. Gamma_S-invariance of the two cutoffs, exact on rational points.
3. The maps eta_S (class of 1_{Z_2} (x) f) and theta_S (class of
   sigma_2 (x) f) on the K_S-invariant sector, by two routes: the Gamma-sum
   from the definition, Mellin-transformed by quadrature, against the local
   Euler factor times the closed-form archimedean Mellin transform.
4. The multiplier m(s) = |1 - 2^(-1/2-is)|^2 and kappa = max m / min m.
5. A finite-dimensional check of the comparison lemma of RESULTS.md s4.
6. The prime-atom form at n = 2 on the mission's shared basis, by a closed
   form and, independently, from the weil_trunc Galerkin code.
7. The window compression of m: the Gram matrix of theta_S on the shared
   basis by direct quadrature, against 3/2 I - sqrt2 H and the prime block.

House rules: mpmath with explicit mp.workdps; sympy Rationals for the exact
parts; numpy only for the random finite-dimensional sanity check.
"""

from __future__ import annotations

import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp
from mpmath import mp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
GALERKIN_PATH = REPO / "hunts" / "rogue_frontier" / "weil_trunc" / "galerkin.py"

CELLS_C = (2.2, 2.5, 2.9)
CELLS_N = (8, 16, 32)
DPS = 40


# ---------------------------------------------------------------------------
# 1. radial functions on Q_2, exact
# ---------------------------------------------------------------------------


class BallModel:
    """Radial functions on Q_2 spanned by b_k = 1{|x|_2 <= 2^k}, |k| <= K.

    Coefficient vectors are column vectors c with f = sum_k c_k b_k, index
    0 <-> k = -K.  Haar measure is self-dual (vol Z_2 = 1), the character is
    e_2 (trivial on Z_2), so F(b_k) = 2^k b_{-k}.  Operators are sympy
    matrices acting on coefficient vectors; the inner product is c^T G d.
    """

    def __init__(self, K: int):
        self.K = int(K)
        n = 2 * self.K + 1
        self.n = n
        ks = list(range(-self.K, self.K + 1))
        self.ks = ks
        self.G = sp.Matrix(n, n, lambda i, j: sp.Rational(2) ** min(ks[i], ks[j]))
        F = sp.zeros(n, n)
        for j, k in enumerate(ks):
            F[self.idx(-k), j] = sp.Rational(2) ** k
        self.F = F

    def idx(self, k: int) -> int:
        return k + self.K

    def ball_mult(self, r: int):
        """Multiplication by 1{|x|_2 <= 2^r}: b_k -> b_{min(k, r)}."""
        M = sp.zeros(self.n, self.n)
        for j, k in enumerate(self.ks):
            M[self.idx(min(k, r)), j] = 1
        return M

    def freq_limit(self, r: int):
        """F (ball_mult r) F^-1, the frequency limitation to the same ball."""
        return self.F * self.ball_mult(r) * self.F.inv()

    def shell(self, n: int):
        """eps_n = 1{|x|_2 = 2^n} = b_n - b_{n-1} (CCM Prop 4.5 notation)."""
        v = sp.zeros(self.n, 1)
        v[self.idx(n)] += 1
        v[self.idx(n - 1)] -= 1
        return v

    def sigma2(self):
        """CCM Prop 4.5 local Sonin vector at p = 2: eps_0 - eps_1 / 2."""
        return self.shell(0) - sp.Rational(1, 2) * self.shell(1)

    def is_orthogonal_projection(self, M) -> bool:
        return (M * M - M).is_zero_matrix and (self.G * M - (self.G * M).T).is_zero_matrix

    def joint_kernel(self, r: int):
        """Basis of {f : ball_mult(r) f = 0 and freq_limit(r) f = 0}."""
        A = self.ball_mult(r).col_join(self.freq_limit(r))
        return A.nullspace()


def two_adic_facts(K: int = 5) -> dict:
    """Exact local statements at p = 2 used in RESULTS.md s1."""
    B = BallModel(K)
    Mc, Mhc = B.ball_mult(0), B.freq_limit(0)
    Mo, Mho = B.ball_mult(-1), B.freq_limit(-1)
    prod_c = Mc * Mhc
    b0 = sp.zeros(B.n, 1)
    b0[B.idx(0)] = 1
    ker_c = B.joint_kernel(0)
    ker_o = B.joint_kernel(-1)
    s2 = B.sigma2()
    # is the open-ball joint kernel spanned by sigma_2?
    spanned = len(ker_o) == 1 and sp.Matrix.hstack(ker_o[0], s2).rank() == 1
    return {
        "K": K,
        "fourier_unitary": (B.F.T * B.G * B.F - B.G).is_zero_matrix,
        "closed_time_is_projection": B.is_orthogonal_projection(Mc),
        "closed_freq_is_projection": B.is_orthogonal_projection(Mhc),
        "closed_time_equals_freq": (Mc - Mhc).is_zero_matrix,
        "closed_time_freq_commute": (Mc * Mhc - Mhc * Mc).is_zero_matrix,
        "closed_product_rank": prod_c.rank(),
        "closed_product_range_is_1_Z2": sp.Matrix.hstack(prod_c, b0).rank() == 1,
        "closed_joint_kernel_dim": len(ker_c),
        "open_time_freq_commute": (Mo * Mho - Mho * Mo).is_zero_matrix,
        "open_joint_kernel_dim": len(ker_o),
        "open_joint_kernel_is_sigma2": bool(spanned),
        "sigma2_fourier_fixed": (B.F * s2 - s2).is_zero_matrix,
        "sigma2_norm_sq": str((s2.T * B.G * s2)[0, 0]),
    }


# ---------------------------------------------------------------------------
# 2. Gamma_S-invariance, exact on rational points
# ---------------------------------------------------------------------------
#
# A point of A_S with x_2 != 0 is recorded as (x_inf, v) with v = ord_2(x_2),
# |x_2|_2 = 2^-v.  The unit 2 in Gamma_S acts by (x_inf, v) -> (2 x_inf, v+1).


def module(x_inf: Fraction, v: int) -> Fraction:
    return abs(Fraction(x_inf)) * Fraction(2) ** (-v)


def in_product_ball(x_inf: Fraction, v: int, lam: Fraction) -> bool:
    """|x_inf| <= lam and |x_2|_2 <= 1 (the closed product ball)."""
    return abs(Fraction(x_inf)) <= lam and v >= 0


def in_module_ball(x_inf: Fraction, v: int, lam: Fraction) -> bool:
    return module(x_inf, v) <= lam


def act(x_inf: Fraction, v: int, n: int):
    """The S-unit 2^n acting diagonally."""
    return Fraction(x_inf) * Fraction(2) ** n, v + n


def orbit_count_product_ball(x_inf: Fraction, v: int, lam: Fraction, nmax: int = 200) -> int:
    """#{n in Z : 2^n x in product ball}; finite for x_inf != 0."""
    return sum(in_product_ball(*act(x_inf, v, n), lam) for n in range(-nmax, nmax + 1))


def orbit_count_formula(x_inf: Fraction, v: int, lam: Fraction) -> int:
    """floor(log2(lam / |x|_S)) + 1 when |x|_S <= lam, else 0 (exact)."""
    q = Fraction(lam) / module(x_inf, v)
    if q < 1:
        return 0
    k = 0
    while Fraction(2) ** (k + 1) <= q:
        k += 1
    return k + 1


# ---------------------------------------------------------------------------
# 3. eta_S and theta_S on the K_S-invariant sector, two routes
# ---------------------------------------------------------------------------


def gaussian(x):
    return mp.exp(-mp.pi * x * x)


def local_eta(v: int):
    """1_{Z_2} as a function of the valuation v of x_2."""
    return mp.mpf(1) if v >= 0 else mp.mpf(0)


local_eta.vmin = 0


def local_sigma2(v: int):
    """sigma_2 = eps_0 - eps_1/2: 1 on |x|=1 (v=0), -1/2 on |x|=2 (v=-1)."""
    if v == 0:
        return mp.mpf(1)
    if v == -1:
        return -mp.mpf(1) / 2
    return mp.mpf(0)


local_sigma2.vmin = -1


def wS_class(local, f, u, xmax: float = 12.0, nmax: int = 400):
    """w_S of the class of local (x) f at the point 1 x u of C_S.

    w_S(xi)(u) = u^{1/2} sum_{n in Z} xi(2^n * (1, u)), where 2^n in Q_2 has
    valuation n.  The sign unit -1 is absorbed because f is even.  The sum
    starts at the lowest valuation where the local factor is nonzero and
    stops once 2^n u > xmax, where the Gaussian is below e^{-pi xmax^2}.
    """
    s = mp.mpf(0)
    n = local.vmin
    while n <= nmax:
        x = mp.ldexp(u, n)
        if x > xmax:
            break
        loc = local(n)
        if loc:
            s += loc * f(x)
        n += 1
    return mp.sqrt(u) * s


def mellin(w, s, dps: int = 30):
    """F_mu(w)(s) = int_0^inf w(u) u^{-is} du/u, by quadrature in t = log u."""
    with mp.workdps(dps + 10):
        s = mp.mpf(s)
        g = lambda t: w(mp.exp(t)) * mp.expj(-s * t)
        pts = [-mp.inf, -8, -4, -2, -1, 0, 1, 2, 3, mp.inf]
        return +mp.quad(g, pts, maxdegree=10)


def mellin_gaussian_closed(s):
    """F_mu(w_inf f)(s) for f = exp(-pi x^2): (1/2) pi^{-z/2} Gamma(z/2), z = 1/2 - is."""
    z = mp.mpf(1) / 2 - 1j * mp.mpf(s)
    return mp.pi ** (-z / 2) * mp.gamma(z / 2) / 2


def L2(z):
    return 1 / (1 - mp.mpf(2) ** (-z))


def eta_theta_check(s_list=(0, 1.3, 5.7, 14.1347), dps: int = 30) -> list[dict]:
    """Route 1 (Gamma-sum + quadrature) against route 2 (Euler factor x closed form)."""
    out = []
    with mp.workdps(dps):
        for s in s_list:
            s = mp.mpf(s)
            base = mellin_gaussian_closed(s)
            eta_q = mellin(lambda u: wS_class(local_eta, gaussian, u), s, dps)
            theta_q = mellin(lambda u: wS_class(local_sigma2, gaussian, u), s, dps)
            z = mp.mpf(1) / 2 - 1j * s
            eta_c = L2(z) * base  # CCM (47): L_2(1/2 - is)
            theta_c = (1 - mp.mpf(2) ** (-(mp.mpf(1) / 2 + 1j * s))) * base  # CCM (57)
            out.append(
                {
                    "s": float(s),
                    "eta_rel_dev": float(abs(eta_q - eta_c) / abs(eta_c)),
                    "theta_rel_dev": float(abs(theta_q - theta_c) / abs(theta_c)),
                    "ratio_theta_over_eta": complex(theta_q / eta_q),
                    "m_of_s": float(m_of_s(s)),
                }
            )
    return out


# ---------------------------------------------------------------------------
# 4. the multiplier and kappa
# ---------------------------------------------------------------------------


def m_of_s(s):
    """|1 - 2^(-1/2 - is)|^2 = 3/2 - sqrt(2) cos(s log 2)."""
    return mp.mpf(3) / 2 - mp.sqrt(2) * mp.cos(mp.mpf(s) * mp.log(2))


def kappa_exact():
    """(3/2 + sqrt2) / (3/2 - sqrt2), simplified exactly."""
    r2 = sp.sqrt(2)
    k = sp.nsimplify(sp.radsimp((sp.Rational(3, 2) + r2) / (sp.Rational(3, 2) - r2)))
    return sp.expand(k)


# ---------------------------------------------------------------------------
# 5. the comparison lemma in finite dimensions (sanity check)
# ---------------------------------------------------------------------------


def _proj(B):
    Q, _ = np.linalg.qr(B)
    return Q @ Q.conj().T


def comparison_lemma_trials(trials: int = 400, n: int = 40, k: int = 12, seed: int = 7) -> dict:
    """T_W(g) = sum_i |g_i|^2 Pi_W[i, i]; compare W = S and W = diag(a) S.

    Lemma (RESULTS.md s4): with lo <= |a_i|^2 <= hi, kappa = hi / lo,
    kappa^-1 T_S <= T_aS <= kappa T_S.  Records the extreme observed ratios.
    """
    rng = np.random.default_rng(seed)
    lo, hi = 1.5 - math.sqrt(2), 1.5 + math.sqrt(2)
    kap = hi / lo
    rmin, rmax = float("inf"), 0.0
    for _ in range(trials):
        S = rng.normal(size=(n, k)) + 1j * rng.normal(size=(n, k))
        phase = rng.uniform(0, 2 * math.pi, size=n)
        mod = np.sqrt(rng.uniform(lo, hi, size=n))
        a = mod * np.exp(1j * phase)
        g2 = rng.exponential(size=n)
        t0 = float(np.real(np.sum(g2 * np.diag(_proj(S)))))
        t1 = float(np.real(np.sum(g2 * np.diag(_proj(a[:, None] * S)))))
        r = t1 / t0
        rmin, rmax = min(rmin, r), max(rmax, r)
    return {"kappa": kap, "ratio_min": rmin, "ratio_max": rmax, "trials": trials}


# ---------------------------------------------------------------------------
# 6. the prime-atom form at n = 2 on the shared basis
# ---------------------------------------------------------------------------


def shift_form_matrix(c, N: int, dps: int = DPS):
    """H with v* H v = Re int f(y) conj f(y - log 2) dy, f = sum v_n U_n.

    Shared basis U_n(y) = L^{-1/2} exp(2 pi i n y / L) on [0, L], L = log c,
    index 0 <-> n = -N.  Closed form (RESULTS.md s5): theta = 2 pi log2 / L,
    H_nn = (1 - log2/L) cos(n theta), H_nm = (sin(m theta) - sin(n theta)) /
    (2 pi (n - m)).  The Weil form Q carries -sqrt(2) log 2 * H.
    """
    with mp.workdps(dps):
        L = mp.log(mp.mpf(c))
        a = mp.log(2)
        th = 2 * mp.pi * a / L
        ns = list(range(-N, N + 1))
        H = mp.matrix(2 * N + 1)
        for i, n in enumerate(ns):
            for j, m in enumerate(ns):
                if n == m:
                    H[i, j] = (1 - a / L) * mp.cos(n * th)
                else:
                    H[i, j] = (mp.sin(m * th) - mp.sin(n * th)) / (2 * mp.pi * (n - m))
        return H


def atom_matrix(c, N: int, dps: int = DPS):
    """sqrt(2) log 2 * H: the n = 2 atom term W_2 that Q subtracts (Q = Q_inf - W_2)."""
    with mp.workdps(dps):
        return mp.sqrt(2) * mp.log(2) * shift_form_matrix(c, N, dps)


def _load_galerkin():
    spec = importlib.util.spec_from_file_location("weil_trunc_galerkin", GALERKIN_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def galerkin_prime_block(c, N: int, dps: int = DPS):
    """-W_2 read from weil_trunc/galerkin.py (read-only import): its prime block.

    Diagonal -R_k, off-diagonal -(P_m - P_n) / (pi (n - m)); for c < 3 the
    only prime power is 2.
    """
    gal = _load_galerkin()
    with mp.workdps(dps):
        T = gal.Truncation(mp.mpf(c), N, "zeta")
        ns = list(range(-N, N + 1))
        M = mp.matrix(2 * N + 1)
        for i, n in enumerate(ns):
            for j, m in enumerate(ns):
                if n == m:
                    M[i, j] = -T._R[abs(n)]
                else:
                    pm = T._sgn(T._P, m)
                    pn = T._sgn(T._P, n)
                    M[i, j] = -(pm - pn) / (mp.pi * (n - m))
        return M


def shift_form_spectrum(c, N: int, dps: int = DPS) -> dict:
    """Eigenvalue statistics of H (continuum spectrum {-1/2, 0, 1/2}, RESULTS s5)."""
    with mp.workdps(dps):
        H = shift_form_matrix(c, N, dps)
        ev = sorted(float(x) for x in mp.eigsy(H, eigvals_only=True))
        L = math.log(c)
        return {
            "c": c,
            "N": N,
            "dps": dps,
            "dim": 2 * N + 1,
            "n_above_quarter": sum(1 for x in ev if x > 0.25),
            "n_below_minus_quarter": sum(1 for x in ev if x < -0.25),
            "max_eig": ev[-1],
            "min_eig": ev[0],
            "collar_fraction_times_dim": (2 * N + 1) * (L - math.log(2)) / L,
        }


def two_route_atom_dev(c, N: int, dps: int = DPS) -> float:
    """max |atom_matrix + galerkin_prime_block| (the two routes)."""
    with mp.workdps(dps):
        A = atom_matrix(c, N, dps)
        G = galerkin_prime_block(c, N, dps)
        return float(max(abs(A[i, j] + G[i, j]) for i in range(A.rows) for j in range(A.cols)))


# ---------------------------------------------------------------------------
# JSON
# ---------------------------------------------------------------------------


def run_cells(path: Path | None = None) -> dict:
    out = {
        "two_adic_facts": two_adic_facts(5),
        "eta_theta_check": [
            {k: (str(v) if isinstance(v, complex) else v) for k, v in row.items()}
            for row in eta_theta_check()
        ],
        "kappa_exact": str(kappa_exact()),
        "comparison_lemma_trials": comparison_lemma_trials(),
        "shift_form_cells": [shift_form_spectrum(c, N) for c in CELLS_C for N in CELLS_N],
        "atom_two_route_dev": {f"{c}_{N}": two_route_atom_dev(c, N) for c in CELLS_C for N in (8, 16)},
        "theta_gram_atom_dev": [theta_gram_atom_dev(c, 2, 30) for c in CELLS_C],
    }
    if path is not None:
        Path(path).write_text(json.dumps(out, indent=1) + "\n")
    return out



# ---------------------------------------------------------------------------
# 7. the window compression of m: Gram of theta_S on the shared basis
# ---------------------------------------------------------------------------


def theta_gram_quadrature(c, N: int, dps: int = 30):
    """<theta_S U_n, theta_S U_m> by direct quadrature, additive variable.

    In the additive variable x = log u, theta_S g = g - 2^{-1/2} g(. - log 2)
    (w_S theta_S = w_inf - 2^{-1/2} (dilation by 2), CCM Prop 4.6 proof).
    U_n lives on [0, L]; its shift on [log 2, L + log 2].  Independent of
    the closed form in shift_form_matrix.
    """
    with mp.workdps(dps):
        L = mp.log(mp.mpf(c))
        a = mp.log(2)
        r = 1 / mp.sqrt(2)
        ns = list(range(-N, N + 1))

        def U(n, y):
            return mp.expj(2 * mp.pi * n * y / L) / mp.sqrt(L)

        def th(n, y):
            v = mp.mpf(0)
            if 0 <= y <= L:
                v += U(n, y)
            if a <= y <= L + a:
                v -= r * U(n, y - a)
            return v

        pts = sorted({mp.mpf(0), a, L, L + a})
        G = mp.matrix(2 * N + 1)
        for i, n in enumerate(ns):
            for j, m in enumerate(ns):
                G[i, j] = mp.quad(lambda y: th(n, y) * mp.conj(th(m, y)), pts)
        return G


def theta_gram_atom_dev(c, N: int = 2, dps: int = 30) -> dict:
    """Compare Gram(theta_S) with 3/2 I - sqrt2 H and with the galerkin prime block."""
    with mp.workdps(dps):
        G = theta_gram_quadrature(c, N, dps)
        H = shift_form_matrix(c, N, dps)
        P = galerkin_prime_block(c, N, dps)  # = -W_2
        n = 2 * N + 1
        d1 = max(abs(G[i, j] - ((mp.mpf(3) / 2 if i == j else 0) - mp.sqrt(2) * H[i, j]))
                 for i in range(n) for j in range(n))
        d2 = max(abs(P[i, j] - mp.log(2) * (G[i, j] - (mp.mpf(3) / 2 if i == j else 0)))
                 for i in range(n) for j in range(n))
        return {"c": c, "N": N, "dps": dps, "gram_vs_H": float(d1), "prime_block_vs_gram": float(d2)}


if __name__ == "__main__":
    import time

    t0 = time.time()
    res = run_cells(HERE / "cutoff_cells.json")
    print(json.dumps(res, indent=1))
    print("seconds", round(time.time() - t0, 1))
