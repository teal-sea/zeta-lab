"""P_2 through E_S on the shared CCM basis: matrix entries, closed form.

Shared basis (mission MISSION.md): U_n(y) = L^{-1/2} exp(2 pi i n y / L) on
[0, L], n = -N .. N, L = log c; index 0 of a matrix is n = -N. A quadratic
form F is delivered as the matrix M with F(f) = v^* M v for f = sum v_n U_n.
The inner product is conjugate linear in its first slot.

The semilocal objects (CCM arXiv:2310.18423 s4, S = {inf, 2}, p = 2), in the
multiplicative picture L^2(X_S)^{K_S} = L^2(R*_+, d*u) (their w_S, eq. (42)),
written in the log variable y:

* D, the dilation by 2: (D h)(y) = h(y - log 2). This is CCM's g(l) -> g(l/p)
  (proof of Prop 4.6 (ii)); it is unitary on L^2(R, dy) and its Mellin
  multiplier is 2^{-is}.
* theta_S, the class of sigma_2 (x) f (sigma_2 the open-ball 2-adic Sonin
  vector, CCM Prop 4.5): Theta_alpha = 1 - alpha 2^{-1/2} D, Mellin
  multiplier 1 - alpha 2^{-1/2 - is} (CCM (57)-(58), alpha = 1 there; one
  factor per Satake parameter alpha in general).
* eta_S = E_S, the class of 1_{Z_2} (x) f (the closed ball, i.e. the time
  limiting P_2 of theory s7.3): E_S = sum_{k >= 0} (alpha 2^{-1/2})^k D^{-k},
  Mellin multiplier L_2(1/2 - is) (CCM (46)-(47)).

On a window of length L the shift correlation <f, D^k f> vanishes as soon as
k log 2 >= L. For 2 < c < 4 only k = 0, +-1 survive, so every Gram form of
theta_S or E_S on window functions is a combination of the identity and of
the single matrix

    C_{mn} := <U_m, D U_n>     (closed form below).

That matrix is also the Weil prime block at 2: Wp = (log 2 / sqrt 2)(C + C^*)
(pinned against the CCM prime block of hunts/rogue_frontier/weil_trunc).
Hence, for unitary alpha and 2 < c < 4,

    -Wp_alpha = log 2 * (M_theta(alpha) - (3/2) I)     (exact identity),

where M_theta(alpha) is the Gram matrix of Theta_alpha on the window basis:
the 2-adic atom of the Weil form is the failure of the Sonin map theta_S to
be a multiple of an isometry on window functions. Grade: exact algebra from
the closed form of C, with the closed form and the identity measured against
direct quadrature and against the independent galerkin.py prime block.
"""

from __future__ import annotations

import importlib.util
import os

from mpmath import mp

__all__ = [
    "shift_corr",
    "shift_corr_quad",
    "theta_gram",
    "es_gram",
    "es_gram_series",
    "prime_block_from_C",
    "galerkin_prime_block",
    "identity_defect",
]

_HERE = os.path.dirname(os.path.abspath(__file__))
_GALERKIN = os.path.normpath(
    os.path.join(_HERE, "..", "..", "..", "rogue_frontier", "weil_trunc", "galerkin.py")
)


def _ns(N: int) -> list[int]:
    return list(range(-N, N + 1))


def shift_corr(c, N: int, dps: int = 40, k: int = 1):
    """C^{(k)}_{mn} = <U_m, D^k U_n> for k >= 1, closed form.

    With h = k log 2 and 0 < h < L:
      m = n : exp(-2 pi i n h / L) (L - h) / L
      m != n: exp(-2 pi i n h / L) (1 - exp(2 pi i (n - m) h / L)) / (2 pi i (n - m))
    and the zero matrix when h >= L (no overlap of the window with its shift).
    """
    with mp.workdps(dps + 10):
        L = mp.log(mp.mpf(c))
        h = k * mp.log(2)
        ns = _ns(N)
        M = mp.matrix(len(ns))
        if h >= L:
            return M
        twopi_i = 2j * mp.pi
        for i, m in enumerate(ns):
            for j, n in enumerate(ns):
                ph = mp.exp(-twopi_i * n * h / L)
                if m == n:
                    M[i, j] = ph * (L - h) / L
                else:
                    M[i, j] = ph * (1 - mp.exp(twopi_i * (n - m) * h / L)) / (twopi_i * (n - m))
        with mp.workdps(dps):
            return M * 1


def shift_corr_quad(c, m: int, n: int, dps: int = 40, k: int = 1):
    """<U_m, D^k U_n> by direct quadrature (independent route for tests)."""
    with mp.workdps(dps + 10):
        L = mp.log(mp.mpf(c))
        h = k * mp.log(2)
        if h >= L:
            return mp.mpc(0)
        f = lambda y: mp.exp(-2j * mp.pi * m * y / L) * mp.exp(2j * mp.pi * n * (y - h) / L) / L
        val = mp.quad(f, mp.linspace(h, L, 2 + abs(m) + abs(n)))
        with mp.workdps(dps):
            return +val


def _alphas(alphas, dps):
    with mp.workdps(dps):
        return [mp.mpc(a) for a in alphas]


def theta_gram(c, N: int, alphas=(1,), dps: int = 40):
    """sum_j Gram(Theta_{alpha_j}) on the window basis, 2 < c < 4.

    Gram(Theta_alpha) = (1 + |alpha|^2 / 2) I - 2^{-1/2} (alpha C + conj(alpha) C^*),
    from ||f - a D f||^2 = (1 + |a|^2) ||f||^2 - a <f, Df> - conj(a) <Df, f>
    with a = alpha 2^{-1/2}, <f, D f> = v^* C v and ||D f|| = ||f||.
    """
    if not (2 < float(c) < 4):
        raise ValueError("the three-term form needs 2 < c < 4")
    with mp.workdps(dps):
        C = shift_corr(c, N, dps)
        Ch = C.H
        n = C.rows
        G = mp.matrix(n)
        for a in _alphas(alphas, dps):
            G += (1 + abs(a) ** 2 / 2) * mp.eye(n) - (a * C + mp.conj(a) * Ch) / mp.sqrt(2)
        return G


def es_gram(c, N: int, alphas=(1,), dps: int = 40):
    """sum_j Gram(E_S, alpha_j) on the window basis, 2 < c < 4, closed form.

    ||E_S f||^2 = <f, |L_2|^2(D) f> with, for |alpha| = 1 and a = alpha 2^{-1/2},
    1 / |1 - a z|^2 = (1 / (1 - |a|^2)) sum_k a^k z^k (k >= 0), conj(a)^|k| z^k (k < 0)
    on |z| = 1. Only k = 0, +-1 survive on these windows:
    Gram = 2 I + 2 * 2^{-1/2} (conj(alpha) C + alpha C^*)
    (the sign pattern is the one checked by es_gram_series).
    """
    if not (2 < float(c) < 4):
        raise ValueError("the three-term form needs 2 < c < 4")
    with mp.workdps(dps):
        C = shift_corr(c, N, dps)
        Ch = C.H
        n = C.rows
        G = mp.matrix(n)
        for a in _alphas(alphas, dps):
            if abs(abs(a) - 1) > mp.mpf(10) ** (-dps + 5):
                raise ValueError("es_gram closed form is for unitary alpha")
            G += 2 * mp.eye(n) + mp.sqrt(2) * (mp.conj(a) * C + a * Ch)
        return G


def es_gram_series(c, N: int, alpha=1, dps: int = 40, kmax: int = 60):
    """Gram of E_S = sum_{k>=0} (alpha 2^{-1/2})^k D^{-k} by its operator series.

    Independent route: expands ||E_S f||^2 = sum_{k,l} conj(a)^k a^l <D^{-k} f, D^{-l} f>
    and uses <D^{-k} f, D^{-l} f> = <f, D^{k-l} f>, truncated at kmax (the
    tail is below (1/2)^kmax relative).
    """
    with mp.workdps(dps + 10):
        a = mp.mpc(alpha) / mp.sqrt(2)
        C = shift_corr(c, N, dps + 10)  # D^{+1}
        n = C.rows
        # coefficient of <f, D^j f> for j = -1, 0, 1 (others vanish on the window)
        coef = {-1: mp.mpc(0), 0: mp.mpc(0), 1: mp.mpc(0)}
        for kk in range(kmax + 1):
            for ll in range(kmax + 1):
                j = kk - ll
                if j in coef:
                    coef[j] += mp.conj(a) ** kk * a**ll
        G = coef[0] * mp.eye(n) + coef[1] * C + coef[-1] * C.H
        with mp.workdps(dps):
            return G * 1


def prime_block_from_C(c, N: int, alphas=(1,), dps: int = 40):
    """Wp_alpha = (log 2 / sqrt 2) sum_j (alpha_j C + conj(alpha_j) C^*) on 2 < c < 4.

    For real alpha (zeta: (1,), Dedekind Q(sqrt -23): (1, 1)) this is the CCM
    prime block restricted to the atom n = 2 (Lambda(2) 2^{-1/2} q_nm(log 2)),
    times the number of parameters. The orientation for complex alpha is the
    convention of this module (the one that makes the atom weight match the
    Mellin multiplier 1 - alpha 2^{-1/2 - is} of Theta_alpha); it is not used
    for any mission cell.
    """
    with mp.workdps(dps):
        C = shift_corr(c, N, dps)
        n = C.rows
        W = mp.matrix(n)
        for a in _alphas(alphas, dps):
            W += (a * C + mp.conj(a) * C.H)
        return W * (mp.log(2) / mp.sqrt(2))


def _load_galerkin():
    spec = importlib.util.spec_from_file_location("_ta_weil_trunc_galerkin", _GALERKIN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def galerkin_prime_block(c, N: int, dps: int = 40):
    """The CCM prime block Wp(n, m) as implemented in weil_trunc/galerkin.py.

    Read from its Truncation object (sequences _P, _R): off-diagonal
    (P_m - P_n) / (pi (n - m)), diagonal R_|n|, i.e. Lambda(q) q^{-1/2} q_nm(log q)
    summed over prime powers q <= c. Independent implementation of the same
    block; on 2 < c < 3 only q = 2 contributes.
    """
    G = _load_galerkin()
    with mp.workdps(dps):
        T = G.Truncation(mp.mpf(c), N, kind="zeta")
        ns = _ns(N)
        W = mp.matrix(len(ns))
        sg = lambda seq, k: seq[k] if k >= 0 else -seq[-k]
        for i, n in enumerate(ns):
            for j, m in enumerate(ns):
                if n == m:
                    W[i, j] = T._R[abs(n)]
                else:
                    W[i, j] = (sg(T._P, m) - sg(T._P, n)) / (mp.pi * (n - m))
        return W


def identity_defect(c, N: int, alphas=(1,), dps: int = 40):
    """max |(-Wp_alpha) - log 2 (Gram(Theta) - sum_j (1 + |alpha_j|^2/2) I)| entrywise."""
    with mp.workdps(dps):
        Wp = prime_block_from_C(c, N, alphas, dps)
        G = theta_gram(c, N, alphas, dps)
        n = G.rows
        shift = sum((1 + abs(a) ** 2 / 2) for a in _alphas(alphas, dps))
        R = -Wp - mp.log(2) * (G - shift * mp.eye(n))
        return max(abs(R[i, j]) for i in range(n) for j in range(n))
