"""The semilocal time-frequency operator P F_S P is not Hilbert-Schmidt.

Multiplicative picture L^2(R*_+, d*u), even sector, lambda = 1. The
archimedean Fourier transform has kernel K(uv) with K(t) = 2 t^{1/2} cos(2 pi t)
(w.r.t. d*v), P restricts to u <= 1, and D is the dilation by 2. By CCM
arXiv:2310.18423 Prop 4.7 (i), F_S = Theta F Theta^{-1} = U_2 F with
U_2 = Theta Theta^{*-1} = -a D + (1 - a^2) sum_{j >= 0} a^j D^{-j},
a = alpha 2^{-1/2}. Hence

    P F_S P = sum_{j >= -1} c_j A_j,   A_j := P D^{-j} F P  (kernel K(2^j u v)),
    c_{-1} = -a,  c_j = (1 - a^2) a^j  (j >= 0).

Exact HS inner products (substituting t = u v, int_0^1 int_0^1 phi(uv) du dv
= int_0^1 phi(t) (-log t) dt, and int_0^1 cos(w t)(-log t) dt = Si(w)/w):

    <A_j, A_l>_HS = 2 * 2^{(j+l)/2} [S(2 pi |2^j - 2^l|) + S(2 pi (2^j + 2^l))],
    S(w) = Si(w) / w, S(0) = 1.

The diagonal terms of ||sum c_j A_j||^2 are c_j^2 <A_j, A_j> = (1/2)(1 + O(2^-j))
for alpha = 1, so the partial sums HS2(K) (Euler levels j <= K) grow by about
1/2 per level. Grade: closed form (ordinary argument, unreviewed) with the
partial sums measured at dps 30. Consequence: unlike the archimedean
P Phat P (trace 2.2375...), the semilocal P Phat^S P is not trace class; its
eigenvalues do not decay super-exponentially, so a truncation of the
semilocal Sonin data by prolate concentration does not converge, and any
truncation has to be by Mellin band.
"""

from __future__ import annotations

from mpmath import mp

__all__ = ["hs_inner", "hs2_partial", "hs2_archimedean"]


def _S(w):
    return mp.mpf(1) if w == 0 else mp.si(w) / w


def hs_inner(j: int, l: int):
    """<A_j, A_l>_HS in closed form."""
    two = mp.mpf(2)
    d = 2 * mp.pi * abs(two**j - two**l)
    s = 2 * mp.pi * (two**j + two**l)
    return 2 * two ** (mp.mpf(j + l) / 2) * (_S(d) + _S(s))


def hs2_partial(K: int, alpha=1, dps: int = 30):
    """||sum_{j=-1}^{K} c_j A_j||_HS^2 (real alpha)."""
    with mp.workdps(dps):
        a = mp.mpf(alpha) / mp.sqrt(2)
        idx = list(range(-1, K + 1))
        c = {j: (-a if j == -1 else (1 - a * a) * a**j) for j in idx}
        tot = mp.mpf(0)
        for j in idx:
            for l in idx:
                tot += c[j] * c[l] * hs_inner(j, l)
        return +tot


def hs2_archimedean(dps: int = 30):
    """||P F P||_HS^2 = Tr(P Phat P), even sector, lambda = 1."""
    with mp.workdps(dps):
        return +hs_inner(0, 0)
