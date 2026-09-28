"""The place 2 alone: time limiting, frequency limiting and Sonin space on Q_2.

Exact rational arithmetic on the Z_2^*-invariant (radial) sector of L^2(Q_2).
Everything here is a finite computation with ``fractions.Fraction``.

Conventions (CCM arXiv:2310.18423 s4.5, with p = 2):

* additive character e_2 trivial on Z_2, self-dual Haar measure, vol(Z_2) = 1;
* B_r := 1_{|x|_2 <= 2^r} (a ball), vol(B_r) = 2^r, so <B_r, B_s> = 2^min(r, s);
* eps_n := 1_{|x|_2 = 2^n} = B_n - B_{n-1}, the shells of CCM (56);
* Fourier transform F(B_r) = 2^r B_{-r}. This is the finite form of CCM (56)
  and it is exact on the span V_K of {B_r : |r| <= K}, which F maps onto itself.

What is checked here, against theory RESULTS s7.3 item 2 ("1_{Z_p} is its own
Fourier transform, so time and frequency limiting to Z_p are the same
projection P_p"):

* P_2 := multiplication by B_0 = 1_{Z_2} (time limiting to Z_2);
* Phat_2 := F P_2 F^{-1} = convolution with 1_{Z_2} (frequency limiting).

They are different projections. They commute, and their product is the rank
one projection onto 1_{Z_2}. With the closed ball |x|_2 <= 1 they join to the
whole radial sector, so the closed-ball local Sonin space is {0}. With the
open ball |x|_2 < 1 (the convention of CCM Definition 4.4) the local Sonin
space is the line spanned by sigma_2 = eps_0 - eps_1 / 2 (CCM Prop 4.5).
"""

from __future__ import annotations

from fractions import Fraction

import sympy

__all__ = [
    "ball_basis",
    "gram",
    "fourier",
    "time_limit",
    "freq_limit",
    "shell",
    "sigma2",
    "sonin_dimension",
    "local_report",
]


def ball_basis(K: int) -> list[int]:
    """Radii r = -K ... K of the ball basis B_r of V_K."""
    return list(range(-K, K + 1))


def _idx(K: int, r: int) -> int:
    return r + K


def gram(K: int) -> sympy.Matrix:
    """Gram matrix <B_r, B_s> = 2^min(r, s) on V_K (exact)."""
    rs = ball_basis(K)
    return sympy.Matrix(len(rs), len(rs), lambda i, j: sympy.Rational(2) ** min(rs[i], rs[j]))


def _op(K: int, image) -> sympy.Matrix:
    """Matrix (columns = images of B_r) of a linear map given on balls."""
    n = 2 * K + 1
    M = sympy.zeros(n, n)
    for r in ball_basis(K):
        for s, coef in image(r).items():
            M[_idx(K, s), _idx(K, r)] += coef
    return M


def fourier(K: int) -> sympy.Matrix:
    """F(B_r) = 2^r B_{-r}: exact, and F maps V_K onto V_K."""
    return _op(K, lambda r: {-r: sympy.Rational(2) ** r})


def time_limit(K: int, radius: int = 0) -> sympy.Matrix:
    """Multiplication by B_radius: B_r -> B_min(r, radius).

    radius = 0 is the closed unit ball Z_2; radius = -1 is the open unit ball
    {|x|_2 < 1} = 2 Z_2.
    """
    return _op(K, lambda r: {min(r, radius): sympy.Integer(1)})


def freq_limit(K: int, radius: int = 0) -> sympy.Matrix:
    """F o time_limit(radius) o F^{-1}; on radial functions F^{-1} = F."""
    F = fourier(K)
    return F * time_limit(K, radius) * F


def shell(K: int, n: int) -> sympy.Matrix:
    """Coordinates of eps_n = B_n - B_{n-1} in the ball basis (|n| < K)."""
    v = sympy.zeros(2 * K + 1, 1)
    v[_idx(K, n)] += 1
    v[_idx(K, n - 1)] -= 1
    return v


def sigma2(K: int) -> sympy.Matrix:
    """sigma_2 = eps_0 - eps_1 / 2 (CCM Prop 4.5 with p = 2)."""
    return shell(K, 0) - shell(K, 1) / 2


def sonin_dimension(K: int, radius: int) -> tuple[int, list]:
    """dim of {f in V_K : P f = 0 and Phat f = 0} for the ball of this radius.

    Returns the dimension and a basis of the kernel (exact vectors). V_K is
    invariant under both projections, so the kernel inside V_K is the
    truncation of the radial local Sonin space, not an artefact of it:
    the proof in CCM Prop 4.5 is exactly this computation.
    """
    A = time_limit(K, radius).col_join(freq_limit(K, radius))
    ker = A.nullspace()
    return len(ker), ker


def _is_orth_projection(P: sympy.Matrix, G: sympy.Matrix) -> bool:
    """P^2 = P and P self-adjoint for the inner product with Gram G."""
    return (P * P - P).is_zero_matrix and (G * P - P.T * G).is_zero_matrix


def local_report(K: int = 6) -> dict:
    """Every exact local statement used in RESULTS.md, as a dict of strings."""
    G = gram(K)
    F = fourier(K)
    I = sympy.eye(2 * K + 1)
    P = time_limit(K, 0)
    Ph = freq_limit(K, 0)
    one = sympy.zeros(2 * K + 1, 1)
    one[_idx(K, 0)] = 1  # B_0 = 1_{Z_2}
    rank1 = one * (one.T * G) / (one.T * G * one)[0, 0]
    dim_closed, _ = sonin_dimension(K, 0)
    dim_open, ker_open = sonin_dimension(K, -1)
    s = sigma2(K)
    # sigma_2 spans the open-ball kernel: rank of [ker | sigma_2] stays 1
    span_ok = dim_open == 1 and sympy.Matrix.hstack(ker_open[0], s).rank() == 1
    eps0 = shell(K, 0)
    return {
        "K": K,
        "F_unitary": (F.T * G * F - G).is_zero_matrix,
        "F_squared_is_identity": (F * F - I).is_zero_matrix,
        "F_fixes_one_Z2": (F * one - one).is_zero_matrix,
        "F_fixes_sigma2": (F * s - s).is_zero_matrix,
        "F_moves_eps0": not (F * eps0 - eps0).is_zero_matrix,
        "P2_is_orth_projection": _is_orth_projection(P, G),
        "Phat2_is_orth_projection": _is_orth_projection(Ph, G),
        "P2_equals_Phat2": (P - Ph).is_zero_matrix,
        "P2_Phat2_commute": (P * Ph - Ph * P).is_zero_matrix,
        "P2_Phat2_is_rank_one_onto_one_Z2": (P * Ph - rank1).is_zero_matrix,
        # P v Phat = P + Phat - P Phat for commuting projections
        "P2_join_Phat2_is_identity": (P + Ph - P * Ph - I).is_zero_matrix,
        "closed_ball_sonin_dim": dim_closed,
        "open_ball_sonin_dim": dim_open,
        "open_ball_sonin_spanned_by_sigma2": bool(span_ok),
        "norm_sq_sigma2": str((s.T * G * s)[0, 0]),
        "norm_sq_one_Z2": str((one.T * G * one)[0, 0]),
    }


if __name__ == "__main__":  # pragma: no cover
    for k, v in local_report().items():
        print(f"{k}: {v}")
