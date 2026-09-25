"""checker/: properties any correct T_S and R_S = Q - T_S must satisfy.

Written in phase 1, before any code in kernel/ or two_adic/ was read. Each
function returns a measured quantity; the tests decide pass or fail. The
grade of each property's derivation is stated where it is defined.

P1 Hermitian. T_S(f) = Tr(theta_S(f) Pi_S theta_S(f)^*) is a Hermitian form in
   f (linear in f on the left, conjugate-linear on the right), so its matrix
   is Hermitian. Grade: elementary derivation.
P2 Positive semidefinite. Pi_S = S_inf (x) P_2 + 1 (x) (1 - P_2) is an
   orthogonal projection when S_inf and P_2 are (the two ranges are
   orthogonal: (S (x) P)(1 (x) (1 - P)) = S (x) P(1 - P) = 0), and then
   Tr(A Pi A^*) = ||Pi A^*||_HS^2 >= 0 for every A. Grade: elementary
   derivation (theory s7.3 item 2 for the form of Pi_S; s7.1 for the role of
   unitarity, which is what makes theta_S(g * g^*) = theta_S(g) theta_S(g)^*).
P3 Galerkin consistency. A fixed quadratic form on a fixed orthonormal basis
   U_n: the matrix at N is the central principal submatrix of the matrix at
   N' > N. Any N-dependent approximation inside a provider shows up here.
   Grade: elementary derivation.
P4 Interlacing. From P3 and Cauchy interlacing, the number of negative
   eigenvalues of R_S is nondecreasing in N and lambda_min is nonincreasing.
   Grade: elementary derivation.
P5 Bounded rank (C4, theory s7.2). The operational content measured here is
   that n_-(R_S) is the same at N = 8, 16, 32. Grade: this is the candidate's
   prediction, not a theorem; a failure is a finding about C4 on these cells,
   not a defect in a provider.
P6 Place 2 off. The S = {inf} instance of the builder is kernel/'s T_inf
   (Pi_{inf} = S_inf). Grade: definitional.
P7 Connes-Consani arXiv:2006.13771 Thm 6.11 at c in {1.5, 1.9} (support in
   [c^{-1/2}, c^{1/2}] inside [2^{-1/2}, 2^{1/2}]): for g with g-hat(-i/2) = 0,
   W_inf(g * g^*) >= Tr(theta(g) S theta(g)^*) - kappa |g-hat(0)|^2 with
   kappa = 4 gamma / log 2, gamma ~ 2.94355 (their Lemma 6.10, a constant
   they compute numerically). In the mission basis: W_inf(g * g^*) = Q(f)
   for c < 2 on the class (no atom, and the pole term vanishes when
   g-hat(-i/2) = 0), g-hat(0) = L^{1/2} v_0, so on V_- = {row_minus . v = 0}:
   Q - T_inf + kappa L e_0 e_0^T >= 0; and on V_- n {v_0 = 0} (their
   Theorem 1 up to the reflection y -> L - y): Q - T_inf >= 0.
   Grade: the inequality is a published theorem; its transcription to this
   basis (normalisation of W_inf against theory s0, and density of the
   trigonometric basis in their class) is a derivation, unreviewed.
P8 Q positive on the cells. Zhu arXiv:2608.24827 Thm 1.2: lambda*(support 1.6)
   >= 8.9e-18, and lambda* is nonincreasing in the window, so every Galerkin
   minimum on c <= 2.9 < e^{1.6} is >= 8.9e-18. Grade: consequence of a
   cited theorem (normalisation of theory s0 = Zhu eq. (2)-(3)).
"""

from __future__ import annotations

from mpmath import mp

import checker_q as CQ

GAMMA_CC = "2.94355"  # Connes-Consani Lemma 6.10, quoted to the digits printed
ZHU_FLOOR = "8.9e-18"  # Zhu Thm 1.2, lambda*(0.8) in theory s0 normalisation


def kappa_cc(dps: int = 40):
    with mp.workdps(dps):
        return 4 * mp.mpf(GAMMA_CC) / mp.log(2)


# Comparisons run at CMP_DPS whatever the caller's ambient precision is: a
# difference taken at mpmath's default 15 digits would hide everything below
# 1e-15 (this happened once while the tests were being written).
CMP_DPS = 80


def max_abs(M):
    with mp.workdps(CMP_DPS):
        return max(abs(M[i, j]) for i in range(M.rows) for j in range(M.cols))


def hermitian_defect(M):
    """max |M_ij - conj(M_ji)|."""
    with mp.workdps(CMP_DPS):
        return max(
            abs(M[i, j] - mp.conj(M[j, i])) for i in range(M.rows) for j in range(i, M.cols)
        )


def submatrix_defect(M_small, M_big):
    """max |M_small - central block of M_big| (P3)."""
    N_small = (M_small.rows - 1) // 2
    B = CQ.central_block(M_big, N_small)
    with mp.workdps(CMP_DPS):
        return max(abs(M_small[i, j] - B[i, j]) for i in range(B.rows) for j in range(B.cols))


def entry_drift(M_a, M_b):
    """max entrywise difference, e.g. dps 40 against dps 60."""
    with mp.workdps(CMP_DPS):
        return max(abs(M_a[i, j] - M_b[i, j]) for i in range(M_a.rows) for j in range(M_a.cols))


def lowest(M, k: int = 3, dps: int = 40):
    return CQ.eigvals_hermitian(M, dps)[:k]


def class_bases(c, N: int, dps: int = 40) -> dict:
    """Orthonormal bases of the three spaces results are reported on.

    "full": everything; "minus": V_- = {g-hat(-i/2) = 0} (CC Thm 6.11 class);
    "minus_zero": V_- n {v_0 = 0}; "plus_zero": V_+ n {v_0 = 0} (the
    reflected Theorem 1 class, reported as a symmetry check)."""
    rows = CQ.transform_rows(c, N, dps)
    dim = 2 * N + 1
    I = mp.eye(dim)
    return {
        "full": I,
        "minus": CQ.constraint_basis([rows["minus"]], dim, dps),
        "minus_zero": CQ.constraint_basis([rows["minus"], rows["zero"]], dim, dps),
        "plus_zero": CQ.constraint_basis([rows["plus"], rows["zero"]], dim, dps),
    }


def cc611_margins(Q, T_inf, c, N: int, dps: int = 40) -> dict:
    """P7 in the mission basis. Returns lambda_min of
    B^*(Q - T_inf)B + kappa L b b^* on V_- (b = row v_0 of B), lambda_min of
    B^*(Q - T_inf)B on V_- n {v_0 = 0}, and kappa_star, the least kappa that
    makes the first form PSD (when the second is positive definite)."""
    with mp.workdps(dps):
        L = mp.log(mp.mpf(c))
        bases = class_bases(c, N, dps)
        X = CQ.compress(Q - T_inf, bases["minus"], dps)
        b = mp.matrix(1, X.cols)
        for j in range(X.cols):
            b[0, j] = bases["minus"][N, j]
        kap = kappa_cc(dps)
        withrank = X + kap * L * (b.H * b)
        m1 = CQ.eigvals_hermitian(withrank, dps)[0]
        Y = CQ.compress(Q - T_inf, bases["minus_zero"], dps)
        m2 = CQ.eigvals_hermitian(Y, dps)[0]
        Yp = CQ.compress(Q - T_inf, bases["plus_zero"], dps)
        m3 = CQ.eigvals_hermitian(Yp, dps)[0]
        # kappa_star: X + kappa L b^* b >= 0 iff kappa L >= -1/(b X^{-1} b^*)
        # when X restricted to b-perp is positive definite and X is invertible
        kstar = None
        try:
            q = (b * mp.inverse(X) * b.H)[0]
            q = mp.re(q)
            if q < 0:
                kstar = -1 / (L * q)
            else:
                kstar = mp.mpf(0)
        except ZeroDivisionError:
            kstar = None
        return {
            "kappa_cc": kap,
            "min_minus_with_kappa": m1,
            "min_minus_zero": m2,
            "min_plus_zero": m3,
            "kappa_star": kstar,
        }


def pole_identity_defect(P, c, N: int, v, dps: int = 40):
    """|v^* P v - 2 Re(F_+ conj F_-)|, F_+- = int f e^{+-y/2} (P = pole block).

    From g(x) = int f(y) conj f(y - x) dy: int g e^{x/2} = F_+ conj(F_-) and
    int g e^{-x/2} = F_- conj(F_+). Grade: elementary derivation."""
    with mp.workdps(dps):
        rows = CQ.transform_rows(c, N, dps)
        Fp = mp.fsum(rows["plus"][i] * v[i] for i in range(2 * N + 1))
        Fm = mp.fsum(rows["minus"][i] * v[i] for i in range(2 * N + 1))
        vv = mp.matrix(v)
        lhs = (vv.H * P * vv)[0]
        return abs(lhs - 2 * mp.re(Fp * mp.conj(Fm)))
