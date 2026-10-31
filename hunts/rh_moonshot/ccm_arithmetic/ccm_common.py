"""ccm_arithmetic: CCM step 2, the radical construction and its rival tests.

Hunt #150 (``rh_moonshot``), mechanism 1.  Every truncated Weil form used here
is assembled by the validated routines of ``hunts/rogue_frontier/weil_trunc``
(``enclosures.BallTruncation``, Arb balls) and ``hunts/weil_propagation/numerics``
(``wp_common``: sector split, the Epstein (1,1,6) and Dedekind Q(sqrt -23)
blocks).  The one new assembly is the shifted product W_a = zeta(s+a) zeta(s-a)
(``wa_matrix``): two archimedean blocks with digamma parameters 1/4 +- a/2, four
pole vectors and the prime block of Lambda(n)(n^a + n^-a).  Its general-parameter
archimedean routine is checked against BallTruncation's own zeta (1/4) and DH
(3/4) blocks entry by entry, and its pole routine against W02
(``test_ccm_arithmetic.py``).

Conventions (those of weil_trunc).  Window [0, L], L = log c; even sector
e_0 = L^-1/2, e_k = sqrt(2/L) cos(2 pi k y / L); nodes om_k = 2 pi k / L;

    F_v(z) = 2 sin(zL/2) [v_0/z + sum_k sqrt2 v_k z / (z^2 - om_k^2)],

which is sqrt(L) times the Fourier transform of the centred window function,
so F_v(0) = L v_0 and F_v(om_j) = L (-1)^j v_j / sqrt2 for j >= 1.

The radical vector of an L-function X with completed entire function Xi_X:

    r_0 = L^-1/2 Xi_X(0),   r_k = sqrt(2/L) (-1)^k Xi_X(om_k),

the Fourier coefficients of the L-periodisation of the kernel Phi_X whose
Fourier transform is Xi_X (for zeta, Phi(x) = k(e^x) with Connes' k = E(h),
arXiv:2602.04022 s6.2).  F_r interpolates sqrt(L) Xi_X at every node, and the
ratio sequence (v_j / r_j) / (v_0 / r_0) samples F_v / Xi_X at the nodes.
Polynomial-weighted radical vectors r^(j)_k = om_k^(2j) r_k sample
t^(2j) Xi_X(t); they span the radical subspace R_m used by the capture bound.

House rules: mpmath only at explicit dps inside workdps, Arb balls where a
statement needs a sign, nothing written into the tree by import.
"""

from __future__ import annotations

import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
_WPN = os.path.join(ROOT, "hunts", "weil_propagation", "numerics")
_WT = os.path.join(ROOT, "hunts", "rogue_frontier", "weil_trunc")
for _p in (_WPN, _WT, ROOT):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from flint import acb, acb_mat, arb, arb_mat, ctx, fmpq  # noqa: E402
from mpmath import mp  # noqa: E402

import enclosures as EN  # noqa: E402
import galerkin as GK  # noqa: E402
import wp_common as WP  # noqa: E402

KINDS = ("zeta", "dh", "epstein", "dedekind", "wa")
WA_SHIFT = fmpq(1, 4)

# DH off-line zero (zeta.epstein pins 50 digits) and the on-line gap around it
DH_GAMMA_OFF = WP.GAMMA_OFF
DH_DELTA_OFF = WP.DELTA_OFF
DH_GAP = (83.109, 87.647)
# Epstein (1,1,6) off-line zero, measured in weil_propagation (argument principle)
EPSTEIN_OFF = (0.953260474794661, 16.2902157203904)


# ---------------------------------------------------------------------------
# precision policy
# ---------------------------------------------------------------------------


def prec_for(kind: str, c, N: int) -> int:
    """Working precision in bits.  zeta's floor reaches ~1e-141 at (31, 128)
    and lower beyond; the rivals' floors stay above ~1e-60 on this grid."""
    cf = float(WP.cq(c))
    if kind == "zeta":
        if N <= 64:
            return 700 if cf <= 31 else 1100
        return 900 if cf <= 31 else 1600
    return 400 if N <= 128 else 600


# ---------------------------------------------------------------------------
# the archimedean block for a general digamma parameter (W_a needs 3/8, 1/8)
# ---------------------------------------------------------------------------


def _ball_pm(x: arb, eps: arb) -> arb:
    return x + (arb(0).union(eps).union(-eps))


def arch_seqs(c, N: int, a: arb, const: arb, prec: int):
    """(S, archdiag) of the archimedean block with density Re psi(a + i r/2)
    - log q, const = -log q + psi(a): BallTruncation's formulas with the
    parameter a left free (same geometric series, same tail balls)."""
    ctx.prec = prec
    pi = arb.pi()
    L = arb(WP.cq(c)).log()
    z = (-2 * L).exp()
    J = int(math.ceil((prec + 30) * math.log(2) / (2 * float(L)))) + 3
    mus = [2 * (arb(j) + a) for j in range(J)]
    Es = [(-m * L).exp() for m in mus]
    one_minus_z = 1 - z
    tail_int = sum((E / m for m, E in zip(mus, Es)), arb(0))
    tail_int = _ball_pm(tail_int, Es[-1] * z / (mus[-1] * one_minus_z))
    psi_a = acb(a).digamma().real
    S = [arb(0)] * (N + 1)
    Dg = [arb(0)] * (N + 1)
    for k in range(N + 1):
        om = 2 * pi * k / L
        zz = acb(a, om / 2)
        psi0 = zz.digamma()
        psi1 = acb(2).zeta(zz)
        if k == 0:
            sum_cos1 = arb(0)
        else:
            geo = sum((E * om / (m * m + om * om) for m, E in zip(mus, Es)), arb(0))
            geo = _ball_pm(geo, Es[-1] * z * om / (mus[-1] ** 2 * one_minus_z))
            S[k] = psi0.imag / 2 - geo
            geo1 = sum((E * om * om / (m * (m * m + om * om)) for m, E in zip(mus, Es)), arb(0))
            geo1 = _ball_pm(geo1, Es[-1] * z / (mus[-1] * one_minus_z))
            sum_cos1 = -(psi0.real - psi_a) / 2 + geo1
        geox = sum(
            (E * ((m * m - om * om) / (m * m + om * om) ** 2 + m * L / (m * m + om * om)) for m, E in zip(mus, Es)),
            arb(0),
        )
        geox = _ball_pm(geox, Es[-1] * z * (1 + mus[-1] * L) / (mus[-1] ** 2 * one_minus_z))
        sum_xcos = psi1.real / 4 - geox
        Dg[k] = 2 * sum_cos1 - (2 / L) * sum_xcos
    archdiag = [const - Dg[k] + 2 * tail_int for k in range(N + 1)]
    return S, archdiag


def pole_vector(L: arb, N: int, beta: arb) -> list:
    """phi with F_v(i beta) = sum_k phi_k v_k (even sector); a simple pole of
    the completed function at z = +- i beta contributes (2/L) phi phi^T."""
    s2 = arb(2).sqrt()
    pi = arb.pi()
    sh = (beta * L / 2).sinh()
    out = [2 * sh / beta]
    for k in range(1, N + 1):
        om = 2 * pi * k / L
        out.append(2 * s2 * beta * sh / (beta * beta + om * om))
    return out


def pole_block(L: arb, N: int, betas) -> arb_mat:
    n = N + 1
    M = arb_mat(n, n)
    for beta in betas:
        phi = pole_vector(L, N, beta)
        for i in range(n):
            for j in range(n):
                M[i, j] += 2 * phi[i] * phi[j] / L
    return M


def _von_mangoldt_int(q: int):
    """(p, True) if q is a prime power p^k, else (None, False)."""
    for p in range(2, q + 1):
        if q % p == 0:
            m = q
            while m % p == 0:
                m //= p
            return (p, True) if m == 1 else (None, False)
    return (None, False)


def wa_matrix(c, N: int, prec: int, shift=WA_SHIFT) -> arb_mat:
    """Even-sector truncated Weil matrix of W_a = zeta(s+a) zeta(s-a),
    completion xi(s+a) xi(s-a) (zeta.epstein.shifted_completed):
    archimedean Re psi(1/4 + a/2 + ir/2) + Re psi(1/4 - a/2 + ir/2) - 2 log pi,
    poles at s = 1 +- a, +- a (z = +- i(1/2 + a), +- i(1/2 - a)),
    prime weights Lambda(n)(n^a + n^-a) n^-1/2 on prime powers n <= c."""
    c0 = WP.cq(c)
    a = arb(shift)
    bt = EN.BallTruncation(c0, N, kind="zeta", prec=prec)
    ctx.prec = prec
    L = bt.L
    lpi = arb.pi().log()
    blocks = []
    for ai in (arb(1) / 4 + a / 2, arb(1) / 4 - a / 2):
        const = -lpi + acb(ai).digamma().real
        S, d = arch_seqs(c0, N, ai, const, prec)
        blocks.append(WP.sector_matrix(bt, "even", S=S, archdiag=d))
    coeffs = []
    for q in range(2, int(math.floor(float(c0) + 1e-12)) + 1):
        p, ok = _von_mangoldt_int(q)
        if not ok:
            continue
        lam = arb(p).log() * (arb(q) ** a + arb(q) ** (-a))
        coeffs.append((arb(q).log(), lam / arb(q).sqrt(), q))
    P, R = WP._prime_seqs(bt, coeffs)
    ctx.prec = prec
    M = blocks[0] + blocks[1] + WP.sector_matrix(bt, "even", P=P, R=R)
    M = M + pole_block(L, N, [arb(1) / 2 + a, arb(1) / 2 - a])
    return M


# ---------------------------------------------------------------------------
# the five matrices
# ---------------------------------------------------------------------------


def window_L(c, prec: int | None = None) -> arb:
    if prec:
        ctx.prec = prec
    return arb(WP.cq(c)).log()


def matrix(kind: str, c, N: int, prec: int | None = None) -> arb_mat:
    """Even-sector truncated Weil matrix (Arb balls) at exact window c."""
    prec = prec or prec_for(kind, c, N)
    if kind in ("zeta", "dh"):
        return WP.build(c, N, kind, prec)[1]
    if kind == "epstein":
        return WP.epstein_matrices(c, N, prec)["even"]
    if kind == "dedekind":
        return WP.epstein_matrices(c, N, prec, form="dedekind-23")["even"]
    if kind == "wa":
        return wa_matrix(c, N, prec)
    raise ValueError(kind)


# ---------------------------------------------------------------------------
# completed functions Xi_X(z) = Lambda_X(1/2 + i z), entire
# ---------------------------------------------------------------------------


def _chi_m23(n: int) -> int:
    """Kronecker symbol (-23 / n).  For a fundamental discriminant D = 1 mod 4
    it equals the Jacobi symbol (n / |D|), so chi(n) = (n mod 23 / 23); this
    gives chi(2) = chi(3) = 1 (split) and chi(5) = -1 (inert), as the
    weil_propagation check K records."""
    from sympy import jacobi_symbol

    r = n % 23
    return 0 if r == 0 else int(jacobi_symbol(r, 23))


def xi_kind(kind: str, z, dps: int = 30):
    """Xi_X(z) for complex z (mpc).  Normalisation is irrelevant here: every
    comparison divides by the value at 0.  The working precision grows with
    |Re z| because Xi_X decays like exp(-pi d |t| / 4) (degree d)."""
    from zeta.core import xi
    from zeta import epstein as EP

    z = mp.mpc(z)
    t = abs(float(mp.re(z)))
    if kind in ("zeta", "dh", "wa"):
        w = dps + int(0.35 * t) + 10
    else:
        w = dps + int(0.70 * t) + 10
    with mp.workdps(w):
        s = mp.mpf(1) / 2 + 1j * z
        if kind == "zeta":
            val = xi(s, dps=w)
        elif kind == "dh":
            val = EP.completed_dh(s, dps=w)
        elif kind == "wa":
            val = EP.shifted_completed(s, shift=mp.mpf(1) / 4, dps=w)
        elif kind == "epstein":
            val = s * (s - 1) * EP.epstein_completed(s, (1, 1, 6), dps=w)
        elif kind == "dedekind":
            q = mp.mpf(23)
            lval = mp.dirichlet(s, [_chi_m23(n) for n in range(23)])
            val = s * (s - 1) * (mp.sqrt(q) / (2 * mp.pi)) ** s * mp.gamma(s) * mp.zeta(s) * lval
        else:
            raise ValueError(kind)
        return +val


def xi_real(kind: str, t, dps: int = 30):
    """Xi_X(t) for real t, imaginary residue discarded (checked small)."""
    v = xi_kind(kind, mp.mpf(t), dps)
    with mp.workdps(dps + 10):
        if mp.im(v) != 0 and abs(mp.im(v)) > abs(mp.re(v)) * mp.mpf(10) ** (-(dps // 2)) + mp.mpf(10) ** (-dps):
            raise ValueError(f"Xi_{kind}({t}) not real: {v}")
        return mp.re(v)


# ---------------------------------------------------------------------------
# eigenpairs
# ---------------------------------------------------------------------------


def _col(vals) -> arb_mat:
    return arb_mat(len(vals), 1, list(vals))


def _dot(x: arb_mat, y: arb_mat) -> arb:
    return sum((x[i, 0] * y[i, 0] for i in range(x.nrows())), arb(0))


def _mid_unit(y: arb_mat) -> arb_mat:
    nrm = _dot(y, y).sqrt()
    return arb_mat(y.nrows(), 1, [(y[i, 0] / nrm).mid() for i in range(y.nrows())])


def lowest_pairs(A: arb_mat, k: int = 4, refine: int = 2):
    """Lowest k eigenpairs of the symmetric ball matrix A.

    Approximate QR eigen-decomposition of the midpoint matrix (python-flint,
    algorithm "approx") locates every eigenvalue, negative ones included;
    each of the k lowest is then refined by shifted inverse iteration at the
    working precision.  Returns [(rq_ball, unit column with exact midpoints)],
    ascending; the first vector is signed so that v_0 > 0.  The Rayleigh
    quotient balls are honest for the returned vectors; whether they bracket
    the true eigenvalues is a separate (Temple) question.
    """
    n = A.nrows()
    Am = A.mid()
    E, R = acb_mat(Am).eig(right=True, algorithm="approx")
    order = sorted(range(n), key=lambda i: float(E[i].real.mid()))
    out = []
    for idx in order[:k]:
        lam = E[idx].real.mid()
        x = _mid_unit(arb_mat(n, 1, [R[r, idx].real.mid() for r in range(n)]))
        for _ in range(refine):
            sh = arb_mat(n, n, [lam if i == j else 0 for i in range(n) for j in range(n)])
            try:
                y = (Am - sh).solve(x, algorithm="approx")
            except Exception:
                break
            for _, v in out:
                y = y - v * _dot(v, y).mid()
            x = _mid_unit(y)
            lam = (_dot(x, Am * x)).mid()
        out.append([_dot(x, A * x) / _dot(x, x), x])
    if out and out[0][1][0, 0] < 0:
        x = out[0][1]
        out[0][1] = arb_mat(n, 1, [-x[i, 0] for i in range(n)])
    return [(rq, x) for rq, x in out]


def residual(A: arb_mat, x: arb_mat, rho: arb) -> str:
    """Upper bound on ||A x - rho x|| from the entrywise ball magnitudes
    (summed in Arb: the squares underflow a float)."""
    r = A * x - x * rho
    s = sum((abs(r[i, 0]).upper() ** 2 for i in range(r.nrows())), arb(0))
    return s.sqrt().upper().str(4, radius=False)


# ---------------------------------------------------------------------------
# the entire transform, radical vectors, ratio profiles
# ---------------------------------------------------------------------------


def to_mp(x: arb_mat) -> list:
    """Column of arb midpoints -> list of mpf at the current mp precision."""
    return [mp.mpf(x[i, 0].mid().str(int(mp.dps) + 20, radius=False)) for i in range(x.nrows())]


def c_mp(c):
    q = WP.cq(c)
    return mp.mpf(int(q.p)) / int(q.q)


def L_mp(c):
    return mp.log(c_mp(c))


def F_mp(v: list, L, z):
    """F_v(z) in mpmath (v as mpf list); z complex, not 0 or a node."""
    z = mp.mpc(z)
    s = v[0] / z
    s2 = mp.sqrt(2)
    for k in range(1, len(v)):
        om = 2 * mp.pi * k / L
        s += s2 * v[k] * z / (z * z - om * om)
    return 2 * mp.sin(z * L / 2) * s


def F_at0(v: list, L):
    return L * v[0]


def radical_vector(kind: str, c, N: int, power: int = 0, dps: int = 30, cache: dict | None = None):
    """r^(power): r_k = sqrt(2/L) (-1)^k om_k^(2 power) Xi_X(om_k), r_0 =
    L^-1/2 Xi_X(0) (power 0) or 0 (power > 0).  mpf list at dps."""
    with mp.workdps(dps + 10):
        L = L_mp(c)
        vals = []
        for k in range(N + 1):
            om = 2 * mp.pi * k / L
            key = (kind, str(WP.cq(c)), k)
            if cache is not None and key in cache:
                xv = cache[key]
            else:
                xv = xi_real(kind, om, dps)
                if cache is not None:
                    cache[key] = xv
            if k == 0:
                vals.append(xv / mp.sqrt(L) if power == 0 else mp.mpf(0))
            else:
                vals.append(mp.sqrt(2 / L) * (-1) ** k * om ** (2 * power) * xv)
        return vals


def overlap_misfit(v: list, r: list):
    """1 - cos^2(v, r) in mpmath."""
    vv = mp.fsum(x * x for x in v)
    rr = mp.fsum(x * x for x in r)
    vr = mp.fsum(x * y for x, y in zip(v, r))
    return 1 - vr * vr / (vv * rr)


def ratio_profile(v: list, r: list, jmax: int):
    """rho_j = (v_j / r_j) / (v_0 / r_0) = (F_v/Xi)(om_j) / (F_v/Xi)(0)."""
    base = v[0] / r[0]
    return [(v[j] / r[j]) / base for j in range(jmax + 1)]


def project_residual(v: list, basis: list):
    """Squared distance of the unit vector v from span(basis) (mpmath,
    modified Gram-Schmidt twice)."""
    qs = []
    for b in basis:
        y = list(b)
        for _ in range(2):
            for q in qs:
                d = mp.fsum(a * bq for a, bq in zip(y, q))
                y = [a - d * bq for a, bq in zip(y, q)]
        nrm = mp.sqrt(mp.fsum(a * a for a in y))
        qs.append([a / nrm for a in y])
    nv = mp.sqrt(mp.fsum(a * a for a in v))
    u = [a / nv for a in v]
    proj2 = mp.fsum(mp.fsum(a * q for a, q in zip(u, qq)) ** 2 for qq in qs)
    return 1 - proj2, qs


def real_zeros(fun, t0, t1, step):
    """Sign-change zeros of a real function on [t0, t1], bisected."""
    zs = []
    t = mp.mpf(t0)
    f0 = fun(t)
    while t < t1:
        t2 = t + step
        f1 = fun(t2)
        if f0 == 0:
            zs.append(t)
        elif f0 * f1 < 0:
            lo, hi, flo = t, t2, f0
            for _ in range(80):
                mid = (lo + hi) / 2
                fm = fun(mid)
                if flo * fm <= 0:
                    hi = mid
                else:
                    lo, flo = mid, fm
            zs.append((lo + hi) / 2)
        t, f0 = t2, f1
    return zs
