"""P-local rivals: self-dual combinations of two Dirichlet L-functions that agree
with an Euler product at every prime up to P.

The construction (MISSION.md).  Let q = 1 (mod 4) be prime, chi the character mod
q of order 4 with chi(g) = i at the least primitive root g, a in {0, 1} its parity
(chi(-1) = (-1)^a), and

    Lambda(s, chi) = (q/pi)^{(s+a)/2} Gamma((s+a)/2) L(s, chi).

Classically Lambda(s, chi) = eps Lambda(1-s, chi-bar) with eps = tau(chi) /
(i^a sqrt q), |eps| = 1, eps = e^{i theta}, theta in (-pi, pi].  Put

    c = (1 - i k)/2,   F_k(s) = c L(s, chi) + conj(c) L(s, chi-bar),
    G_k(s) = c Lambda(s, chi) + conj(c) Lambda(s, chi-bar).

G_k(s) - G_k(1-s) is linear in k, so one linear solve at one point gives the k
that makes G_k self-dual, exactly as ``zeta.epstein._kappa_cached`` derives kappa;
:func:`k_linear_solve` does that and then checks the same k at an unrelated point.
Matching the coefficients of the two independent completed L-functions in
G(s) = G(1-s) gives k = tan(theta/2), so F_k is eps^{-1/2} L + eps^{1/2} L-bar
divided by 2 cos(theta/2): the normalisation a_1 = 1 exists exactly when
cos(theta/2) != 0.  :func:`k_from_gauss` computes tan(theta/2) from the Gauss sum,
a second route that shares nothing with the linear solve but the character table,
and :func:`jacobi_check` records why theta = pi cannot occur for order 4.

Coefficients.  b(n) = 2 Re(c chi(n)) = Re chi(n) + k Im chi(n), periodic mod q.

The factorisation behind the P-local identities (ordinary argument, checked in
exact arithmetic by :func:`exact_identity_report`).  chi(p)^2 is the Legendre
symbol, so chi(p) is real exactly at the quadratic residues p.  At such p,
chi-bar(p) = chi(p), so the Euler factors of L(s, chi) and L(s, chi-bar) at p
coincide and

    F_k(s) = L_QR(s, chi) * [ c L_NR(s, chi) + conj(c) L_NR(s, chi-bar) ],

with L_QR, L_NR the Euler products over residue and non-residue primes.  Hence
F_k has the exact Euler factor of L(s, chi) at every quadratic-residue prime, and
-F'/F has coefficients Lambda(n) chi(n) at every n except those n > 1 coprime to q
whose prime factors are all non-residues.  If every prime p <= P is a residue,
every P-smooth n is in the agreement set, b(n) = chi(n) there, and the unnormalised
coefficients are 2 cos(theta/2) chi(n): the statement in MISSION.md.

House rules: mpmath with explicit dps through ``mp.workdps``, guard digits
internal, no global mpmath state left modified.  Grades are stated where numbers
are made; nothing here is a result (``hunts/README.md``).
"""

from __future__ import annotations

import math
import os
import sys
from fractions import Fraction
from functools import lru_cache

from mpmath import fp, mp

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
WEIL_TRUNC = os.path.join(REPO, "hunts", "rogue_frontier", "weil_trunc")
for _p in (REPO, WEIL_TRUNC):
    if _p not in sys.path:
        sys.path.insert(0, _p)

#: The two cases of MISSION.md, q -> P (every prime p <= P is a square mod q).
CASES = {17: 2, 73: 4}

#: Guard digits carried internally.
_GUARD = 10


# ---------------------------------------------------------------------------
# exact arithmetic: primes, residues, the order-4 character
# ---------------------------------------------------------------------------


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def primes_upto(n: int) -> list[int]:
    """All primes <= n, by an exact sieve."""
    if n < 2:
        return []
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def factorize(n: int) -> dict[int, int]:
    """{p: e} with n = prod p^e, by trial division."""
    out: dict[int, int] = {}
    m = n
    p = 2
    while p * p <= m:
        while m % p == 0:
            out[p] = out.get(p, 0) + 1
            m //= p
        p += 1 if p == 2 else 2
    if m > 1:
        out[m] = out.get(m, 0) + 1
    return out


def is_residue(a: int, q: int) -> bool:
    """Euler's criterion: a is a nonzero square mod the odd prime q."""
    return a % q != 0 and pow(a, (q - 1) // 2, q) == 1


def least_nonresidue(q: int) -> int:
    """The least quadratic non-residue mod q (always a prime)."""
    for a in range(2, q):
        if not is_residue(a, q):
            return a
    raise ValueError(q)


def p_local(q: int) -> int:
    """The largest P with every prime p <= P a square mod q: n(q) - 1."""
    return least_nonresidue(q) - 1


def primitive_root(q: int) -> int:
    """The least primitive root mod the prime q."""
    phi = q - 1
    fac = factorize(phi)
    for g in range(2, q):
        if all(pow(g, phi // p, q) != 1 for p in fac):
            return g
    raise ValueError(q)


#: i^j as Gaussian integers (re, im).
_I_POW = ((1, 0), (0, 1), (-1, 0), (0, -1))


@lru_cache(maxsize=None)
def character(q: int) -> tuple[tuple[int, int], ...]:
    """chi(a) for a = 0..q-1 as exact Gaussian integers (re, im).

    chi is the order-4 character with chi(g) = i at the least primitive root g;
    chi-bar is the other one.  F_k is the same function for either choice (the
    pair {chi, chi-bar} is swapped and k is unchanged), which the tests check.
    """
    if not is_prime(q) or q % 4 != 1:
        raise ValueError("q must be a prime = 1 mod 4")
    g = primitive_root(q)
    out = [(0, 0)] * q
    x = 1
    for j in range(q - 1):
        out[x] = _I_POW[j % 4]
        x = x * g % q
    return tuple(out)


def chi_value(n: int, q: int) -> tuple[int, int]:
    return character(q)[n % q]


def parity(q: int) -> int:
    """a in {0, 1} with chi(-1) = (-1)^a."""
    re, _ = chi_value(q - 1, q)
    return 0 if re == 1 else 1


def coefficient_pair(n: int, q: int) -> tuple[int, int]:
    """b(n) = x + y k as the exact pair (x, y) = (Re chi(n), Im chi(n))."""
    return chi_value(n, q)


def jacobi_sum(q: int) -> tuple[int, int]:
    """J(chi, chi) = sum_a chi(a) chi(1 - a), an exact Gaussian integer."""
    chi = character(q)
    re = im = 0
    for a in range(q):
        x1, y1 = chi[a]
        x2, y2 = chi[(1 - a) % q]
        re += x1 * x2 - y1 * y2
        im += x1 * y2 + x2 * y1
    return re, im


# ---------------------------------------------------------------------------
# mpmath: L(s, chi), the completion, the linear solve for k
# ---------------------------------------------------------------------------


def _num(s):
    return mp.mpmathify(s)


def _chi_mp(a: int, q: int, conj: bool):
    x, y = chi_value(a, q)
    return mp.mpc(x, -y if conj else y)


def _hurwitz(s, q: int) -> list:
    """zeta(s, a/q) for a = 1..q-1 at ambient precision."""
    return [mp.zeta(s, mp.mpf(a) / q) for a in range(1, q)]


def L_mp(s, q: int, conj: bool = False, dps: int = 30):
    """L(s, chi) (or L(s, chi-bar)) = q^{-s} sum_a chi(a) zeta(s, a/q).  s != 1."""
    with mp.workdps(dps + _GUARD):
        s = _num(s)
        h = _hurwitz(s, q)
        tot = mp.mpc(0)
        for a in range(1, q):
            tot += _chi_mp(a, q, conj) * h[a - 1]
        val = mp.power(q, -s) * tot
    return +val


def gamma_factor(s, q: int):
    """(q/pi)^{(s+a)/2} Gamma((s+a)/2) at ambient precision."""
    a = parity(q)
    return mp.power(q / mp.pi, (s + a) / 2) * mp.gamma((s + a) / 2)


def _lambda_pair(s, q: int):
    """(Lambda(s, chi), Lambda(s, chi-bar)) at ambient precision, one Hurwitz pass."""
    h = _hurwitz(s, q)
    lc = mp.mpc(0)
    lb = mp.mpc(0)
    for a in range(1, q):
        lc += _chi_mp(a, q, False) * h[a - 1]
        lb += _chi_mp(a, q, True) * h[a - 1]
    pre = mp.power(q, -s) * gamma_factor(s, q)
    return pre * lc, pre * lb


@lru_cache(maxsize=64)
def _k_cached(q: int, dps: int) -> tuple:
    """(k, Im k residue, cross-point relative defect), derived at dps + guard.

    The defect of G_k(s) - G_k(1-s) is [A(s) - i k B(s)]/2 with
        A = Lam + Lambar - Lam(1-s) - Lambar(1-s),
        B = Lam - Lambar - Lam(1-s) + Lambar(1-s),
    so k = A(s0) / (i B(s0)) at any point with B(s0) != 0 (the base point is
    zeta.epstein's).  The same k must then kill the defect at an unrelated point.
    """
    with mp.workdps(dps + _GUARD + 5):
        s0 = mp.mpc(mp.mpf(3) / 4, mp.mpf(3) / 2)
        l0, b0 = _lambda_pair(s0, q)
        l1, b1 = _lambda_pair(1 - s0, q)
        A = l0 + b0 - l1 - b1
        B = l0 - b0 - l1 + b1
        if abs(B) < mp.mpf(10) ** (-(dps // 2)):
            raise ArithmeticError("B(s0) is too small for the linear solve")
        k = A / (mp.mpc(0, 1) * B)
        k_re, k_im = mp.re(k), mp.im(k)
        s1 = mp.mpc(mp.mpf(3) / 10, 2)
        c = (1 - mp.mpc(0, 1) * k_re) / 2
        x0, y0 = _lambda_pair(s1, q)
        x1, y1 = _lambda_pair(1 - s1, q)
        g0 = c * x0 + mp.conj(c) * y0
        g1 = c * x1 + mp.conj(c) * y1
        rel = abs(g0 - g1) / abs(g0)
        return (+k_re, +k_im, +rel)


def k_linear_solve(q: int, dps: int = 40):
    """The real constant k making G_k self-dual, derived by the linear solve.

    Raises if the imaginary residue or the cross-point defect is not at the
    working precision, which is the self-check ``zeta.epstein.kappa`` runs.
    """
    k_re, k_im, rel = _k_cached(int(q), int(dps))
    tol = mp.mpf(10) ** (-(dps + 2))
    if not (abs(k_im) < tol and rel < tol):
        raise ArithmeticError(
            f"k derivation failed self-check at q={q}: Im k = {mp.nstr(k_im, 5)}, "
            f"cross-point defect = {mp.nstr(rel, 5)} at dps={dps}"
        )
    with mp.workdps(dps):
        return +k_re


def gauss_sum(q: int, dps: int = 40):
    """tau(chi) = sum_a chi(a) e^{2 pi i a / q}."""
    with mp.workdps(dps + _GUARD):
        tot = mp.mpc(0)
        for a in range(1, q):
            tot += _chi_mp(a, q, False) * mp.expjpi(mp.mpf(2 * a) / q)
        return +tot


def root_number(q: int, dps: int = 40):
    """eps(chi) = tau(chi) / (i^a sqrt q)."""
    with mp.workdps(dps + _GUARD):
        a = parity(q)
        eps = gauss_sum(q, dps + _GUARD) / (mp.mpc(0, 1) ** a * mp.sqrt(q))
        return +eps


def theta_angle(q: int, dps: int = 40):
    """theta = arg eps in (-pi, pi]."""
    with mp.workdps(dps + _GUARD):
        return +mp.arg(root_number(q, dps + _GUARD))


def k_from_gauss(q: int, dps: int = 40):
    """tan(theta/2) from the Gauss sum, the second route to k."""
    with mp.workdps(dps + _GUARD):
        return +mp.tan(theta_angle(q, dps + _GUARD) / 2)


def jacobi_check(q: int, dps: int = 40) -> dict:
    """Why cos(theta/2) != 0 for an order-4 character (ordinary argument).

    Classically (Ireland-Rosen ch. 8) tau(chi)^2 = J(chi, chi) tau(chi^2), and
    tau(chi^2) = sqrt q for the quadratic character of a prime q = 1 mod 4, so
    eps^2 = chi(-1) J(chi, chi) / sqrt q.  J is a Gaussian integer of norm q,
    and q is not a square, so Im J != 0: eps^2 is not real, eps is none of
    +-1, +-i, and theta is none of 0, +-pi/2, pi.  In particular cos(theta/2) and
    sin(theta/2) are both nonzero, so the normalisation exists and k != 0.
    The exact part is J and its norm; the identity is cited and measured here.
    """
    jre, jim = jacobi_sum(q)
    with mp.workdps(dps + _GUARD):
        eps = root_number(q, dps + _GUARD)
        sign = 1 if parity(q) == 0 else -1
        pred = sign * mp.mpc(jre, jim) / mp.sqrt(q)
        resid = abs(eps * eps - pred)
        th = mp.arg(eps)
        return {
            "q": q,
            "J": (jre, jim),
            "norm_J": jre * jre + jim * jim,
            "eps_squared_identity_residual": float(resid),
            "theta": +th,
            "cos_half_theta": +mp.cos(th / 2),
            "sin_half_theta": +mp.sin(th / 2),
        }


# ---------------------------------------------------------------------------
# the rival F_k, its completion, its functional-equation defect
# ---------------------------------------------------------------------------


def coefficient(n: int, q: int, k=None, dps: int = 40):
    """b(n) = Re chi(n) + k Im chi(n), with k from the linear solve by default."""
    if k is None:
        k = k_linear_solve(q, dps)
    x, y = coefficient_pair(n, q)
    with mp.workdps(dps + _GUARD):
        return +(x + y * mp.mpf(k))


def _b_table(q: int, k, perturb: dict | None = None) -> list:
    """b(a) for a = 1..q-1 at ambient precision, optionally perturbed per class."""
    out = []
    for a in range(1, q):
        x, y = coefficient_pair(a, q)
        v = x + y * k
        if perturb and a in perturb:
            v = v + mp.mpf(perturb[a])
        out.append(v)
    return out


def _F_amb(s, q: int, k, perturb: dict | None = None,
           perturb_n: dict | None = None):
    """F_k(s) at ambient precision, no rounding on return.

    ``perturb`` adds a constant to b on whole residue classes mod q;
    ``perturb_n`` adds delta to the single coefficient b(n) (one term
    delta n^{-s}).  Both are planted faults for the defect test.
    """
    h = _hurwitz(s, q)
    b = _b_table(q, mp.mpf(k), perturb)
    val = mp.power(q, -s) * mp.fsum(b[i] * h[i] for i in range(q - 1))
    if perturb_n:
        for n, delta in perturb_n.items():
            val += mp.mpf(delta) * mp.power(n, -s)
    return val


def F_mp(s, q: int, k=None, dps: int = 30, perturb: dict | None = None):
    """F_k(s) = q^{-s} sum_a b(a) zeta(s, a/q), s != 1.  ``perturb`` adds a
    constant to b on one or more residue classes (the planted-fault control)."""
    if k is None:
        k = k_linear_solve(q, dps)
    with mp.workdps(dps + _GUARD):
        val = _F_amb(_num(s), q, k, perturb)
    return +val


def completed_F(s, q: int, k=None, dps: int = 30, perturb: dict | None = None):
    """G_k(s) = (q/pi)^{(s+a)/2} Gamma((s+a)/2) F_k(s)."""
    if k is None:
        k = k_linear_solve(q, dps)
    with mp.workdps(dps + _GUARD):
        s = _num(s)
        val = gamma_factor(s, q) * _F_amb(s, q, k, perturb)
    return +val


def fe_defect(s, q: int, k=None, dps: int = 40, perturb: dict | None = None,
              perturb_n: dict | None = None):
    """|G(s) - G(1-s)| / |G(s)|: the relative functional-equation defect.

    k defaults to the linear solve at ``dps`` digits, so the defect measures
    what a dps-digit k achieves; both sides are evaluated with ``_GUARD`` extra
    digits and differenced without intermediate rounding, so an agreement
    below 10^-dps is reported as a number rather than rounded to zero.
    """
    if k is None:
        k = k_linear_solve(q, dps)
    with mp.workdps(dps + 2 * _GUARD):
        s = _num(s)
        g0 = gamma_factor(s, q) * _F_amb(s, q, k, perturb, perturb_n)
        g1 = gamma_factor(1 - s, q) * _F_amb(1 - s, q, k, perturb, perturb_n)
        return +(abs(g0 - g1) / abs(g0))


#: Sample points for the defect measurement: asymmetric, off the line, away from 1.
FE_POINTS = (
    (3, 4), (-0.25, 10.5), (1.4, -3), (0.8, 21), (2.5, 0.7), (-1.5, 2.25),
)


def fe_defect_table(q: int, dps: int = 40, k=None, perturb: dict | None = None,
                    perturb_n: dict | None = None):
    """Max relative defect over :data:`FE_POINTS` (measured, one route)."""
    out = []
    for (x, y) in FE_POINTS:
        out.append(fe_defect(mp.mpc(x, y), q, k=k, dps=dps, perturb=perturb,
                             perturb_n=perturb_n))
    return max(out), out


# ---------------------------------------------------------------------------
# exact arithmetic for -F'/F: the P-smooth identities and the agreement set
# ---------------------------------------------------------------------------
#
# Lambda_F(n) is an integer combination of k^j log p: the recursion
#     Lambda_F(n) = b(n) log n - sum_{d | n, 1 < d < n} Lambda_F(d) b(n/d),
# with b(n) = x + y k in Z[k] and log n = sum e_p log p, never leaves
# Z[k] (x) span{log p}.  A dict {(p, j): integer} holds the coefficient of
# k^j log p.  Lambda(n) chi(n) is a Gaussian integer times log p at prime powers.


def exact_lambda_F(nmax: int, q: int) -> list[dict]:
    """Lambda_F(n) for n = 0..nmax as exact dicts {(p, j): int} (index 0, 1 empty)."""
    divisors: list[list[int]] = [[] for _ in range(nmax + 1)]
    for d in range(2, nmax // 2 + 1):
        for m in range(2 * d, nmax + 1, d):
            divisors[m].append(d)
    logs = [None] * (nmax + 1)
    lam: list[dict] = [dict() for _ in range(nmax + 1)]
    for n in range(2, nmax + 1):
        x, y = coefficient_pair(n, q)
        acc: dict = {}
        if x or y:
            fac = factorize(n)
            logs[n] = fac
            for p, e in fac.items():
                if x:
                    acc[(p, 0)] = acc.get((p, 0), 0) + e * x
                if y:
                    acc[(p, 1)] = acc.get((p, 1), 0) + e * y
        for d in divisors[n]:
            ld = lam[d]
            if not ld:
                continue
            x2, y2 = coefficient_pair(n // d, q)
            if not (x2 or y2):
                continue
            for (p, j), v in ld.items():
                if x2:
                    acc[(p, j)] = acc.get((p, j), 0) - v * x2
                if y2:
                    acc[(p, j + 1)] = acc.get((p, j + 1), 0) - v * y2
        lam[n] = {key: v for key, v in acc.items() if v != 0}
    return lam


def exact_lambda_chi(n: int, q: int) -> dict:
    """Lambda(n) chi(n) as {p: (re, im)} (empty unless n is a prime power)."""
    fac = factorize(n)
    if len(fac) != 1:
        return {}
    (p, e), = fac.items()
    x, y = 1, 0
    cx, cy = chi_value(p, q)
    for _ in range(e):
        x, y = x * cx - y * cy, x * cy + y * cx
    if x == 0 and y == 0:
        return {}
    return {p: (x, y)}


def exact_agrees(lam_F: dict, lam_chi: dict) -> bool:
    """Formal equality: Lambda_F has no k-terms and equals the real Lambda chi."""
    if any(im != 0 for (_, im) in lam_chi.values()):
        return False
    want = {(p, 0): re for p, (re, _) in lam_chi.items() if re != 0}
    return lam_F == want


def is_smooth(n: int, P: int) -> bool:
    return all(p <= P for p in factorize(n)) if n > 1 else True


def nr_composed(n: int, q: int) -> bool:
    """n > 1, coprime to q, every prime factor a quadratic non-residue mod q."""
    if n <= 1 or n % q == 0:
        return False
    return all(not is_residue(p, q) for p in factorize(n))


def _lambda_F_numeric(lam: dict, k, dps: int = 40):
    with mp.workdps(dps + _GUARD):
        return mp.fsum(v * mp.mpf(k) ** j * mp.log(p) for (p, j), v in lam.items())


def exact_identity_report(q: int, nmax: int = 10 ** 4, dps: int = 40) -> dict:
    """The P-smooth identities and the full agreement set, exactly, for n <= nmax.

    Checks, each exact:
      (i)  b(n) = chi(n) (real, Im chi(n) = 0) for every P-smooth n <= nmax;
      (ii) Lambda_F(n) = Lambda(n) chi(n) formally for every P-smooth n <= nmax;
      (iii) the formal agreement set is exactly the complement of the
            non-residue-composed n, as the factorisation predicts;
    and, numerically at the derived k (measured), every formal disagreement is a
    genuine one, |Lambda_F(n) - Lambda(n) chi(n)| > 1e-20.
    """
    P = p_local(q)
    lam = exact_lambda_F(nmax, q)
    k = k_linear_solve(q, dps)
    smooth = [n for n in range(1, nmax + 1) if is_smooth(n, P)]
    bad_b = [n for n in smooth if coefficient_pair(n, q)[1] != 0
             or coefficient_pair(n, q)[0] not in (1, -1)]
    bad_lam = [n for n in smooth if n > 1 and not exact_agrees(lam[n], exact_lambda_chi(n, q))]
    disagree = [n for n in range(2, nmax + 1)
                if not exact_agrees(lam[n], exact_lambda_chi(n, q))]
    predicted = [n for n in range(2, nmax + 1) if nr_composed(n, q)]
    min_gap = None
    with mp.workdps(dps + _GUARD):
        for n in disagree:
            lf = _lambda_F_numeric(lam[n], k, dps)
            lc = exact_lambda_chi(n, q)
            lcv = mp.fsum(mp.mpc(re, im) * mp.log(p) for p, (re, im) in lc.items())
            gap = abs(lf - lcv)
            if min_gap is None or gap < min_gap:
                min_gap = gap
    return {
        "q": q,
        "P": P,
        "nmax": nmax,
        "n_smooth": len(smooth),
        "smooth_coefficient_failures": bad_b,
        "smooth_log_derivative_failures": bad_lam,
        "first_disagreement": disagree[0] if disagree else None,
        "n_disagreements": len(disagree),
        "disagreement_set_equals_nr_composed": disagree == predicted,
        "accidental_agreements": sorted(set(predicted) - set(disagree)),
        "min_numeric_gap_on_disagreements": float(min_gap) if min_gap is not None else None,
        "lambda_F_first": {n: lam[n] for n in range(2, 13)},
    }


# ---------------------------------------------------------------------------
# window forms: the CvS/CCM truncated Weil form of hunts/rogue_frontier/weil_trunc
# ---------------------------------------------------------------------------
#
# galerkin.py assembles Q = W02 - WR - Wp on the Fourier basis
# U_n(y) = L^{-1/2} e^{2 pi i n y / L} of L^2([0, L]), L = log c, n in [-N, N],
# for zeta and for Davenport-Heilbronn.  Its archimedean block depends only on
# the Gamma shift a (1/4 for Gamma(s/2), 3/4 for Gamma((s+1)/2)) and the
# conductor through the constant log(q/pi) + psi(a); its prime block reads the
# coefficients Lambda_f(n), n <= c, of -f'/f.  Neither F_k nor L(s, chi) has a
# pole, so W02 = 0 for both.
#
# The one new piece is the prime block for complex coefficients, which L(s, chi)
# needs once a non-residue prime enters the window.  The explicit formula pairs
# Lambda(n) chi(n) with G(log n) and its conjugate with G(-log n) = conj G(log n),
# G(y) = int f(x + y) conj f(x) dx the autocorrelation, so a coefficient
# c_n = Lambda(n) chi(n) enters as 2 Re(c_n G(log n)).  With
# g_nm(y) = int_0^{L-y} U_n(x+y) conj U_m(x) dx (= g_mn) one has
#     2 Re g_nm = q_nm   (CCM Lemma 2.3, the kernel galerkin.py uses),
#     -2 Im g_nm = qo_nm = [cos(a_m y) - cos(a_n y)] / (pi (n - m)),  n != m,
#     qo_nn = -2 (1 - y/L) sin(a_n y),   a_n = 2 pi n / L,
# so the block is sum_n n^{-1/2} [Re(c_n) q_nm + Im(c_n) qo_nm](log n): still
# real symmetric in this basis, but qo is odd under the parity n -> -n, so the
# imaginary parts couple galerkin.py's even and odd sectors.  Convention: with
# the opposite pairing (chi(n) with G(-log n)) the form is that of L(s, chi-bar),
# which is this one reflected n -> -n, with the same spectrum; nothing below
# depends on the choice.  :func:`odd_kernel_check` measures qo against direct
# quadrature of the correlation integral.


def _galerkin():
    import galerkin  # hunts/rogue_frontier/weil_trunc/galerkin.py

    return galerkin


def lambda_F_numeric(nmax: int, q: int, k=None, dps: int = 40) -> list:
    """Lambda_F(n), n <= nmax, from b(n) by zeta.epstein's numeric recursion.

    This is a different implementation from :func:`exact_lambda_F` (it solves
    the recursion in floating point from the coefficients), so the window
    forms below do not inherit the exact module's code.
    """
    from zeta.epstein import log_derivative_coefficients

    if k is None:
        k = k_linear_solve(q, dps)
    with mp.workdps(dps + _GUARD):
        kk = mp.mpf(k)

        def coef(n, _q=q, _k=kk):
            x, y = coefficient_pair(int(n), _q)
            return x + y * _k

        lam = log_derivative_coefficients(coef, nmax, dps=dps + _GUARD)
    return lam


def lambda_chi_numeric(n: int, q: int):
    """Lambda(n) chi(n) as an mpc, from the von Mangoldt function directly."""
    fac = factorize(n)
    if len(fac) != 1:
        return mp.mpc(0)
    (p, e), = fac.items()
    x, y = chi_value(pow(p, e), q)
    return mp.mpc(x, y) * mp.log(p)


class CharacterTruncation:
    """Band-N window form at cutoff c for an entire function with conductor q,
    Gamma shift a = 1/4 + parity/2, and complex prime coefficients.

    ``coeffs`` is a list of (n, c_n) with c_n = Lambda_f(n), n <= c.  Real parts
    go through galerkin.py's own P, R sequences and its ``entry`` assembly (an
    instance of ``galerkin.Truncation`` is built by bypassing its kind
    dispatch, so ``entry``, ``even_matrix`` and ``odd_matrix`` are its code);
    imaginary parts add the parity-odd block derived above.
    """

    def __init__(self, c, N: int, q, parity_a: int, coeffs):
        g = _galerkin()
        t = g.Truncation.__new__(g.Truncation)
        t.c = c
        t.N = int(N)
        t.kind = "character"  # not "zeta": galerkin's w02 returns 0
        L = mp.log(c)
        t.L = L
        J = int((mp.dps + 12) * mp.log(10) / (2 * L)) + 3
        a = mp.mpf(1) / 4 + mp.mpf(parity_a) / 2
        t.a = a
        const = mp.log(mp.mpf(q) / mp.pi) + mp.psi(0, a)
        S, D, tail = g._arch_sums(a, L, N, J)
        t._S = S
        t._archdiag = [const - D[k] + 2 * tail for k in range(N + 1)]
        Pseq = [mp.mpf(0)] * (N + 1)
        Rseq = [mp.mpf(0)] * (N + 1)
        Cseq = [mp.mpf(0)] * (N + 1)
        Oseq = [mp.mpf(0)] * (N + 1)
        has_odd = False
        for n, cn in coeffs:
            cn = mp.mpmathify(cn)
            re, im = mp.re(cn), mp.im(cn)
            y = mp.log(n)
            w = 1 / mp.sqrt(n)
            for kk in range(N + 1):
                om = 2 * mp.pi * kk / L
                if re != 0:
                    Pseq[kk] += w * re * mp.sin(om * y)
                    Rseq[kk] += w * re * 2 * (1 - y / L) * mp.cos(om * y)
                if im != 0:
                    has_odd = True
                    Cseq[kk] += w * im * mp.cos(om * y)
                    Oseq[kk] += w * im * (-2) * (1 - y / L) * mp.sin(om * y)
        t._P = Pseq
        t._R = Rseq
        self.base = t
        self.N = int(N)
        self.c = c
        self._C = Cseq
        self._O = Oseq
        self.has_odd = has_odd

    def _odd(self, n: int, m: int):
        if not self.has_odd:
            return mp.mpf(0)
        if n == m:
            k = abs(n)
            v = self._O[k]
            return v if n >= 0 else -v
        cm = self._C[abs(m)]
        cn = self._C[abs(n)]
        return (cm - cn) / (mp.pi * (n - m))

    def entry(self, n: int, m: int):
        """Q(n, m) = galerkin's entry minus the parity-odd prime block."""
        return self.base.entry(n, m) - self._odd(n, m)

    def full_matrix(self):
        """(2N+1) x (2N+1), rows and columns indexed n = -N..N."""
        N = self.N
        M = mp.matrix(2 * N + 1)
        for i, n in enumerate(range(-N, N + 1)):
            for j, m in enumerate(range(-N, N + 1)):
                if j < i:
                    continue
                v = self.entry(n, m)
                M[i, j] = v
                M[j, i] = v
        return M

    def even_matrix(self):
        if self.has_odd:
            raise ValueError("parity sectors are coupled; use full_matrix")
        return self.base.even_matrix()

    def odd_matrix(self):
        if self.has_odd:
            raise ValueError("parity sectors are coupled; use full_matrix")
        return self.base.odd_matrix()


def window_form_F(c, N: int, q: int, k=None, dps: int = 40) -> CharacterTruncation:
    """The window form of F_k (real coefficients Lambda_F(n), n <= c)."""
    nmax = int(math.floor(float(c) + 1e-9))
    lam = lambda_F_numeric(max(nmax, 2), q, k=k, dps=dps)
    coeffs = [(n, lam[n]) for n in range(2, nmax + 1) if lam[n] != 0]
    return CharacterTruncation(c, N, q, parity(q), coeffs)


def window_form_L(c, N: int, q: int) -> CharacterTruncation:
    """The window form of L(s, chi) (complex coefficients Lambda(n) chi(n))."""
    nmax = int(math.floor(float(c) + 1e-9))
    coeffs = []
    for n in range(2, nmax + 1):
        v = lambda_chi_numeric(n, q)
        if v != 0:
            coeffs.append((n, v))
    return CharacterTruncation(c, N, q, parity(q), coeffs)


def matrix_max_abs_diff(A, B):
    return max(abs(A[i, j] - B[i, j]) for i in range(A.rows) for j in range(A.cols))


def window_comparison(c, N: int, q: int, dps: int = 40) -> dict:
    """Entrywise and spectral comparison of the two full window forms at (c, N)."""
    with mp.workdps(dps):
        WF = window_form_F(c, N, q, dps=dps)
        WL = window_form_L(c, N, q)
        MF = WF.full_matrix()
        ML = WL.full_matrix()
        diff = matrix_max_abs_diff(MF, ML)
        scale = max(abs(MF[i, j]) for i in range(MF.rows) for j in range(MF.cols))
        eF = sorted(mp.eigsy(MF)[0])
        eL = sorted(mp.eigsy(ML)[0])
        return {
            "q": q,
            "c": float(c),
            "N": N,
            "max_abs_entry_diff": float(diff),
            "max_abs_entry": float(scale),
            "L_parity_coupled": WL.has_odd,
            "lambda_min_F": float(eF[0]),
            "lambda_min_L": float(eL[0]),
            "max_eig_diff": float(max(abs(x - y) for x, y in zip(eF, eL))),
        }


def odd_kernel_check(c=7, n: int = 2, m: int = -3, y=None, dps: int = 30) -> dict:
    """qo_nm(y) and q_nm(y) against direct quadrature of -2 Im g_nm and 2 Re g_nm."""
    with mp.workdps(dps):
        L = mp.log(c)
        y = mp.mpf(y) if y is not None else L / 3
        U = lambda k, x: mp.expjpi(2 * k * x / L) / mp.sqrt(L)  # noqa: E731
        g = mp.quad(lambda x: U(n, x + y) * mp.conj(U(m, x)), [0, L - y])
        an = 2 * mp.pi * n / L
        am = 2 * mp.pi * m / L
        if n != m:
            q_cl = (mp.sin(am * y) - mp.sin(an * y)) / (mp.pi * (n - m))
            qo_cl = (mp.cos(am * y) - mp.cos(an * y)) / (mp.pi * (n - m))
        else:
            q_cl = 2 * (1 - y / L) * mp.cos(an * y)
            qo_cl = -2 * (1 - y / L) * mp.sin(an * y)
        return {
            "q_closed_minus_quad": float(abs(q_cl - 2 * mp.re(g))),
            "qo_closed_minus_quad": float(abs(qo_cl + 2 * mp.im(g))),
            "g_symmetric": float(abs(g - mp.quad(
                lambda x: U(m, x + y) * mp.conj(U(n, x)), [0, L - y]))),
        }


# ---------------------------------------------------------------------------
# zeros, route A: mpmath (fp context for the census, mp for polishing)
# ---------------------------------------------------------------------------
#
# The census uses the folded argument principle.  G_k(1-s) = G_k(s) and
# G_k(conj s) = conj G_k(s), so the reflection s -> 1 - conj(s) carries G to
# conj G, and the count of zeros of G in [1 - sR, sR] x [T1, T2] is (1/pi) times
# the continuous change of arg G along the right half of the boundary,
# 1/2 + iT1 -> sR + iT1 -> sR + iT2 -> 1/2 + iT2.  The Gamma factor is analytic
# and zero-free on Re s >= 1/2, so its share is theta(T2) - theta(T1) with
#     theta(t) = (t/2) log(q/pi) + Im log Gamma((1/2 + a + i t)/2).
# On Re s = sR, with sR above the coefficient-domination abscissa of strip.py,
# |F - 1| < 1, so Re F > 0 and the right edge contributes the difference of
# principal arguments.  Writing lam(T) = Arg F(sR + iT) + (continuous change of
# arg F from sR + iT to 1/2 + iT),
#     N(T1, T2) = [Psi(T2) - Psi(T1)] / pi,    Psi(T) = theta(T) + lam(T),
# and with F > 0 on [1/2, sR] the base is Psi(0) = 0, so N(0, T) = Psi(T)/pi.
# G(1/2 + iT) is real, so Psi(T)/pi is an integer, and sign Z(T) = (-1)^{Psi/pi}
# for the Hardy function Z(t) = e^{i theta(t)} F(1/2 + it).  Each window then
# closes as  n_box = n_line + 2 n_right, the census.py accounting.


def _fp_table(q: int, k) -> list[tuple[float, float]]:
    """[(a/q, b(a))] for the residue classes with b(a) != 0, as floats."""
    out = []
    kf = float(k)
    for a in range(1, q):
        x, y = coefficient_pair(a, q)
        v = x + y * kf
        if v != 0:
            out.append((a / q, v))
    return out


class FpRival:
    """F_k, theta and Z in mpmath's fp context (double precision, measured)."""

    def __init__(self, q: int, k=None, dps: int = 40):
        self.q = q
        self.k = float(k if k is not None else k_linear_solve(q, dps))
        self.a = parity(q)
        self.table = _fp_table(q, self.k)
        self.logq = math.log(q)
        self.n_evals = 0

    def F(self, s: complex) -> complex:
        self.n_evals += 1
        s = complex(s)
        tot = 0j
        for a, v in self.table:
            tot += v * complex(fp.zeta(s, a))
        return tot * complex(fp.exp(-s * self.logq))

    def dF(self, s: complex) -> complex:
        s = complex(s)
        tot = 0j
        tot1 = 0j
        for a, v in self.table:
            tot += v * complex(fp.zeta(s, a))
            tot1 += v * complex(fp.zeta(s, a, 1))
        e = complex(fp.exp(-s * self.logq))
        return e * (tot1 - self.logq * tot)

    def theta(self, t: float) -> float:
        z = complex(0.5 + self.a, t) / 2
        return 0.5 * t * math.log(self.q / math.pi) + complex(fp.loggamma(z)).imag

    def Z(self, t: float) -> float:
        v = complex(fp.expj(self.theta(t))) * self.F(complex(0.5, t))
        return v.real

    def mean_gap(self, t: float) -> float:
        x = self.q * max(t, 1.0) / (2 * math.pi)
        return 2 * math.pi / math.log(max(x, 3.0))


def arg_change_fp(f, z0: complex, z1: complex, step: float = 0.04,
                  max_turn: float = 0.6, min_len: float = 1e-9) -> tuple[float, int]:
    """Continuous change of arg f along the segment z0 -> z1 (measured).

    Samples at about ``step`` spacing and refines any piece whose principal
    argument increment exceeds ``max_turn`` radians, so the accumulated sum is
    the continuous variation unless f winds faster than the refinement can
    see.  Raises if f becomes 1e-12-small on the contour.
    """
    length = abs(z1 - z0)
    n = max(2, int(math.ceil(length / step)))
    pts = [z0 + (z1 - z0) * j / n for j in range(n + 1)]
    vals = [f(z) for z in pts]
    total = 0.0
    n_ev = len(vals)
    stack = [(pts[j], pts[j + 1], vals[j], vals[j + 1]) for j in range(n)][::-1]
    while stack:
        za, zb, fa, fb = stack.pop()
        if abs(fa) < 1e-12 or abs(fb) < 1e-12:
            raise ArithmeticError(f"f is too small on the contour near {za}")
        d = math.atan2((fb / fa).imag, (fb / fa).real)
        if abs(d) > max_turn:
            if abs(zb - za) < min_len:
                raise ArithmeticError(f"no resolution of arg near {za}")
            zm = (za + zb) / 2
            fm = f(zm)
            n_ev += 1
            stack.append((zm, zb, fm, fb))
            stack.append((za, zm, fa, fm))
            continue
        total += d
    return total, n_ev


def domination_abscissa_mp(q: int, k=None, dps: int = 30):
    """Root sigma_dom > 1 of sum_{n>=2} |b(n)| n^{-sigma} = 1 (strip.py's g).

    Coefficient domination, as in hunts/lambda_dh_bounds/strip.py: for
    Re s > sigma_dom, |F(s) - 1| < 1, so Re F > 0 there.  Measured (mpmath).
    """
    if k is None:
        k = k_linear_solve(q, dps)
    with mp.workdps(dps + _GUARD):
        kk = abs(mp.mpf(k))
        wts = []
        for a in range(1, q):
            x, y = coefficient_pair(a, q)
            w = abs(x) + abs(y) * kk
            if w:
                wts.append((a, w))

        def g(sig):
            sig = mp.mpf(sig)
            return mp.fsum(w * mp.power(q, -sig) * mp.zeta(sig, mp.mpf(a) / q)
                           for a, w in wts) - 2

        lo, hi = mp.mpf("1.0001"), mp.mpf(6)
        if not (g(lo) > 0 and g(hi) < 0):
            raise ArithmeticError("domination bracket failed")
        for _ in range(80):
            mid = (lo + hi) / 2
            if g(mid) > 0:
                lo = mid
            else:
                hi = mid
        return +hi


def psi_fp(rv: FpRival, T: float, sR: float) -> dict:
    """Psi(T) = theta(T) + lam(T) and the count N(0, T) = Psi/pi (measured)."""
    z_right = complex(sR, T)
    fR = rv.F(z_right)
    if fR.real <= 0:
        raise ArithmeticError("Re F <= 0 on the right edge: sR is too small")
    argR = math.atan2(fR.imag, fR.real)
    change, n_ev = arg_change_fp(rv.F, z_right, complex(0.5, T))
    psi = rv.theta(T) + argR + change
    x = psi / math.pi
    n = round(x)
    return {"T": T, "psi_over_pi": x, "N": int(n), "defect": abs(x - n), "n_evals": n_ev + 1}


def box_count_fp(rv: FpRival, x0: float, x1: float, y0: float, y1: float,
                 step: float = 0.04) -> dict:
    """Winding number of F around [x0, x1] x [y0, y1] (measured, fp)."""
    corners = [complex(x0, y0), complex(x1, y0), complex(x1, y1), complex(x0, y1)]
    total = 0.0
    n_ev = 0
    for i in range(4):
        d, n = arg_change_fp(rv.F, corners[i], corners[(i + 1) % 4], step=step)
        total += d
        n_ev += n
    w = total / (2 * math.pi)
    return {"box": [x0, x1, y0, y1], "winding": w, "N": int(round(w)),
            "defect": abs(w - round(w)), "n_evals": n_ev}


def newton_fp(rv: FpRival, s0: complex, tol: float = 1e-13, max_iter: int = 40) -> complex:
    """Newton in double precision.  The step tolerance is relative to |s|: at
    height 640 the spacing of floats near Im s is about 1e-13, so an absolute
    1e-13 sits at the noise floor and was never met there (window 80 of the
    q = 17 census, 2026-10-21)."""
    s = complex(s0)
    floor = 64 * 2.2e-16 * max(1.0, abs(s))
    for _ in range(max_iter):
        f = rv.F(s)
        df = rv.dF(s)
        ds = f / df
        s = s - ds
        if abs(ds) < max(tol, floor):
            return s
    raise ArithmeticError(f"Newton did not converge from {s0}")


def polish_mp(q: int, s0, dps: int = 30, k=None, iters: int = 6):
    """Newton in mp at ``dps`` from s0 (slow: mp Hurwitz zeta at height ~1000)."""
    if k is None:
        k = k_linear_solve(q, dps + 10)
    with mp.workdps(dps + _GUARD):
        kk = mp.mpf(k)
        b = _b_table(q, kk)
        s = mp.mpc(s0)
        for _ in range(iters):
            h0 = [mp.zeta(s, mp.mpf(a) / q) for a in range(1, q)]
            h1 = [mp.zeta(s, mp.mpf(a) / q, 1) for a in range(1, q)]
            e = mp.power(q, -s)
            f = e * mp.fsum(b[i] * h0[i] for i in range(q - 1))
            df = e * (mp.fsum(b[i] * h1[i] for i in range(q - 1)) - mp.log(q) * mp.fsum(
                b[i] * h0[i] for i in range(q - 1)))
            ds = f / df
            s = s - ds
            if abs(ds) < mp.mpf(10) ** (-(dps + 2)):
                break
        res = abs(_F_amb(s, q, kk))
        return +s, +res


# ---------------------------------------------------------------------------
# CORE_CANDIDATE.md: a prototype battery interface, and the claim it catches
# ---------------------------------------------------------------------------
#
# The field contract is zeta.epstein.zeta_interface's.  Nothing in zeta/ is
# edited: battery_with_plocal runs zeta.epstein.battery unchanged and then
# evaluates the same claim on this rival, recomputing the verdict by the same
# rule (a claim zeta shares with any rival does not distinguish).


def plocal_interface(q: int = 17, dps: int = 30) -> dict:
    """The zeta-like interface of zeta.epstein for F_k at conductor q."""
    from zeta.epstein import count_zeros_box

    k = k_linear_solve(q, dps + 10)

    def coef(n, _q=q, _k=k, _d=dps):
        if int(n) < 1:
            raise ValueError("Dirichlet coefficients are indexed from n = 1")
        return coefficient(int(n), _q, k=_k, dps=_d)

    def completed(s, _q=q, _k=k, _d=dps):
        return completed_F(s, _q, k=_k, dps=_d)

    def fe(s, _q=q, _k=k, _d=dps):
        with mp.workdps(_d + 2 * _GUARD):
            s = _num(s)
            v = gamma_factor(s, _q) * _F_amb(s, _q, _k) - gamma_factor(1 - s, _q) * _F_amb(1 - s, _q, _k)
        return +v

    def Z(t, _q=q, _k=k, _d=dps):
        with mp.workdps(_d + _GUARD):
            t = mp.mpf(t)
            a = parity(_q)
            th = t / 2 * mp.log(_q / mp.pi) + mp.im(mp.loggamma((mp.mpf(1) / 2 + a + mp.mpc(0, t)) / 2))
            v = mp.re(mp.expj(th) * _F_amb(mp.mpc(mp.mpf(1) / 2, t), _q, _k))
        return +v

    def zeros_on_line(t0, t1, _Z=Z):
        n = max(int(20 * (float(t1) - float(t0))) + 2, 8)
        vals = [_Z(mp.mpf(t0) + (mp.mpf(t1) - mp.mpf(t0)) * j / n) for j in range(n + 1)]
        return sum(1 for a, b in zip(vals, vals[1:]) if a * b < 0)

    return {
        "name": f"plocal_{q}",
        "coefficient": coef,
        "completed": completed,
        "fe_defect": fe,
        "Z": Z,
        "zeros_on_line": zeros_on_line,
        "count_zeros_box": lambda s0, s1, _c=completed, _d=dps: count_zeros_box(
            s0, s1, dps=_d, fn=_c),
    }


def claim_unitary_euler_factor_at_2(iface: dict, jmax: int = 6) -> bool:
    """Claim: "the normalised coefficients have a degree-1 unitary Euler factor
    at p = 2": b(2^j) = b(2)^j for j <= jmax and |b(2)| = 1.

    Passes for zeta (b = 1) and for F_17 (b(2^j) = (-1)^j); fails for
    Davenport-Heilbronn (b(2) = kappa), for the shifted product (b(2) = 2^a +
    2^-a), for the principal Epstein form (b(2) = 0), and for the non-principal
    form, whose a(1) = 0: a Dirichlet series with a(1) = 0 has no Euler factor
    in this normalisation, so the claim is false there, not undefined.
    """
    a = iface["coefficient"]
    a1 = a(1)
    if a1 == 0:
        return False
    b2 = a(2) / a1
    tol = mp.mpf("1e-12")
    if abs(abs(b2) - 1) > tol:
        return False
    return all(abs(a(2 ** j) / a1 - b2 ** j) < tol for j in range(2, jmax + 1))


def battery_with_plocal(claim_fn, q: int = 17, dps: int = 30) -> dict:
    """zeta.epstein.battery unchanged, then the same claim on F_k at conductor q."""
    from zeta.epstein import battery

    base = battery(claim_fn, dps=dps)
    iface = plocal_interface(q, dps)
    try:
        holds = bool(claim_fn(iface))
        reason = None
    except Exception as exc:  # noqa: BLE001 - recorded, as battery does
        holds = False
        reason = f"{type(exc).__name__}: {exc}"
    out = dict(base)
    out[iface["name"]] = holds
    shared = set(base["shared_with"]) | ({iface["name"]} if holds else set())
    undefined = set(base["undefined_for"]) | ({iface["name"]} if reason else set())
    out["shared_with"] = tuple(sorted(shared))
    out["undefined_for"] = tuple(sorted(undefined))
    out["distinguishes"] = bool(base["riemann_zeta"]) and not shared and not undefined
    out["distinguishes_without_plocal"] = base["distinguishes"]
    return out
