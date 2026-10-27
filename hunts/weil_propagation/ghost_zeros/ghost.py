"""Ghost zeros of the band-N even ground-state transform (lane "ghost-zeros").

Everything this file does is fixed by ``PREREG.md`` (committed before any of
it ran); ``RESULTS.md`` reports it; ``test_ghost.py`` pins it.

For a window c (exact rational), a kind (dh, zeta, epstein, dedekind) and the
band N = 128 even sector of ``../numerics/wp_common.py``:

1. assemble the ball matrix (Arb), find the ground pair, and decide the CvS
   hypotheses for the band-N matrix: H1 simple (ball LDL^T at a shift between
   lambda_1 and lambda_2 has exactly one negative pivot), H3 isolated (the gap
   that shift proves), H2 even (the odd sector's bottom lies above the even
   one, by a ball LDL^T of the odd matrix);
2. enclose the true eigenvector: Davis-Kahan from the ball residual and that
   gap, ||v - x/||x|| || <= sqrt(2) eps / (s - RQ(x));
3. count the zeros of F_v (``wp_common.F_even_acb``) in thin rectangles by an
   Arb argument principle (Taylor models with a Cauchy remainder on each
   boundary segment; the vertical sides avoid every omega_k = 2 pi k / L by at
   least 1/32), count real sign changes at exact dyadic points, and locate each
   real zero by ball bisection.

Lesions act on the DH matrix: ``q1`` subtracts the off-line quadruple term
(4/L) Re(a(z_1) a(z_1)^T), z_1 = gamma_1 - i delta_1; ``sham`` subtracts the
on-line term (2/L) a(g) a(g)^T at the DH zero g = 89.4392...

The ``float`` command is a second implementation of the same assembly formulas
(``galerkin.Truncation`` is the mpmath original of which
``enclosures.BallTruncation`` is the ball twin), so it checks the code, not
the derivation of those formulas. The two routes also share the prime-power
sieve ``galerkin.prime_powers_upto`` (imported by the Arb assembly) and, for
Epstein and Dedekind, the integer representation counts of
``zeta.epstein.epstein_representation_count``. The inverse iteration, the
inertia, the transform (sinc form against the partial-fraction form), the
zero scan and the winding number are separate code: mpmath inverse iteration
seeded from a float64 spectrum, an mpmath LDL^T inertia, the sinc form of F,
and a sampled winding number with an integrality guard.

Usage, from the repository root with the repository root on PYTHONPATH:

    ghost.py windows                     on-line zeros for the Epstein and zeta_K windows
    ghost.py arb KIND [c ...] [--variant=primary|prec2|q1|sham|scan]
    ghost.py float KIND [c ...]
    ghost.py s2 [c ...] [--variant=primary|q1]
    ghost.py summary                     merge units/ into ghost_table.json and decide

Checkpoints are per unit in ``units/<variant>_<kind>.json``. Nothing here is a
claim about RH.
"""

from __future__ import annotations

import glob
import json
import math
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
NUM = os.path.join(ROOT, "hunts", "weil_propagation", "numerics")
WT = os.path.join(ROOT, "hunts", "rogue_frontier", "weil_trunc")
for _p in (NUM, WT, ROOT):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from flint import acb, arb, arb_mat, ctx, fmpq  # noqa: E402

import enclosures as EN  # noqa: E402
import wp_common as W  # noqa: E402

N_BAND = 128
C_LIST = ["29", "30", "61/2", "245/8", "31", "63/2", "47"]
C_BEFORE = ["29", "30", "61/2", "245/8"]  # at or before c*_128 in (30.646484375, 30.6474609375]
C_SCAN = ["14", "18", "22", "25", "27", "28"]
KINDS = ("dh", "zeta", "epstein", "dedekind")

#: (precision of assembly, eigenvector and F; precision of the LDL steps and residual), bits
PRECS = {
    "primary": {"dh": (400, 400), "epstein": (400, 400), "dedekind": (400, 400), "zeta": (900, 3200)},
    "prec2": {"dh": (640, 640), "epstein": (640, 640), "dedekind": (640, 640), "zeta": (1300, 3200)},
}
#: bisection depth of each real zero (2^-bits): PREREG S7 compares locations to 1e-20 / 1e-40
BISECT_BITS = {"dh": 70, "epstein": 70, "dedekind": 70, "zeta": 136}

GAMMA_1 = W.GAMMA_OFF  # 50 digits
DELTA_1 = W.DELTA_OFF
GAMMA_E = "16.2902157203904"  # ../numerics/epstein_offline.json root (measured)
DELTA_E = "0.453260474794661"
DH_GAP = (83.10884108474983, 87.64747633255973)  # data/dh_zeros_online_T120.json
ZETA_23 = "84.735492980517050105735311206827741417106627934241"
ZETA_24 = "87.425274613125229406531667850919213252171886401269"
SHAM_NEAR = 89.43924

GHOST_RADIUS = Fraction(3, 10)
ACCOUNT_RADIUS = 0.15
STEP_SC = Fraction(1, 512)
SIDE_STEP = Fraction(1, 512)
OMEGA_CLEAR = Fraction(1, 32)
#: |sinc(w)| <= 1.1753 cosh(Im w) for every complex w (sinh(1) < 1.1753 covers |w| < 1)
SINC_ABS = "1.1753"

UNITS = os.path.join(HERE, "units")
TABLE = os.path.join(HERE, "ghost_table.json")


# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------


def ckey(c) -> str:
    f = Fraction(c)
    return str(f.numerator) if f.denominator == 1 else f"{f.numerator}/{f.denominator}"


def dy(x) -> arb:
    """An exact rational (dyadic on every grid used here) as an arb."""
    x = Fraction(x)
    return arb(fmpq(x.numerator, x.denominator))


def dyadic_in(x: float, den: int, up: bool) -> Fraction:
    v = x * den
    return Fraction(math.ceil(v) if up else math.floor(v), den)


def s_arb(x: arb, d: int = 15) -> str:
    return x.str(d, radius=True)


def fl(x: arb) -> float:
    return float(x.mid())


def sgn(x: arb) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0


def dh_online() -> list:
    return json.load(open(os.path.join(ROOT, "data", "dh_zeros_online_T120.json")))["zeros"]


def sham_ordinate() -> float:
    return min(dh_online(), key=lambda g: abs(g - SHAM_NEAR))


def load_json(path: str, default):
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return default


# ---------------------------------------------------------------------------
# assembly and lesions
# ---------------------------------------------------------------------------


def assemble(kind: str, c, prec: int, N: int = N_BAND):
    """(even arb_mat, odd arb_mat, L) for the band-N form at window c."""
    q = W.cq(Fraction(c))
    if kind in ("dh", "zeta"):
        bt = EN.BallTruncation(q, N, kind=kind, prec=prec)
        ctx.prec = prec
        return arb_mat(bt.even_matrix()), arb_mat(bt.odd_matrix()), bt.L
    form = W.EPSTEIN_FORM if kind == "epstein" else "dedekind-23"
    M = W.epstein_matrices(q, N, prec, form=form)
    ctx.prec = prec
    return M["even"], M["odd"], arb(q).log()


def basis_at(L: arb, z: acb, n: int) -> list:
    """[a_0(z), ..., a_{n-1}(z)] with F_v(z) = sum_k v_k a_k(z), the F_even_acb formula."""
    s2 = arb(2).sqrt()
    pi = arb.pi()
    sn = 2 * (z * L / 2).sin()
    out = [sn / z]
    for k in range(1, n):
        om = 2 * pi * k / L
        out.append(sn * s2 * z / (z * z - om * om))
    return out


def lesion_matrix(which: str, L: arb, n: int) -> arb_mat:
    """q1: (4/L) Re(a a^T) at z_1 (x^T M x = wp_common.offline_quadruple); sham: (2/L) a a^T at an on-line zero."""
    if which == "q1":
        a = basis_at(L, acb(arb(GAMMA_1), -arb(DELTA_1)), n)
        f = 4 / L
        return arb_mat(n, n, [f * (a[i].real * a[j].real - a[i].imag * a[j].imag) for i in range(n) for j in range(n)])
    if which == "sham":
        a = [t.real for t in basis_at(L, acb(arb(repr(sham_ordinate()))), n)]
        f = 2 / L
        return arb_mat(n, n, [f * a[i] * a[j] for i in range(n) for j in range(n)])
    if which == "q12":  # both off-line quadruples below 120 (exploratory, RESULTS.md s9)
        a2 = basis_at(L, acb(arb(W.GAMMA_OFF2), -arb(W.DELTA_OFF2)), n)
        f = 4 / L
        M2 = arb_mat(n, n, [f * (a2[i].real * a2[j].real - a2[i].imag * a2[j].imag) for i in range(n) for j in range(n)])
        return lesion_matrix("q1", L, n) + M2
    raise ValueError(which)


def planted_vector(L: arb, N: int, real_zeros, complex_zeros, prec: int = 256) -> arb_mat:
    """An element of the band-N even space with known zeros (PREREG s3, s4).

    V_N is the set of F(z) = 2 sin(zL/2) p(z^2) / (z q(z^2)), q(w) = prod_{k<=N}(w - omega_k^2),
    deg p <= N, and p fixes v through p(0) = v_0 prod(-omega_k^2) and
    p(omega_k^2) = sqrt2 v_k omega_k^2 prod_{j != k}(omega_k^2 - omega_j^2). With
    p(w) = prod (w - z_j^2) over the given real zeros and over each complex zero
    and its conjugate, the zeros of F in Re z > 0 are exactly those points (and
    omega_k, k > N). Returns the unit vector (exact midpoints).
    """
    ctx.prec = prec
    pi = arb.pi()
    s2 = arb(2).sqrt()
    om2 = [(2 * pi * k / L) ** 2 for k in range(1, N + 1)]
    roots = [acb(dy(z)) ** 2 for z in real_zeros]
    for z in complex_zeros:
        z0 = acb(dy(z[0]), dy(z[1]))
        roots += [z0 ** 2, z0.conjugate() ** 2]

    def p(w):
        out = acb(1)
        for r in roots:
            out *= w - r
        return out.real

    prod0 = arb(1)
    for o in om2:
        prod0 *= -o
    v = [p(acb(0)) / prod0]
    for k in range(N):
        den = s2 * om2[k]
        for j in range(N):
            if j != k:
                den *= om2[k] - om2[j]
        v.append(p(acb(om2[k])) / den)
    col = arb_mat(N + 1, 1, v)
    return W._mid_unit(col)


# ---------------------------------------------------------------------------
# ground state, CvS hypotheses, eigenvector enclosure
# ---------------------------------------------------------------------------


def _ldl(A: arb_mat, shift) -> tuple:
    M = [[A[i, j] for j in range(A.ncols())] for i in range(A.nrows())]
    return EN.ldlt_inertia(M, shift)


def ground_state(A: arb_mat, A_ldl: arb_mat, prec: int, prec_ldl: int):
    """Lowest eigenpair estimate: (x exact column, lam2 estimate, method, inertia at 0)."""
    ctx.prec = prec_ldl
    npos, nneg, concl = _ldl(A_ldl, arb(0))
    ctx.prec = prec
    if concl and nneg == 0:
        (r1, x), (r2, _) = W.lowest_pairs(A, 2, iters=8)
        return x, float(r2.mid()), "inverse iteration at shift 0 (positive definite by ball LDL)", [npos, nneg, concl]
    ev = W.approx_spectrum(A, 3)
    _, x = W.eig_near(A, ev[0], iters=10)
    x = W._fix_sign(x)
    return x, ev[1], "shifted inverse iteration at the lowest approximate eigenvalue", [npos, nneg, concl]


def residual_upper(A: arb_mat, x: arb_mat, rho: arb) -> arb:
    """An upper bound for ||A x - rho x|| that stays finite when the residual is at
    rounding level: the square root of sum |r_i|_upper^2, never of a ball reaching
    below 0 (``wp_common.residual_norm`` takes sqrt of the dot product, which is NaN
    once the ball contains negative numbers; that voided the first c = 31 unit)."""
    r = A * x - x * rho
    e2 = arb(0)
    for i in range(r.nrows()):
        u = abs(r[i, 0]).upper()
        e2 += u * u
    return e2.sqrt().upper()


def hypotheses(A_ldl: arb_mat, A_odd_ldl, x: arb_mat, lam2_est: float, prec_ldl: int) -> dict:
    """H1, H3, H2 and the Davis-Kahan eigenvector radius eta, from balls at prec_ldl."""
    ctx.prec = prec_ldl
    nx = W.dot(x, x).sqrt()
    rho = W.rq(A_ldl, x)
    eps = residual_upper(A_ldl, x, rho) / nx.lower()
    s = arb(repr((float(rho.mid()) + lam2_est) / 2)).mid()
    npos, nneg, concl = _ldl(A_ldl, s)
    h1 = bool(concl and nneg == 1 and rho < s)
    out = {"rq": s_arb(rho, 20), "residual": eps.str(5), "shift": s.str(12),
           "ldl_at_shift": [npos, nneg, bool(concl)], "prec_ldl": prec_ldl,
           "H1_simple": h1, "lam2_estimate": lam2_est}
    if not h1:
        out.update({"H3_isolated": False, "eta": None, "H2_even": None})
        return out
    if not math.isfinite(float(eps.mid())):
        out.update({"H3_isolated": None, "eta": None, "H2_even": None,
                    "enclosure_defect": "residual bound not finite; no eigenvector enclosure"})
        return out
    gap = s - rho
    lo = rho - eps * eps / gap
    out.update({"H3_isolated": True, "gap_lower": gap.lower().str(6),
                "eta": (arb(2).sqrt() * eps / gap).upper().str(6),
                "lam1_bracket": [lo.lower().str(20), rho.upper().str(20)]})
    if A_odd_ldl is None:
        out["H2_even"] = None
        out["H2_detail"] = "not decided (lesioned even form; the odd sector is not lesioned)"
        return out
    pu, nu, cu = _ldl(A_odd_ldl, rho.upper())
    if cu and nu == 0:
        h2, why = True, "odd LDL at the even upper bound is positive definite"
    else:
        pl, nl, cl = _ldl(A_odd_ldl, lo.lower())
        if cl and nl >= 1:
            h2, why = False, f"odd LDL at the even lower bound has {nl} negative pivot(s)"
        else:
            h2, why = None, f"undecided: odd LDL at upper {[pu, nu, cu]}, at lower {[pl, nl, cl]}"
    out["H2_even"] = h2
    out["H2_detail"] = why
    return out


# ---------------------------------------------------------------------------
# the transform: point values, Taylor models, bounds
# ---------------------------------------------------------------------------


class Transform:
    """F_x for an exact column x, with the bounds the counter needs.

    ``value`` and ``real_value`` enclose ||x|| F_v, v the true unit eigenvector
    (within eta of x/||x||), so their signs and zeros are those of F_v.
    """

    def __init__(self, x: arb_mat, L: arb, prec: int, eta):
        ctx.prec = prec
        self.prec = prec
        self.x = x
        self.L = L
        self.n = x.nrows()
        self.xs = [x[i, 0] for i in range(self.n)]
        pi = arb.pi()
        self.om = [2 * pi * k / L for k in range(self.n)]
        s2h = arb(2).sqrt() / 2
        self.coef = [None] + [s2h * self.xs[k] for k in range(1, self.n)]
        self.x_l1 = sum((abs(t) for t in self.xs), arb(0)).upper()
        self.x_norm = W.dot(x, x).sqrt().upper()
        self.eta = arb(0) if eta is None else arb(eta)
        self.sqrtn = arb(self.n).sqrt()
        self._cache = {}

    def B(self, y) -> arb:
        """Upper bound for max_k |a_k(z)| on |Im z| <= y, Re z >= 0:
        a_k(z) = sqrt2 L (-1)^k z sinc((z - omega_k) L/2) / (z + omega_k), |z/(z + omega_k)| <= 1."""
        return (arb(2).sqrt() * self.L * arb(SINC_ABS) * (arb(y) * self.L / 2).cosh()).upper()

    def pert(self, y) -> arb:
        """Bound on | ||x|| F_v(z) - F_x(z) | for |Im z| <= y (Cauchy-Schwarz with the Davis-Kahan radius)."""
        return (self.x_norm * self.eta * self.sqrtn * self.B(y)).upper()

    def value(self, z: acb, key=None) -> acb:
        if key is not None and key in self._cache:
            return self._cache[key]
        ctx.prec = self.prec
        F = W.F_even_acb(self.x, self.L, z)
        e = self.pert(abs(z.imag).upper())
        out = F + acb(arb(0, e), arb(0, e))
        if key is not None:
            self._cache[key] = out
        return out

    def real_value(self, t: arb) -> arb:
        ctx.prec = self.prec
        return W.F_even_acb(self.x, self.L, acb(t)).real + arb(0, self.pert(0))

    def taylor(self, zc: acb, K: int) -> list:
        """F_n(zc), n < K, with F_x(zc + t) = sum F_n t^n, from
        F = 2 sin(zL/2) R(z), R(z) = x_0/z + (sqrt2/2) sum_k x_k [1/(z - omega_k) + 1/(z + omega_k)]."""
        ctx.prec = self.prec
        L = self.L
        th = zc * L / 2
        sn, cs = th.sin(), th.cos()
        cyc = (sn, cs, -sn, -cs)
        S = []
        f = arb(1)
        hl = L / 2
        for m in range(K):
            S.append(cyc[m % 4] * f)
            f = f * hl / (m + 1)
        R = [acb(0)] * K
        u = 1 / zc
        p = u
        x0 = self.xs[0]
        for nn in range(K):
            R[nn] += x0 * p
            p = p * u
        for k in range(1, self.n):
            ck = self.coef[k]
            om = self.om[k]
            u1 = 1 / (zc - om)
            u2 = 1 / (zc + om)
            p1, p2 = u1, u2
            for nn in range(K):
                R[nn] += ck * (p1 + p2)
                p1 = p1 * u1
                p2 = p2 * u2
        for nn in range(1, K, 2):
            R[nn] = -R[nn]
        out = []
        for nn in range(K):
            acc = acb(0)
            for m in range(nn + 1):
                acc += S[m] * R[nn - m]
            out.append(2 * acc)
        return out


# ---------------------------------------------------------------------------
# the counter: Arb argument principle and sign changes
# ---------------------------------------------------------------------------


def _segment(T: Transform, p0, p1, stats: dict):
    """(accepted, arg increment) for the segment p0 -> p1 (exact rational endpoints).

    Accepted when the Taylor model at the centre, with Cauchy remainder
    M q^K / (1 - q) and the eigenvector term, keeps F within |F_0| sin(pi/4)
    of F_0 on the whole segment: then F has no zero there, its arg moves by
    less than pi/2, and the increment is the principal arg of F(p1)/F(p0).
    """
    zc = acb(dy((p0[0] + p1[0]) / 2), dy((p0[1] + p1[1]) / 2))
    r = dy((abs(p1[0] - p0[0]) + abs(p1[1] - p0[1])) / 2)  # axis-aligned segments: exact half-length
    rho = 16 * r
    if rho > arb("0.5"):
        rho = arb("0.5")
    q = r / rho
    yc = abs(zc.imag).upper()
    M = (T.x_l1 * T.B(yc + rho)).upper()
    a0 = abs(T.taylor(zc, 1)[0]).lower()
    if not a0 > 0:
        return False, None
    need = float((M / (a0 * arb("0.001") * (1 - q))).log().upper())
    K = max(2, int(math.ceil(need / -float(q.log().upper()))) + 1)
    if K > 90:
        return False, None
    Fn = T.taylor(zc, K)
    delta = M * q ** K / (1 - q) + T.pert(yc + r)
    rp = arb(1)
    for nn in range(1, K):
        rp = rp * r
        delta += abs(Fn[nn]) * rp
    stats["segments"] += 1
    stats["max_K"] = max(stats["max_K"], K)
    if not (delta < abs(Fn[0]) * arb("0.7071")):
        return False, None
    g0 = T.value(acb(dy(p0[0]), dy(p0[1])), key=p0)
    g1 = T.value(acb(dy(p1[0]), dy(p1[1])), key=p1)
    inc = (g1 / g0).arg()
    if not inc.rad() < arb("0.01"):
        return False, None
    return True, inc


def winding(T: Transform, a: Fraction, b: Fraction, h: Fraction, max_depth: int = 20) -> dict:
    """Arb argument principle on [a, b] x [-h, h].

    F is real on the real line (F(conj z) = conj F(z)), so the arg change on
    the lower half of the boundary equals that on the upper half: the count is
    twice the arg change along (b, 0) -> (b, h) -> (a, h) -> (a, 0), over 2 pi.
    """
    path = [(b, Fraction(0)), (b, h), (a, h), (a, Fraction(0))]
    stats = {"segments": 0, "max_K": 0, "max_depth": 0}
    total = arb(0)
    for (xa, ya), (xb, yb) in zip(path[:-1], path[1:]):
        length = abs(xb - xa) + abs(yb - ya)
        piece = Fraction(1, 8) if ya == yb else Fraction(1, 32)
        m = max(1, math.ceil(length / piece))
        pts = [(xa + (xb - xa) * Fraction(j, m), ya + (yb - ya) * Fraction(j, m)) for j in range(m + 1)]
        stack = [((pts[j], pts[j + 1]), 0) for j in range(m)][::-1]
        while stack:
            (p0, p1), depth = stack.pop()
            ok, inc = _segment(T, p0, p1, stats)
            if ok:
                total += inc
                stats["max_depth"] = max(stats["max_depth"], depth)
                continue
            if depth >= max_depth:
                return {"closed": False, "failed_at": [float(p0[0]), float(p0[1]), float(p1[0]), float(p1[1])], **stats}
            mid = ((p0[0] + p1[0]) / 2, (p0[1] + p1[1]) / 2)
            stack.append(((mid, p1), depth + 1))
            stack.append(((p0, mid), depth + 1))
    wnum = 2 * total / (2 * arb.pi())
    k = round(float(wnum.mid()))
    closed = bool(wnum.rad() < arb("0.25") and (wnum - k).contains(0))
    return {"closed": closed, "n_AP": k if closed else None, "winding": wnum.str(8, radius=True), **stats}


def clear_of_omega(T: Transform, x: Fraction) -> bool:
    xa = dy(x)
    lim = dy(OMEGA_CLEAR)
    return all(abs(xa - om) > lim for om in T.om[1:])


def count_rect(T: Transform, lo: float, hi: float, h: Fraction) -> dict:
    """AP count with dyadic vertical sides moved inward (steps of 1/512) until
    clear of every omega_k by 1/32 and until the count closes."""
    a = dyadic_in(lo, 1024, up=True)
    b = dyadic_in(hi, 1024, up=False)
    moves = 0
    while not clear_of_omega(T, a):
        a += SIDE_STEP
        moves += 1
    while not clear_of_omega(T, b):
        b -= SIDE_STEP
        moves += 1
    for _ in range(12):
        res = winding(T, a, b, h)
        if res["closed"]:
            res.update({"a": str(a), "b": str(b), "a_float": float(a), "b_float": float(b),
                        "h": str(h), "side_moves": moves})
            return res
        fa = res.get("failed_at") or [float(a)]
        if abs(fa[0] - float(a)) <= abs(fa[0] - float(b)):
            a += SIDE_STEP
            while not clear_of_omega(T, a):
                a += SIDE_STEP
        else:
            b -= SIDE_STEP
            while not clear_of_omega(T, b):
                b -= SIDE_STEP
        moves += 1
    return {"closed": False, "n_AP": None, "a": str(a), "b": str(b), "h": str(h), "side_moves": moves}


def sign_scan(T: Transform, lo: float, hi: float, bits: int, step: Fraction = STEP_SC) -> dict:
    """Signs of F_v at the multiples of ``step`` in [lo, hi]; each sign change
    bisected (exact dyadic midpoints, ball signs) to width 2^-bits."""
    j0 = math.ceil(lo / float(step))
    j1 = math.floor(hi / float(step))
    pts = [step * j for j in range(j0, j1 + 1)]
    signs = [sgn(T.real_value(dy(t))) for t in pts]
    undecided = [float(t) for t, s in zip(pts, signs) if s == 0]
    zeros = []
    for i in range(len(pts) - 1):
        s0, s1 = signs[i], signs[i + 1]
        if s0 and s1 and s0 != s1:
            a, b = pts[i], pts[i + 1]
            for _ in range(bits - 9):
                m = (a + b) / 2
                sm = sgn(T.real_value(dy(m)))
                if sm == 0:
                    break
                if sm == s0:
                    a = m
                else:
                    b = m
            zeros.append({"lo": str(a), "hi": str(b), "x": float((a + b) / 2), "width": float(b - a)})
    return {"n_points": len(pts), "n_SC": len(zeros), "zeros": zeros, "undecided_points": undecided,
            "step": str(step), "lo": lo, "hi": hi}


# ---------------------------------------------------------------------------
# windows per kind (PREREG s5)
# ---------------------------------------------------------------------------


def windows_for(kind: str) -> dict:
    g1 = float(GAMMA_1)
    gE = float(GAMMA_E)
    r = float(GHOST_RADIUS)
    half, tf = Fraction(1, 2), Fraction(3, 5)
    if kind == "dh":
        return {"gap": (83.109, 87.647, half), "ghost": (g1 - r, g1 + r, half), "ctx": (80.5, 90.5, half)}
    if kind == "zeta":
        return {"gap": (float(ZETA_23) + 0.01, float(ZETA_24) - 0.01, half),
                "ghost": (g1 - r, g1 + r, half), "ctx": (80.5, 90.5, half)}
    out = {"ghost": (gE - r, gE + r, tf), "ctx": (12.0, 21.0, tf)}
    if kind == "epstein":
        gap = load_json(TABLE, {}).get("windows", {}).get("epstein_gap")
        if gap:
            out["gap"] = (gap[0], gap[1], tf)
    return out


def ref_ordinate(kind: str) -> float:
    return float(GAMMA_1) if kind in ("dh", "zeta") else float(GAMMA_E)


def online_zeros(kind: str) -> list:
    if kind == "dh":
        return dh_online()
    if kind == "zeta":
        from mpmath import mp
        with mp.workdps(20):
            return [float(mp.zetazero(n).imag) for n in range(1, 41)]
    win = load_json(TABLE, {}).get("windows", {})
    return win.get("epstein_online" if kind == "epstein" else "dedekind_online", [])


# ---------------------------------------------------------------------------
# one unit
# ---------------------------------------------------------------------------


def basis_variant(variant: str):
    """'N64', 'N192', 'N256': the exploratory basis-size response (RESULTS.md says it was
    chosen after the primary numbers); returns (N, (prec, prec_ldl)) or None."""
    if variant.startswith("N") and variant[1:].isdigit():
        n = int(variant[1:])
        return n, ((400, 400) if n <= 192 else (600, 800))
    return None


def unit(kind: str, c, variant: str = "primary") -> dict:
    t0 = time.time()
    bv = basis_variant(variant)
    N = bv[0] if bv else N_BAND
    if bv:
        if kind != "dh":
            raise ValueError("the basis-size response is run for dh only")
        prec, prec_ldl = bv[1]
    else:
        pv = "primary" if variant in ("q1", "sham") or variant.startswith("scan") else variant
        prec, prec_ldl = PRECS[pv][kind]
    lesion = variant if variant in ("q1", "sham") else None
    if lesion and kind != "dh":
        raise ValueError("lesions act on dh only")
    A, Aodd, L = assemble(kind, c, prec, N)
    if lesion:
        A = A - lesion_matrix(lesion, L, A.nrows())
    if prec_ldl != prec:
        A3, A3odd, L3 = assemble(kind, c, prec_ldl, N)
        if lesion:
            A3 = A3 - lesion_matrix(lesion, L3, A3.nrows())
    else:
        A3, A3odd = A, Aodd
    x, lam2, method, inert0 = ground_state(A, A3, prec, prec_ldl)
    hyp = hypotheses(A3, None if lesion else A3odd, x, lam2, prec_ldl)
    if not hyp["H1_simple"]:
        # one retry of the LDL steps at double precision (wp_common.ldl_prec's note)
        P2 = 2 * prec_ldl
        A3, A3odd, L3 = assemble(kind, c, P2, N)
        if lesion:
            A3 = A3 - lesion_matrix(lesion, L3, A3.nrows())
        hyp = hypotheses(A3, None if lesion else A3odd, x, lam2, P2)
        hyp["ldl_retry"] = True
    ctx.prec = prec
    T = Transform(x, L, prec, hyp.get("eta"))
    rec = {"kind": kind, "c": ckey(c), "c_float": float(Fraction(c)), "variant": variant, "N": N,
           "prec": prec, "L": fl(L), "eigen_method": method, "inertia_at_0": inert0, **hyp,
           "mu0": W.mu0(x).str(10, radius=True), "v_head": [fl(x[i, 0]) for i in range(6)],
           "band_edge": 2 * math.pi * N / fl(L)}
    nx2 = W.dot(x, x)
    if kind == "dh":
        rec["Q1"] = (W.offline_quadruple(x, L, GAMMA_1, DELTA_1) / nx2).str(10, radius=True)
        rec["Q2"] = (W.offline_quadruple(x, L, W.GAMMA_OFF2, W.DELTA_OFF2) / nx2).str(10, radius=True)
    if kind == "epstein":
        rec["Q_E"] = (W.offline_quadruple(x, L, GAMMA_E, DELTA_E) / nx2).str(10, radius=True)
    rects = {}
    for name, (lo, hi, h) in windows_for(kind).items():
        t1 = time.time()
        ap = count_rect(T, lo, hi, h)
        sc = sign_scan(T, lo, hi, BISECT_BITS[kind])
        rects[name] = {"nominal": [lo, hi], "AP": ap, "SC": sc, "elapsed_s": round(time.time() - t1, 1)}
    rec["rects"] = rects
    rec.update(classify(kind, rec))
    rec["elapsed_s"] = round(time.time() - t0, 1)
    return rec


def classify(kind: str, rec: dict) -> dict:
    """Ghost decision and S1 bookkeeping for one unit (PREREG s5 to s7)."""
    g = ref_ordinate(kind)
    r = float(GHOST_RADIUS)
    on = online_zeros(kind)
    within = []
    for zr in rec["rects"]["ghost"]["SC"]["zeros"]:
        lo, hi = float(Fraction(zr["lo"])), float(Fraction(zr["hi"]))
        if lo >= g - r and hi <= g + r:
            acc = [y for y in on if abs(y - zr["x"]) <= ACCOUNT_RADIUS]
            within.append({"x": zr["x"], "lo": zr["lo"], "hi": zr["hi"], "dist": zr["x"] - g, "accounted_by": acc})
    ghosts = [w for w in within if not w["accounted_by"]]
    out = {"ghost": bool(ghosts), "ghosts": ghosts, "zeros_within_radius": within}
    ctxz = rec["rects"]["ctx"]["SC"]["zeros"]
    if ctxz:
        nz = min(ctxz, key=lambda zr: abs(zr["x"] - g))
        out["nearest_zero_to_ref"] = {"x": nz["x"], "dist": nz["x"] - g}
    s1 = {}
    for name, rr in rec["rects"].items():
        ap = rr["AP"]
        if ap.get("closed"):
            a, b = Fraction(ap["a"]), Fraction(ap["b"])
            zs = rr["SC"]["zeros"]
            n_in = sum(1 for zr in zs if Fraction(zr["lo"]) >= a and Fraction(zr["hi"]) <= b)
            strad = sum(1 for zr in zs if Fraction(zr["lo"]) < a < Fraction(zr["hi"]) or Fraction(zr["lo"]) < b < Fraction(zr["hi"]))
            s1[name] = {"n_AP": ap["n_AP"], "n_SC_inside": n_in, "straddling_side": strad,
                        "equal": ap["n_AP"] == n_in and strad == 0}
        else:
            s1[name] = {"n_AP": None, "n_SC_inside": None, "equal": None}
    out["S1"] = s1
    acc = []
    for zr in ctxz:
        near = sorted((y for y in on if abs(y - zr["x"]) <= ACCOUNT_RADIUS), key=lambda y: abs(y - zr["x"]))
        acc.append({"x": zr["x"], "accounted_by": near[0] if near else None,
                    "offset": (zr["x"] - near[0]) if near else None})
    out["ctx_accounting"] = acc
    lo, hi = rec["rects"]["ctx"]["nominal"]
    out["online_in_ctx"] = [y for y in on if lo < y < hi]
    return out


# ---------------------------------------------------------------------------
# S2: Q1 against its first-order prediction from the zero nearest gamma_1
# ---------------------------------------------------------------------------


def s2_check(c, variant: str = "primary") -> dict:
    prec, _ = PRECS["primary"]["dh"]
    A, _, L = assemble("dh", c, prec)
    if variant == "q1":
        A = A - lesion_matrix("q1", L, A.nrows())
    x, _, _, _ = ground_state(A, A, prec, prec)
    T = Transform(x, L, prec, None)
    g1, d1 = float(GAMMA_1), float(DELTA_1)
    sc = sign_scan(T, g1 - 1.2, g1 + 1.2, 60)
    if not sc["zeros"]:
        return {"x_g": None}
    zg = min(sc["zeros"], key=lambda zr: abs(zr["x"] - g1))
    xg = (Fraction(zg["lo"]) + Fraction(zg["hi"])) / 2
    Fn = T.taylor(acb(dy(xg)), 3)
    nx2 = W.dot(x, x)
    q1 = W.offline_quadruple(x, L, GAMMA_1, DELTA_1) / nx2
    d = arb(GAMMA_1) - dy(xg)
    pred = 4 / L * Fn[1].real ** 2 / nx2 * (d * d - arb(DELTA_1) ** 2)
    dd = float(d.mid())
    return {"x_g": float(xg), "dist": -dd, "Q1": q1.str(8), "Q1_first_order": pred.str(8),
            "ratio": fl(q1 / pred) if not pred.contains(0) else None,
            "sign_rule_applies": abs(abs(dd) - d1) > 0.05,
            "sign_rule_holds": sgn(q1) == (1 if abs(dd) > d1 else -1)}


# ---------------------------------------------------------------------------
# control windows: Epstein and zeta_K on-line zeros in [12, 21]
# ---------------------------------------------------------------------------


def _kron_m23(n: int) -> int:
    """Kronecker symbol (-23/n), n >= 1."""
    from sympy import jacobi_symbol

    res = 1
    while n % 2 == 0:
        n //= 2
        res *= 1  # (-23/2) = 1 since -23 = 1 mod 8
    return res if n == 1 else res * int(jacobi_symbol(-23 % n, n))


def windows_cmd():
    """On-line zeros in [12, 21] for the Epstein and zeta_K windows.

    Deviation from PREREG s5, decided before any Epstein or Dedekind ground state
    existed and recorded in RESULTS.md: one Z_epstein evaluation took about 10 s on
    the loaded box, so the preregistered Z_epstein scan (step 1/100) would have
    taken hours. The zero lists come from PARI's lfunzeros instead (lfunqf for the
    form, lfuncreate(x^2 + x + 6) for zeta_K), and every listed zero is confirmed
    by a sign change of the lab's own routes at +-0.01: Z_epstein((1,1,6)) for
    Epstein, Z_(1,1,6) + 2 Z_(2,1,3) for zeta_K; zeta_K's list is also rebuilt
    from mpmath (zetazero plus sign changes of the completed L(1/2 + it, chi_-23),
    step 1/50, mpmath.dirichlet) and the two lists compared.
    """
    import cypari2
    from mpmath import mp

    from zeta.epstein import Z_epstein

    pari = cypari2.Pari()
    pari.set_real_precision(38)
    tab = load_json(TABLE, {})
    win = tab.setdefault("windows", {})
    t0 = time.time()

    def scan(fn, lo, hi, den, dps, bis=34):
        with mp.workdps(dps):
            ts = [mp.mpf(j) / den for j in range(lo * den, hi * den + 1)]
            vals = [fn(t) for t in ts]
            zs = []
            for i in range(len(ts) - 1):
                if vals[i] * vals[i + 1] < 0:
                    a, b, fa = ts[i], ts[i + 1], vals[i]
                    for _ in range(bis):
                        m = (a + b) / 2
                        fm = fn(m)
                        if fm * fa > 0:
                            a, fa = m, fm
                        else:
                            b = m
                    zs.append(float((a + b) / 2))
            return zs

    if "epstein_online" not in win:
        ze = [float(z) for z in pari.lfunzeros(pari("lfunqf([2,1;1,12])"), pari("[12,21]"))]
        conf = []
        for z in ze:
            f = [Z_epstein(z + e, (1, 1, 6), dps=36) for e in (-0.01, 0.01)]
            conf.append(bool(f[0] * f[1] < 0))
        win["epstein_online"] = ze
        win["epstein_confirmed_by_Z_epstein_sign_change"] = conf
        win["epstein_route"] = ("PARI lfunzeros(lfunqf([2,1;1,12]), [12,21]) at 38 digits; each zero confirmed by a sign "
                                "change of zeta.epstein.Z_epstein(t, (1,1,6)) at t +- 0.01, dps 36")
        gE = float(GAMMA_E)
        below = [z for z in ze if z < gE]
        above = [z for z in ze if z > gE]
        win["epstein_gap"] = [max(below), min(above)] if below and above else None
        W.save(TABLE, tab)
        print("epstein on-line", ze, conf, f"[{time.time() - t0:.0f} s]", flush=True)
    if "dedekind_online" not in win:
        zp = [float(z) for z in pari.lfunzeros(pari("lfuncreate(x^2+x+6)"), pari("[12,21]"))]
        chi = [0] + [_kron_m23(n) for n in range(1, 23)]
        with mp.workdps(30):
            zz = [float(mp.zetazero(n).imag) for n in range(1, 6)]

            def ZL(t):
                s = mp.mpc(0.5, t)
                return mp.re((mp.mpf(23) / mp.pi) ** (s / 2) * mp.gamma((s + 1) / 2) * mp.dirichlet(s, chi))

            zl = scan(ZL, 12, 21, 50, 30)
        zm = sorted([z for z in zz if 12 < z < 21] + zl)
        agree = len(zm) == len(zp) and all(abs(a - b) < 1e-8 for a, b in zip(zm, zp))
        cross = []
        for z in zp:
            f = [Z_epstein(z + e, (1, 1, 6), dps=36) + 2 * Z_epstein(z + e, (2, 1, 3), dps=36) for e in (-0.01, 0.01)]
            cross.append(bool(f[0] * f[1] < 0))
        win["dedekind_online"] = zp
        win["dedekind_mpmath_list"] = zm
        win["dedekind_lists_agree_to_1e-8"] = agree
        win["dedekind_L_chi_zeros"] = zl
        win["dedekind_confirmed_by_classgroup_sign_change"] = cross
        win["dedekind_route"] = ("PARI lfunzeros(lfuncreate(x^2+x+6), [12,21]); mpmath: zetazero plus sign changes of the "
                                 "completed L(1/2 + it, chi_-23) (mpmath.dirichlet, dps 30, step 1/50); class-group sign "
                                 "change Z_(1,1,6) + 2 Z_(2,1,3) at t +- 0.01, dps 36")
        W.save(TABLE, tab)
        print("dedekind on-line", zp, agree, cross, f"[{time.time() - t0:.0f} s]", flush=True)


# ---------------------------------------------------------------------------
# float route (mpmath only)
# ---------------------------------------------------------------------------


def _float_epstein(cm, N: int, kind: str):
    """mpmath twin of wp_common.epstein_matrices (even sector) from galerkin.Truncation pieces;
    Lambda_Q from zeta.epstein.log_derivative_coefficients."""
    import copy

    from mpmath import mp

    import galerkin as GK
    from zeta.epstein import epstein_representation_count as rep
    from zeta.epstein import log_derivative_coefficients as ldc

    nmax = int(mp.floor(cm))
    if kind == "epstein":
        cnt = [0] + [rep(k, (1, 1, 6)) for k in range(1, nmax + 1)]
    else:
        cnt = [0] + [rep(k, (1, 1, 6)) + 2 * rep(k, (2, 1, 3)) for k in range(1, nmax + 1)]
    coeff = [mp.mpf(0)] + [mp.mpf(cnt[k]) / cnt[1] for k in range(1, nmax + 1)]
    lam = ldc(lambda n: coeff[n], nmax, dps=mp.dps)
    tz = GK.Truncation(cm, N, kind="zeta")
    td = GK.Truncation(cm, N, kind="dh")
    L = tz.L
    P = [mp.mpf(0)] * (N + 1)
    R = [mp.mpf(0)] * (N + 1)
    for q in range(2, nmax + 1):
        lq = mp.mpf(lam[q])
        if lq == 0:
            continue
        y = mp.log(q)
        w = lq / mp.sqrt(q)
        for k in range(N + 1):
            om = 2 * mp.pi * k / L
            P[k] += w * mp.sin(om * y)
            R[k] += w * 2 * (1 - y / L) * mp.cos(om * y)
    t1 = copy.copy(tz)
    t1._P, t1._R = P, R
    t2 = copy.copy(td)
    t2._P = [mp.mpf(0)] * (N + 1)
    t2._R = [mp.mpf(0)] * (N + 1)
    E = t1.even_matrix() + t2.even_matrix()
    sh = mp.log(mp.mpf(23) / 5)
    for i in range(N + 1):
        E[i, i] += sh
    return E


def _mp_inertia(M):
    """(n_neg, smallest |pivot|) of a symmetric mpmath matrix by LDL^T without pivoting (float grade)."""
    n = M.rows
    A = [[M[i, j] for j in range(n)] for i in range(n)]
    neg = 0
    small = None
    for j in range(n):
        d = A[j][j]
        if d == 0:
            return -1, 0
        if d < 0:
            neg += 1
        small = abs(d) if small is None or abs(d) < small else small
        rowj = A[j]
        for i in range(j + 1, n):
            f = A[i][j] / d
            if f == 0:
                continue
            Ai = A[i]
            for k in range(j + 1, n):
                Ai[k] -= f * rowj[k]
    return neg, small


def float_route(kind: str, c) -> dict:
    import numpy as np
    from mpmath import mp

    import galerkin as GK

    t0 = time.time()
    dps = 320 if kind == "zeta" else 60
    fc = Fraction(c)
    prim = load_json(_unit_path("primary", kind), {}).get(ckey(c), {})
    with mp.workdps(dps):
        cm = mp.mpf(fc.numerator) / fc.denominator
        E = GK.Truncation(cm, N_BAND, kind=kind).even_matrix() if kind in ("dh", "zeta") else _float_epstein(cm, N_BAND, kind)
        n = E.rows
        evf = np.linalg.eigvalsh(np.array([[float(E[i, j]) for j in range(n)] for i in range(n)]))
        low = float(evf[0])
        sigma = mp.mpf(0) if abs(low) < 1e-9 * float(max(abs(evf))) else mp.mpf(low)
        LU, perm = mp.LU_decomp(E - sigma * mp.eye(n))

        def solve(b):
            return mp.U_solve(LU, mp.L_solve(LU, b, perm))

        x = mp.matrix([mp.mpf(1) + mp.mpf(i * 7919 % 97) / 97 for i in range(n)])
        for _ in range(10):
            x = solve(x)
            x = x / mp.norm(x)
        if x[0] < 0:
            x = -x
        lam1 = (x.T * E * x)[0]
        y = mp.matrix([mp.mpf(1) + mp.mpf(i * 104729 % 89) / 89 for i in range(n)])
        for _ in range(12):
            y = solve(y)
            y = y - x * (x.T * y)[0]
            y = y / mp.norm(y)
        lam2 = (y.T * E * y)[0]
        res = mp.norm(E * x - lam1 * x)
        nneg, piv = _mp_inertia(E - ((lam1 + lam2) / 2) * mp.eye(n))
        L = mp.log(cm)
        xs = [x[i] for i in range(n)]
        s2 = mp.sqrt(2)
        oms = [2 * mp.pi * k / L for k in range(n)]

        def F(z):
            tot = xs[0] * mp.sinc(z * L / 2)
            for k in range(1, n):
                term = s2 * xs[k] * z * mp.sinc((z - oms[k]) * L / 2) / (z + oms[k])
                tot += term if k % 2 == 0 else -term
            return L * tot

        rects = {}
        for name, (lo, hi, h) in windows_for(kind).items():
            zs = _mp_real_zeros(F, lo, hi, mp)
            ap = prim.get("rects", {}).get(name, {}).get("AP", {})
            if ap.get("closed"):
                a = mp.mpf(Fraction(ap["a"]).numerator) / Fraction(ap["a"]).denominator
                b = mp.mpf(Fraction(ap["b"]).numerator) / Fraction(ap["b"]).denominator
            else:
                a = mp.mpf(dyadic_in(lo, 1024, True).numerator) / 1024
                b = mp.mpf(dyadic_in(hi, 1024, False).numerator) / 1024
            wn = _mp_winding(F, a, b, mp.mpf(h.numerator) / h.denominator, mp)
            inside = [z for z in zs if float(a) < z < float(b)]
            rects[name] = {"real_zeros": zs, "n_real": len(zs), "n_real_inside_rect": len(inside),
                           "rect": [float(a), float(b)], "winding": wn}
        out = {"kind": kind, "c": ckey(c), "dps": dps, "lam1": mp.nstr(lam1, 15), "lam2": mp.nstr(lam2, 8),
               "residual": mp.nstr(res, 5), "n_neg_at_midshift": nneg, "smallest_pivot": mp.nstr(piv, 5),
               "seed_shift": mp.nstr(sigma, 8), "rects": rects, "elapsed_s": round(time.time() - t0, 1)}
    return out


def _mp_real_zeros(F, lo, hi, mp, den=256, bis=48):
    ts = [mp.mpf(j) / den for j in range(math.ceil(lo * den), math.floor(hi * den) + 1)]
    vals = [mp.re(F(t)) for t in ts]
    out = []
    for i in range(len(ts) - 1):
        if vals[i] * vals[i + 1] < 0:
            a, b, fa = ts[i], ts[i + 1], vals[i]
            for _ in range(bis):
                m = (a + b) / 2
                fm = mp.re(F(m))
                if fm * fa > 0:
                    a, fa = m, fm
                else:
                    b = m
            out.append(float((a + b) / 2))
    return out


def _mp_winding(F, a, b, h, mp, tol=0.25, max_depth=16):
    """Sampled winding number of F around [a, b] x [-h, h], full contour, refined
    wherever one step turns the arg by more than ``tol``."""
    corners = [mp.mpc(a, -h), mp.mpc(b, -h), mp.mpc(b, h), mp.mpc(a, h), mp.mpc(a, -h)]
    total = mp.mpf(0)
    evals = 0
    for z0, z1 in zip(corners[:-1], corners[1:]):
        m = int(mp.ceil(abs(z1 - z0) / mp.mpf("0.02")))
        pts = [z0 + (z1 - z0) * j / m for j in range(m + 1)]
        vals = [F(p) for p in pts]
        evals += len(pts)
        for j in range(m):
            stack = [(pts[j], pts[j + 1], vals[j], vals[j + 1], 0)]
            while stack:
                p0, p1, f0, f1, d = stack.pop()
                inc = mp.arg(f1 / f0)
                if abs(inc) > tol and d < max_depth:
                    pm = (p0 + p1) / 2
                    fm = F(pm)
                    evals += 1
                    stack.append((pm, p1, fm, f1, d + 1))
                    stack.append((p0, pm, f0, fm, d + 1))
                else:
                    total += inc
    w = total / (2 * mp.pi)
    k = int(mp.nint(w))
    return {"n": k, "defect": float(abs(w - k)), "integral": bool(abs(w - k) < 1e-6), "evals": evals}


# ---------------------------------------------------------------------------
# summary: merge and decide (PREREG s6, s7)
# ---------------------------------------------------------------------------


def _unit_path(variant: str, kind: str) -> str:
    os.makedirs(UNITS, exist_ok=True)
    return os.path.join(UNITS, f"{variant}_{kind}.json")


def _zlist(rec, name):
    return [Fraction(z["lo"]) for z in rec["rects"][name]["SC"]["zeros"]], rec["rects"][name]["SC"]["zeros"]


def nominal_count(rec: dict, name: str):
    """Zeros of F_v in the nominal rectangle ``name`` (before any side moved), read
    from R_ctx. When R_ctx's count closed and equals its sign changes with no bracket
    on a side (S1), every zero of F_v in R_ctx is real, simple and alone in one
    bracket, so the zeros in a nominal sub-rectangle of R_ctx (same or smaller
    half-height) are the brackets inside it. None when that reading does not apply."""
    rects = rec.get("rects", {})
    cx, rr = rects.get("ctx"), rects.get(name)
    if not cx or not rr or not rec.get("S1", {}).get("ctx", {}).get("equal"):
        return None
    lo, hi = Fraction(rr["nominal"][0]), Fraction(rr["nominal"][1])
    if not (Fraction(cx["AP"]["a"]) <= lo and hi <= Fraction(cx["AP"]["b"])):
        return None
    if Fraction(rr["AP"].get("h", cx["AP"]["h"])) > Fraction(cx["AP"]["h"]):
        return None
    n = 0
    for z in cx["SC"]["zeros"]:
        zl, zh = Fraction(z["lo"]), Fraction(z["hi"])
        if lo <= zl and zh <= hi:
            n += 1
        elif zl < lo < zh or zl < hi < zh:
            return None
    return n


def summarize() -> dict:
    tab = load_json(TABLE, {})
    # a unit file missing from units/ keeps the table's copy (never wipe the record)
    units = dict(tab.get("units", {}))
    for p in sorted(glob.glob(os.path.join(UNITS, "*.json"))):
        name = os.path.basename(p)[:-5]
        units[name] = load_json(p, {})
    tab["units"] = units
    pr = units.get("primary_dh", {})
    dec = {}
    # P
    before = [pr.get(c) for c in C_BEFORE]
    if all(before):
        conf = [c for c in C_BEFORE if pr[c]["H1_simple"] and pr[c]["ghost"]]
        refut = all(pr[c]["H1_simple"] and pr[c]["rects"]["ghost"]["AP"].get("n_AP") == 0 for c in C_BEFORE)
        dec["P"] = {"verdict": "confirmed" if conf else ("refuted" if refut else "undecided"),
                    "c_with_ghost_at_or_before": conf,
                    "first_c_with_ghost": next((c for c in C_LIST if pr.get(c, {}).get("ghost")), None),
                    "ghost_after_crossing": {c: pr.get(c, {}).get("ghost") for c in C_LIST if c not in C_BEFORE},
                    "ghost_location": {c: (pr[c].get("ghosts") or [{}])[0].get("x") for c in C_LIST if c in pr}}
    # S1
    s1_all, s1_bad = 0, []
    for uname, d in units.items():
        if uname.startswith(("float", "s2", "resolution")):
            continue
        for c, rec in d.items():
            if not rec.get("H1_simple"):
                continue
            if uname == "gap2_dh":  # gap2_unit records no S1 block; compare its counts here
                for rn, rr in rec["rects"].items():
                    ap = rr["AP"]
                    s1_all += 1
                    if not ap.get("closed"):
                        s1_bad.append(f"{uname}|{c}|{rn}")
                        continue
                    a, b = Fraction(ap["a"]), Fraction(ap["b"])
                    inside = sum(1 for z in rr["SC"]["zeros"] if Fraction(z["lo"]) >= a and Fraction(z["hi"]) <= b)
                    if inside != ap["n_AP"]:
                        s1_bad.append(f"{uname}|{c}|{rn}")
                continue
            for rn, s in rec.get("S1", {}).items():
                s1_all += 1
                if s.get("equal") is not True:
                    s1_bad.append(f"{uname}|{c}|{rn}")
    dec["S1"] = {"rectangles_checked": s1_all, "not_equal_or_not_closed": s1_bad, "holds": not s1_bad}
    # counts on the nominal rectangles, through R_ctx (added after the primary numbers,
    # RESULTS.md s1): the AP sides were moved inward in a few rectangles (PREREG s4)
    nom = {}
    for uname, d in units.items():
        if uname.startswith(("float", "s2", "resolution", "gap2")):
            continue
        for c, rec in d.items():
            row = {}
            for rn, rr in rec.get("rects", {}).items():
                if rn == "ctx":
                    continue
                row[rn] = {"nominal": nominal_count(rec, rn), "moved_sides_AP": rr["AP"].get("n_AP"),
                           "sides": [rr["AP"].get("a"), rr["AP"].get("b")], "nominal_x": rr["nominal"]}
            nom[f"{uname}|{c}"] = row
    dec["nominal_counts"] = {"by_unit": nom,
                             "all_read": all(v["nominal"] is not None for r in nom.values() for v in r.values()),
                             "agree_with_AP": all(v["nominal"] == v["moved_sides_AP"] for r in nom.values() for v in r.values())}
    # S3 zeta
    zt = units.get("primary_zeta", {})
    if zt:
        rows = {}
        for c, rec in zt.items():
            acc = rec["ctx_accounting"]
            offs = [abs(a["offset"]) for a in acc if a["offset"] is not None]
            rows[c] = {"n_AP_gap": rec["rects"]["gap"]["AP"].get("n_AP"), "ghost": rec["ghost"],
                       "n_ctx_zeros": len(acc), "n_zeta_zeros_in_ctx": len(rec["online_in_ctx"]),
                       "n_AP_ctx": rec["rects"]["ctx"]["AP"].get("n_AP"),
                       "max_offset": max(offs) if offs else None,
                       "all_within_0.01": bool(acc) and all(a["offset"] is not None and abs(a["offset"]) <= 0.01 for a in acc)}
            rows[c]["holds"] = (rows[c]["n_AP_gap"] == 0 and not rec["ghost"] and rows[c]["all_within_0.01"]
                                and rows[c]["n_ctx_zeros"] == rows[c]["n_zeta_zeros_in_ctx"] == rows[c]["n_AP_ctx"])
        dec["S3"] = {"by_c": rows, "holds": all(r["holds"] for r in rows.values())}
    # S4 epstein
    ep = units.get("primary_epstein", {})
    if ep:
        rows = {}
        for c, rec in ep.items():
            lam_neg = arb(rec["rq"]) < 0 if rec.get("rq") else None
            rows[c] = {"lam1_negative": bool(lam_neg), "ghost": rec["ghost"],
                       "ghost_x": (rec.get("ghost_nearest") or {}).get("x"), "H2_even": rec.get("H2_even")}
        dec["S4"] = {"by_c": rows, "holds": all(r["ghost"] for r in rows.values() if r["lam1_negative"])}
    # S5 dedekind
    de = units.get("primary_dedekind", {})
    if de:
        rows = {}
        for c, rec in de.items():
            acc = rec["ctx_accounting"]
            rows[c] = {"ghost": rec["ghost"], "unaccounted": [a["x"] for a in acc if a["accounted_by"] is None],
                       "n_ctx_zeros": len(acc), "n_online_in_ctx": len(rec["online_in_ctx"])}
            rows[c]["holds"] = (not rec["ghost"]) and not rows[c]["unaccounted"]
        dec["S5"] = {"by_c": rows, "holds": all(r["holds"] for r in rows.values())}
    # S6 lesion
    q1 = units.get("q1_dh", {})
    if q1 and pr:
        rows = {}
        for c, rec in q1.items():
            base = pr.get(c)
            if not base:
                continue
            bx = (base.get("ghost_nearest") or {}).get("x")
            lz = [w["x"] for w in rec["zeros_within_radius"]]
            near = rec.get("nearest_zero_to_ref", {}).get("x")
            moved = (bx is not None and near is not None and abs(near - bx) > 0.1)
            rows[c] = {"base_ghost_x": bx, "lesion_zeros_within_0.3": lz, "lesion_nearest_x": near,
                       "vanished": not lz, "moved_over_0.1": moved,
                       "holds": (bx is None) or (not lz) or moved}
        sh = units.get("sham_dh", {})
        for c, rec in sh.items():
            if c in rows:
                rows[c]["sham_zeros_within_0.3"] = [w["x"] for w in rec["zeros_within_radius"]]
                rows[c]["sham_nearest_x"] = rec.get("nearest_zero_to_ref", {}).get("x")
        dec["S6"] = {"by_c": rows, "holds": all(r["holds"] for r in rows.values())}
    # S7 precision response and float route
    s7 = {}
    for kind in KINDS:
        a = units.get(f"primary_{kind}", {})
        b = units.get(f"prec2_{kind}", {})
        f = units.get(f"float_{kind}", {})
        tol = 1e-40 if kind == "zeta" else 1e-20
        for c in a:
            row = {}
            if c in b:
                same, dmax = True, 0.0
                for rn in a[c]["rects"]:
                    za = a[c]["rects"][rn]["SC"]["zeros"]
                    zb = b[c]["rects"][rn]["SC"]["zeros"]
                    if len(za) != len(zb) or a[c]["rects"][rn]["AP"].get("n_AP") != b[c]["rects"][rn]["AP"].get("n_AP"):
                        same = False
                        continue
                    for u, v in zip(za, zb):
                        mid_u = (Fraction(u["lo"]) + Fraction(u["hi"])) / 2
                        mid_v = (Fraction(v["lo"]) + Fraction(v["hi"])) / 2
                        dmax = max(dmax, float(abs(mid_u - mid_v)))
                row["prec2_same_counts"] = same
                row["prec2_max_location_diff"] = dmax
                row["prec2_holds"] = same and dmax <= tol
            if c in f:
                same, dmax = True, 0.0
                for rn in a[c]["rects"]:
                    za = [z["x"] for z in a[c]["rects"][rn]["SC"]["zeros"]]
                    zf = f[c]["rects"][rn]["real_zeros"]
                    wf = f[c]["rects"][rn]["winding"]
                    if len(za) != len(zf) or not wf["integral"] or wf["n"] != a[c]["rects"][rn]["AP"].get("n_AP"):
                        same = False
                        continue
                    for u, v in zip(za, zf):
                        dmax = max(dmax, abs(u - v))
                row["float_same_counts"] = same
                row["float_max_location_diff"] = dmax
                la, lf = arb(a[c]["rq"]), arb(f[c]["lam1"])
                row["float_lam1_rel_diff"] = float((abs(lf - la) / abs(la)).mid())
                row["float_holds"] = same and dmax <= 1e-8
            s7[f"{kind}|{c}"] = row
    dec["S7"] = {"by_unit": s7,
                 "holds": all(r.get("prec2_holds", True) and r.get("float_holds", True) for r in s7.values()),
                 "complete": all("prec2_holds" in r and "float_holds" in r for r in s7.values())}
    s2 = units.get("s2_primary_dh", {})
    if s2:
        pre = {c: r for c, r in s2.items() if c in C_LIST}
        exp = {c: r for c, r in s2.items() if c not in C_LIST}
        dec["S2"] = {"by_c": pre, "holds": all(r.get("sign_rule_holds") for r in pre.values() if r.get("sign_rule_applies")),
                     "note": "preregistered windows C only"}
        dec["S2_exploratory_scan"] = {"by_c": exp, "holds": all(r.get("sign_rule_holds") for r in exp.values() if r.get("sign_rule_applies")),
                                      "violations": [c for c, r in exp.items() if r.get("sign_rule_applies") and not r.get("sign_rule_holds")]}
    tab["decisions"] = dec
    tab["meta"] = {"lane": "ghost-zeros (hunt weil_propagation)", "prereg": "PREREG.md", "N": N_BAND,
                   "windows_c": C_LIST, "at_or_before_crossing": C_BEFORE,
                   "precisions_bits": PRECS, "bisect_bits": BISECT_BITS,
                   "note": "band-128 even ground states; nothing here is a claim about RH"}
    W.save(TABLE, tab)
    return dec


# ---------------------------------------------------------------------------
# exploratory, chosen after the primary numbers (RESULTS.md says so): tracking
# of a function's own on-line zeros by the real zeros of F_v, against height
# ---------------------------------------------------------------------------


def resolution(kind: str, c, lo: float, hi: float, lesion: str | None = None) -> dict:
    """Real zeros of F_v on [lo, hi] (step 1/512, bisected to 2^-40) against the
    kind's own on-line zeros there: for each on-line zero, the distance to the
    nearest real zero of F_v. ``t_res`` is the height where the function's mean
    zero density, (1/2 pi) log(q t / 2 pi) for degree 1 and (1/pi) log(sqrt(q) t / 2 pi)
    for degree 2, equals L/(2 pi), the mean real-zero density of an entire function
    of type L/2; it is recorded for comparison only (the Q1 lesion shows that DH's
    band-128 F_v does follow DH's zeros above it)."""
    prec, prec_ldl = PRECS["primary"][kind]
    A, _, L = assemble(kind, c, prec)
    if lesion:
        A = A - lesion_matrix(lesion, L, A.nrows())
    A3 = A if prec_ldl == prec else assemble(kind, c, prec_ldl)[0]
    x, _, _, _ = ground_state(A, A3, prec, prec_ldl)
    T = Transform(x, L, prec, None)
    sc = sign_scan(T, lo, hi, 40)
    fz = [z["x"] for z in sc["zeros"]]
    if kind in ("epstein", "dedekind") and (lo < 12 or hi > 21):
        import cypari2

        pari = cypari2.Pari()
        pari.set_real_precision(38)
        Lf = pari("lfunqf([2,1;1,12])") if kind == "epstein" else pari("lfuncreate(x^2+x+6)")
        on = [float(z) for z in pari.lfunzeros(Lf, pari(f"[{lo},{hi}]"))]
    else:
        on = [y for y in online_zeros(kind) if lo < y < hi]
    rows = [{"online": y, "nearest_F_zero": min(fz, key=lambda f: abs(f - y)) if fz else None,
             "dist": min(abs(f - y) for f in fz) if fz else None} for y in on]
    q = {"dh": 5, "zeta": 1, "epstein": 23, "dedekind": 23}[kind]
    cf = float(Fraction(c))
    t_res = 2 * math.pi * cf / q if kind in ("dh", "zeta") else 2 * math.pi * math.sqrt(cf / q)
    return {"kind": kind, "c": ckey(c), "window": [lo, hi], "F_zeros": fz, "online": rows,
            "t_res": t_res, "note": "F_v of the band-128 even ground state; float distances; measured"}


#: DH's on-line gap around the second off-line ordinate gamma_2 (data/dh_zeros_online_T120.json)
DH_GAP2 = (112.37639423691519, 116.72151358725921)


def gap2_unit(c) -> dict:
    """Exploratory (RESULTS.md s9): the same counts in DH's second on-line gap,
    around gamma_2 = 114.1633427308 (delta_2 = 0.1508300806), with the same
    enclosure chain as ``unit`` (primary precision, eta from H1's shift)."""
    t0 = time.time()
    prec, _ = PRECS["primary"]["dh"]
    A, Aodd, L = assemble("dh", c, prec)
    x, lam2, method, inert0 = ground_state(A, A, prec, prec)
    hyp = hypotheses(A, Aodd, x, lam2, prec)
    T = Transform(x, L, prec, hyp.get("eta"))
    g2 = float(W.GAMMA_OFF2)
    r = float(GHOST_RADIUS)
    rects = {}
    for name, (lo, hi) in {"gap2": (DH_GAP2[0] + 0.001, DH_GAP2[1] - 0.001), "ghost2": (g2 - r, g2 + r)}.items():
        rects[name] = {"nominal": [lo, hi], "AP": count_rect(T, lo, hi, Fraction(1, 2)),
                       "SC": sign_scan(T, lo, hi, BISECT_BITS["dh"])}
    zs = rects["gap2"]["SC"]["zeros"]
    near = min(zs, key=lambda z: abs(z["x"] - g2)) if zs else None
    nx2 = W.dot(x, x)
    return {"c": ckey(c), "H1_simple": hyp["H1_simple"], "eta": hyp.get("eta"), "rq": hyp["rq"],
            "Q2": (W.offline_quadruple(x, L, W.GAMMA_OFF2, W.DELTA_OFF2) / nx2).str(10, radius=True),
            "rects": rects, "nearest_to_gamma2": ({"x": near["x"], "lo": near["lo"], "hi": near["hi"],
                                                    "dist": near["x"] - g2} if near else None),
            "elapsed_s": round(time.time() - t0, 1)}


# ---------------------------------------------------------------------------
# tables quoted verbatim by RESULTS.md (test_ghost.py regenerates and compares)
# ---------------------------------------------------------------------------


def _e(s: str, d: int = 4) -> str:
    """A ball string or float as a short decimal (midpoint, d significant digits)."""
    if s is None:
        return "n/a"
    v = arb(s) if isinstance(s, str) else arb(repr(s))
    return f"{float(v.mid()):.{d - 1}e}"


def _yn(b) -> str:
    return {True: "yes", False: "no", None: "undecided"}[b]


def _ghost_x(rec) -> str:
    g = rec.get("ghosts") or []
    return f"{g[0]['x']:.6f}" if g else "none"


def _ghost_d(rec) -> str:
    g = rec.get("ghosts") or []
    return f"{g[0]['dist']:+.4f}" if g else "n/a"


def tables(tab: dict | None = None) -> dict:
    tab = tab or load_json(TABLE, {})
    U = tab.get("units", {})
    out = {}
    pr = U.get("primary_dh", {})
    rows = ["| c | lambda_1 (ball RQ) | lambda_2 (est.) | H1 simple | H2 even | eta | Q1 | zeros in R_gap | ghost x | x - gamma_1 |",
            "|---|---|---|---|---|---|---|---|---|---|"]
    for c in C_LIST:
        r = pr.get(c)
        if not r:
            continue
        rows.append(f"| {c} | {_e(r['rq'])} | {_e(r['lam2_estimate'], 2)} | {_yn(r['H1_simple'])} | {_yn(r['H2_even'])} | "
                    f"{_e(r['eta'], 2)} | {_e(r['Q1'])} | {r['rects']['gap']['AP']['n_AP']} | {_ghost_x(r)} | {_ghost_d(r)} |")
    out["dh"] = "\n".join(rows)
    # controls
    rows = ["| kind | c | lambda_1 | H1 | H2 | n_AP(R_gap) | n_AP(R_ghost) | ghost | zeros in R_ctx | on-line zeros in R_ctx | accounted within 0.15 |",
            "|---|---|---|---|---|---|---|---|---|---|---|"]
    for kind in ("zeta", "epstein", "dedekind"):
        d = U.get(f"primary_{kind}", {})
        for c in C_LIST:
            r = d.get(c)
            if not r:
                continue
            gapn = r["rects"].get("gap", {}).get("AP", {}).get("n_AP", "n/a") if "gap" in r["rects"] else "n/a"
            acc = sum(1 for a in r["ctx_accounting"] if a["accounted_by"] is not None)
            rows.append(f"| {kind} | {c} | {_e(r['rq'])} | {_yn(r['H1_simple'])} | {_yn(r['H2_even'])} | {gapn} | "
                        f"{r['rects']['ghost']['AP']['n_AP']} | {_ghost_x(r)} | {len(r['ctx_accounting'])} | "
                        f"{len(r['online_in_ctx'])} | {acc} |")
    out["controls"] = "\n".join(rows)
    # lesion
    q1, sh = U.get("q1_dh", {}), U.get("sham_dh", {})
    rows = ["| c | unlesioned ghost x | Q1 lesion: lambda_1 | Q1 lesion: zeros within 0.3 of gamma_1 | Q1 lesion: nearest zero | sham lesion: ghost x |",
            "|---|---|---|---|---|---|"]
    for c in C_LIST:
        if c not in q1:
            continue
        r = q1[c]
        near = r.get("nearest_zero_to_ref", {}).get("x")
        rows.append(f"| {c} | {_ghost_x(pr.get(c, {}))} | {_e(r['rq'])} | {len(r['zeros_within_radius'])} | "
                    f"{near:.6f} | {_ghost_x(sh[c]) if c in sh else 'n/a'} |" if near is not None else
                    f"| {c} | {_ghost_x(pr.get(c, {}))} | {_e(r['rq'])} | {len(r['zeros_within_radius'])} | none | "
                    f"{_ghost_x(sh[c]) if c in sh else 'n/a'} |")
    out["lesion"] = "\n".join(rows)
    # scan below 29
    sc = {**U.get("scan_dh", {}), **U.get("scanfine_dh", {})}
    rows = ["| c | lambda_1 | H1 | zeros in R_gap | ghost x | x - gamma_1 | Q1 |", "|---|---|---|---|---|---|---|"]
    for c in sorted(sc, key=lambda k: Fraction(k)):
        r = sc[c]
        rows.append(f"| {c} | {_e(r['rq'])} | {_yn(r['H1_simple'])} | {r['rects']['gap']['AP']['n_AP']} | {_ghost_x(r)} | "
                    f"{_ghost_d(r)} | {_e(r['Q1'])} |")
    out["scan"] = "\n".join(rows)
    # basis-size response (exploratory)
    rows = ["| c | N | band edge | lambda_1 | H1 | zeros in R_gap | ghost x | x - gamma_1 |", "|---|---|---|---|---|---|---|---|"]
    for c in C_LIST:
        for n in (64, 128, 192, 256):
            r = pr.get(c) if n == N_BAND else U.get(f"N{n}_dh", {}).get(c)
            if not r:
                continue
            rows.append(f"| {c} | {n} | {r['band_edge']:.1f} | {_e(r['rq'])} | {_yn(r['H1_simple'])} | "
                        f"{r['rects']['gap']['AP']['n_AP']} | {_ghost_x(r)} | {_ghost_d(r)} |")
    out["basis"] = "\n".join(rows)
    # S2
    s2 = U.get("s2_primary_dh", {})
    rows = ["| c | window set | x_g | x_g - gamma_1 | Q1 | first-order value | ratio | sign rule applies | holds |",
            "|---|---|---|---|---|---|---|---|---|"]
    for c in sorted(s2, key=lambda k: Fraction(k)):
        r = s2[c]
        if r.get("x_g") is None:
            continue
        rows.append(f"| {c} | {'C' if c in C_LIST else 'scan'} | {r['x_g']:.6f} | {r['dist']:+.4f} | {_e(r['Q1'])} | "
                    f"{_e(r['Q1_first_order'])} | {r['ratio']:.3f} | {_yn(r['sign_rule_applies'])} | {_yn(r['sign_rule_holds'])} |")
    out["s2"] = "\n".join(rows)
    # precision and float route
    s7 = tab.get("decisions", {}).get("S7", {}).get("by_unit", {})
    rows = ["| kind | c | second precision: counts | its brackets | float route: counts | its locations (float64) | its lambda_1, relative difference |",
            "|---|---|---|---|---|---|---|"]

    def _same(b):
        return {True: "same", False: "differ", None: "not run"}[b]

    for key in sorted(s7, key=lambda k: (KINDS.index(k.split("|")[0]), C_LIST.index(k.split("|")[1]) if k.split("|")[1] in C_LIST else 99)):
        r = s7[key]
        kind, c = key.split("|")
        pd = r.get("prec2_max_location_diff")
        fd = r.get("float_max_location_diff")
        fl1 = r.get("float_lam1_rel_diff")
        rows.append(f"| {kind} | {c} | {_same(r.get('prec2_same_counts'))} | "
                    f"{'identical' if pd == 0 else ('n/a' if pd is None else f'{pd:.1e} apart')} | "
                    f"{_same(r.get('float_same_counts'))} | "
                    f"{'n/a' if fd is None else ('equal' if fd == 0 else f'{fd:.1e} apart')} | "
                    f"{'n/a' if fl1 is None else f'{fl1:.0e}'} |")
    out["s7"] = "\n".join(rows)
    return out


def results_numbers(tab: dict | None = None) -> dict:
    """The numbers RESULTS.md and the hunts/README.md line quote in prose, computed
    from the table (test_ghost.py checks each appears where quoted)."""
    tab = tab or load_json(TABLE, {})
    U = tab.get("units", {})
    pr = U.get("primary_dh", {})
    on = dh_online()
    g1 = float(GAMMA_1)
    out = {}
    gx = [pr[c]["ghosts"][0]["x"] for c in C_LIST if pr.get(c, {}).get("ghosts")]
    gd = [x - g1 for x in gx]
    if gx:
        out["GHOST_MIN"] = f"{min(gx):.4f}"
        out["GHOST_MAX"] = f"{max(gx):.4f}"
        out["DIST_MIN"] = f"{min(gd):.3f}"
        out["DIST_MAX"] = f"{max(gd):.3f}"

    def other_offsets(d):
        vals = []
        for c in C_LIST:
            r = d.get(c)
            if not r:
                continue
            ghosts = [g["x"] for g in r.get("ghosts", [])]
            for a in r["ctx_accounting"]:
                if a["x"] in ghosts:
                    continue
                vals.append(abs(a["x"] - min(on, key=lambda y: abs(y - a["x"]))))
        return vals

    po = other_offsets(pr)
    if po:
        out["OTHER_MIN"] = f"{min(po):.2f}"
        out["OTHER_MAX"] = f"{max(po):.2f}"
    q1 = U.get("q1_dh", {})
    lo = other_offsets(q1)
    if lo:
        out["LESION_OTHER_MAX"] = f"{max(lo):.2f}"
        out["LESION_OTHER_MAX_C30"] = f"{max(other_offsets({c: q1[c] for c in q1 if c != '29'})):.3f}"
    if "47" in q1:
        out["LESION_47"] = ", ".join(f"{a['x']:.4f}" for a in q1["47"]["ctx_accounting"])
    # the lesioned zero that approximates DH's on-line zero DH_GAP[0] = 83.10884...,
    # at the windows where it sits inside the nominal gap rectangle (left side 83.109)
    edge = [z["x"] - DH_GAP[0] for c in C_LIST if c in q1 for z in q1[c]["rects"]["ctx"]["SC"]["zeros"]
            if 83.109 <= z["x"] < DH_GAP[0] + 0.15]
    if edge:
        out["LESION_EDGE"] = f"{min(edge):.4f} to {max(edge):.3f}"
    # the largest inward move of an AP side in the primary DH rectangles (PREREG s4)
    sh_ = [max(r["rects"][n]["AP"]["a_float"] - r["rects"][n]["nominal"][0],
               r["rects"][n]["nominal"][1] - r["rects"][n]["AP"]["b_float"]) for r in pr.values() for n in r["rects"]]
    if sh_:
        out["SIDE_SHIFT_MAX"] = f"{max(sh_):.3f}"
    sh = U.get("sham_dh", {})
    sx = [sh[c]["ghosts"][0]["x"] for c in C_LIST if sh.get(c, {}).get("ghosts")]
    if sx:
        out["SHAM_MIN"] = f"{min(sx):.4f}"
        out["SHAM_MAX"] = f"{max(sx):.4f}"
    s2 = U.get("s2_primary_dh", {})
    rat = [s2[c]["ratio"] for c in C_LIST if c in s2 and s2[c].get("ratio") is not None]
    if rat:
        out["S2_RATIO_MIN"] = f"{min(rat):.3f}"
        out["S2_RATIO_MAX"] = f"{max(rat):.3f}"
    zt = U.get("primary_zeta", {})
    if zt:
        w = max(float(Fraction(z["hi"]) - Fraction(z["lo"])) for r in zt.values() for z in r["rects"]["ctx"]["SC"]["zeros"])
        out["ZETA_BRACKET"] = f"{w:.1e}"
    s1 = tab.get("decisions", {}).get("S1", {})
    if s1:
        out["S1_N"] = str(s1["rectangles_checked"])
    sc = {**U.get("scan_dh", {}), **U.get("scanfine_dh", {})}
    first = [c for c in sorted(sc, key=lambda k: Fraction(k)) if sc[c]["ghost"]]
    if first:
        out["SCAN_FIRST"] = first[0]
    bx = []
    for c in ("29", "31", "47"):
        xs = [U.get(f"N{n}_dh", {}).get(c, {}).get("ghosts", [{}])[0].get("x") for n in (64, 192, 256)]
        xs.append(pr.get(c, {}).get("ghosts", [{}])[0].get("x"))
        xs = [x for x in xs if x is not None]
        if len(xs) >= 2:
            bx.append(max(xs) - min(xs))
    if bx:
        out["BASIS_SPREAD"] = f"{max(bx):.1e}"
    ep = U.get("primary_epstein", {})
    ex = [ep[c]["ghosts"][0] for c in C_LIST if ep.get(c, {}).get("ghosts")]
    if ex:
        out["EP_MIN"] = f"{min(g['x'] for g in ex):.3f}"
        out["EP_MAX"] = f"{max(g['x'] for g in ex):.3f}"
        out["EP_DIST_MIN"] = f"{min(abs(g['dist']) for g in ex):.3f}"
        out["EP_DIST_MAX"] = f"{max(abs(g['dist']) for g in ex):.3f}"
    de = U.get("primary_dedekind", {})
    if de:
        acc = [sum(1 for a in de[c]["ctx_accounting"] if a["accounted_by"] is not None) for c in C_LIST if c in de]
        nz = [len(de[c]["ctx_accounting"]) for c in C_LIST if c in de]
        near = [min((abs(a["x"] - float(GAMMA_E)) for a in de[c]["ctx_accounting"]), default=None) for c in C_LIST if c in de]
        out["DED_ACC"] = f"{min(acc)} to {max(acc)}"
        out["DED_NZ"] = f"{min(nz)} to {max(nz)}"
        out["DED_NEAR_MIN"] = f"{min(near):.2f}"
    g2 = U.get("gap2_dh", {})
    if g2:
        ds = [abs(g2[c]["nearest_to_gamma2"]["dist"]) for c in C_LIST if c in g2 and g2[c].get("nearest_to_gamma2")]
        out["GAP2_MIN"] = f"{min(ds):.1e}"
        out["GAP2_MAX"] = f"{max(ds):.3f}"
    w = []
    for name in ("primary_zeta",):
        for r in U.get(name, {}).values():
            w += [float(Fraction(z["hi"]) - Fraction(z["lo"])) for rr in r["rects"].values() for z in rr["SC"]["zeros"]]
    if w:
        out["ZETA_WIDEST"] = f"{max(w):.1e}"
    we = [float(Fraction(z["hi"]) - Fraction(z["lo"])) for rr in ep.get("29", {}).get("rects", {}).values() for z in rr["SC"]["zeros"]]
    if we:
        out["EP29_WIDEST"] = f"{max(we):.1e}"
        out["EP29_ETA"] = _e(ep["29"]["eta"], 2)
    # exploratory scan: the single locked zero from c = 25 on (scan and preregistered windows)
    allg = {**sc, **pr}
    lock = [allg[c]["ghosts"][0] for c in allg if Fraction(c) >= 25 and allg[c].get("ghosts")]
    if lock:
        out["LOCK_MIN"] = f"{min(g['x'] for g in lock):.6f}"
        out["LOCK_MAX"] = f"{max(g['x'] for g in lock):.6f}"
        out["LOCK_DIST_MAX"] = f"{max(abs(g['dist']) for g in lock):.3f}"
    early = [allg[c]["ghosts"][0] for c in allg if Fraction(c) < 25 and allg[c].get("ghosts")]
    if early:
        out["EARLY_DIST_MAX"] = f"{max(abs(g['dist']) for g in early):.4f}"
    if "18" in sc:
        zz = [z["x"] for z in sc["18"]["rects"]["gap"]["SC"]["zeros"]]
        if len(zz) == 2:
            out["C18_SEP"] = f"{zz[1] - zz[0]:.2f}"
    # tracking diagnostic (resolution_all.json)
    res = U.get("resolution_all", {})

    def dists(key, lo=-1.0, hi=1e9):
        r = res.get(key)
        return [o["dist"] for o in r["online"] if lo < o["online"] < hi and o["dist"] is not None] if r else []

    if res.get("dh|30|3|120"):
        tr = res["dh|30|3|120"]["t_res"]
        out["TRES_DH"] = f"{tr:.1f}"
        out["TRACK_DH_LOW"] = f"{max(dists('dh|30|3|120', hi=tr)):.0e}"
        out["TRACK_DH_40"] = f"{dists('dh|30|3|120', lo=40)[0]:.0e}"
        hiv = dists("dh|30|3|120", lo=68)
        out["TRACK_DH_HIGH"] = f"{min(hiv):.2g} to {max(hiv):.2g}"
        out["TRACK_DH_8765"] = f"{dists('dh|30|3|120', lo=87.6, hi=87.7)[0]:.2g}"
    if res.get("dh|30|3|120|q1"):
        out["TRACK_Q1_8765"] = f"{dists('dh|30|3|120|q1', lo=87.6, hi=87.7)[0]:.0e}"
    if res.get("dh|30|3|120|q12"):
        mid = dists("dh|30|3|120|q12", lo=92, hi=110)
        out["TRACK_Q12_MID"] = f"{min(mid):.1f} to {max(mid):.1f}"
    if res.get("zeta|30|10|120"):
        out["TRES_ZETA"] = f"{res['zeta|30|10|120']['t_res']:.1f}"
        out["TRACK_ZETA_MAX"] = f"{max(dists('zeta|30|10|120')):.0e}"
        out["TRACK_ZETA_N"] = str(len(res["zeta|30|10|120"]["online"]))
    for kind in ("dedekind", "epstein"):
        r = res.get(f"{kind}|30|1|21")
        if r:
            tr = r["t_res"]
            K = kind[:3].upper()
            out[f"TRES_{K}"] = f"{tr:.1f}"
            out[f"TRACK_{K}_LOW"] = f"{max(dists(f'{kind}|30|1|21', hi=tr)):.0e}"
            up = dists(f"{kind}|30|1|21", lo=12)
            out[f"TRACK_{K}_HIGH"] = f"{min(up):.2g} to {max(up):.2g}"
    return out


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def arb_cmd(kind: str, cs, variant: str):
    path = _unit_path(variant, kind)
    d = load_json(path, {})
    for c in cs:
        k = ckey(c)
        if k in d:
            continue
        rec = unit(kind, c, variant)
        d[k] = rec
        W.save(path, d)
        rg = rec["rects"]["ghost"]
        print(f"{variant} {kind} c={k}: H1={rec['H1_simple']} H2={rec.get('H2_even')} eta={rec.get('eta')} "
              f"ghost={rec['ghost']} n_AP(ghost)={rg['AP'].get('n_AP')} n_SC(ghost)={rg['SC']['n_SC']} "
              f"[{rec['elapsed_s']} s]", flush=True)


def float_cmd(kind: str, cs):
    path = _unit_path("float", kind)
    d = load_json(path, {})
    for c in cs:
        k = ckey(c)
        if k in d:
            continue
        rec = float_route(kind, c)
        d[k] = rec
        W.save(path, d)
        g = rec["rects"]["ghost"]
        print(f"float {kind} c={k}: lam1={rec['lam1']} n_neg_mid={rec['n_neg_at_midshift']} "
              f"ghost real={g['n_real']} winding={g['winding']['n']} [{rec['elapsed_s']} s]", flush=True)


def main(argv):
    if not argv:
        print(__doc__)
        return
    cmd = argv[0]
    rest = [a for a in argv[1:] if not a.startswith("--")]
    variant = "primary"
    for a in argv[1:]:
        if a.startswith("--variant="):
            variant = a.split("=", 1)[1]
    if cmd == "windows":
        windows_cmd()
    elif cmd == "arb":
        arb_cmd(rest[0], rest[1:] or (C_SCAN if variant == "scan" else C_LIST), variant)
    elif cmd == "float":
        float_cmd(rest[0], rest[1:] or C_LIST)
    elif cmd == "s2":
        out = load_json(_unit_path(f"s2_{variant}", "dh"), {})
        for c in rest or C_LIST:
            out[ckey(c)] = s2_check(c, variant)
            print(ckey(c), out[ckey(c)], flush=True)
            W.save(_unit_path(f"s2_{variant}", "dh"), out)
    elif cmd == "summary":
        print(json.dumps(summarize(), indent=1)[:6000])
    elif cmd == "tables":
        for name, t in tables().items():
            print(f"[{name}]\n{t}\n")
    elif cmd == "gap2":
        path = _unit_path("gap2", "dh")
        out = load_json(path, {})
        for c in rest or C_LIST:
            if ckey(c) in out:
                continue
            out[ckey(c)] = gap2_unit(c)
            W.save(path, out)
            r = out[ckey(c)]
            print(f"gap2 dh c={ckey(c)}: H1={r['H1_simple']} n_AP(gap2)={r['rects']['gap2']['AP'].get('n_AP')} "
                  f"n_SC(gap2)={r['rects']['gap2']['SC']['n_SC']} n_AP(ghost2)={r['rects']['ghost2']['AP'].get('n_AP')} "
                  f"nearest={r['nearest_to_gamma2']} [{r['elapsed_s']} s]", flush=True)
    elif cmd == "resolution":
        path = _unit_path("resolution", "all")
        out = load_json(path, {})
        for spec in rest:  # KIND:c:lo:hi[:lesion]
            parts = spec.split(":")
            kind, c, lo, hi = parts[:4]
            les = parts[4] if len(parts) > 4 else None
            key = f"{kind}|{ckey(c)}|{lo}|{hi}" + (f"|{les}" if les else "")
            if key in out:
                continue
            out[key] = resolution(kind, c, float(lo), float(hi), les)
            W.save(path, out)
            r = out[key]
            print(key, "t_res=%.1f" % r["t_res"], [(round(o["online"], 3), round(o["dist"], 3) if o["dist"] is not None else None) for o in r["online"]], flush=True)
    else:
        raise SystemExit(f"unknown command {cmd}")


if __name__ == "__main__":
    main(sys.argv[1:])
