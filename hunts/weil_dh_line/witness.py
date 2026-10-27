"""The full DH Weil form on the scout's Legendre basis, in position space
(hunt weil_dh_line, #146).

The stage-A block R(T#) of scout.py is a lower bound, in the Loewner order, for
the N-mode Davenport-Heilbronn form Q_N, and it increases to Q_N as T# grows
(given the envelope bound S and the archimedean bound used for t > T#). So the
stage-A pipeline refuses DH at every T# exactly when Q_N has a negative
eigenvalue, and one vector v with Q_N(v) < 0 shows it for every T# at once.
This module assembles Q_N itself, with no T# split, through the explicit
formula in position space, in Arb ball arithmetic.

For even real f supported in [-L, L], g = f * f~ (so g(x) = int f(y) f(y - x) dy,
g even, g = 0 for |x| >= 2L, and the Fourier transform of g is F(t)^2):

    Q(f) = (1/pi) int_0^inf Psi(t) F(t)^2 dt,
    Psi(t) = Re digamma(3/4 + it/2) + log(5/pi) - sum_n c_n cos(t log n),

with c_n = 2 Lambda_f(n)/sqrt(n) for log n < 2L (price.dh_comb, the comb the
scout uses). Gauss's integral for digamma turns the archimedean part into

    (1/(2 pi)) int g^(t) Re digamma(3/4 + it/2) dt
        = digamma(3/4) g(0) + int_0^inf w(x) (g(0) - g(x)) dx,
    w(x) = 2 e^{-3x/2} / (1 - e^{-2x}) = e^{-x/2} / sinh x,

so

    Q(f) = (log(5/pi) + digamma(3/4) + W_tail) g(0)
           + int_0^{2L} w(x) (g(0) - g(x)) dx - sum_n c_n g(log n),
    W_tail = int_{2L}^inf w = sum_{j >= 0} 2 e^{-(3/2 + 2j) 2L} / (3/2 + 2j).

Exact pieces. On [0, 2L], g is a polynomial of degree at most 2D + 1 (D the
degree of f), and g(x) = int_{x-L}^{L} f(y) f(y - x) dy is a Gauss-Legendre sum
with M = D + 1 nodes, exact. The comb needs g at the 22 points log n only (the nonzero DH comb terms).

The one truncation. int_0^{2L} w(x)(g(0) - g(x)) dx = int q(x) r(x) dx with
q = (g(0) - g)/x a polynomial of degree at most 2D and r = x w(x) analytic in a
Bernstein ellipse of [0, 2L] that avoids +-i pi. Gauss-Legendre with Nx nodes
then errs by at most 4L sup|q| ||r - r_m||, m = 2 Nx - 1 - 2D, and
||r - r_m|| <= 2 M_rho rho^{-m} / (rho - 1) (Chebyshev truncation), M_rho the
maximum of |r| on the ellipse, which `ellipse_bound` encloses in Arb on a
covering of the boundary. sup|q| <= sup|g'| <= ||f||_inf^2 + ||f||_2 ||f'||_2,
bounded for unit coefficient vectors in `quad_error_bound`.

Work basis. The Gram matrices are built in psi_k(y) = T_{2k}(y/L) (Chebyshev),
whose values cos(2k arccos u) come from a two-level table of direct sin_cos
values, so every entry carries at most one rotation and its Arb radius stays
near the working precision (a three-term recurrence or repeated complex
multiplication in ball arithmetic inflates radii by up to (1 + sqrt 2) or
sqrt 2 per step). The scout's basis is phi_i = T_{2i} = sqrt((2(2i)+1)/(2L))
P_{2i}(y/L) with P_{2i} = a_i^2 + 2 sum_k a_{i-k} a_{i+k} T_{2k}, a_j =
binom(2j, j)/4^j (exact rationals), so Q_phi = K Q_psi K^T.

Matrix products are taken on exact midpoints (Arb rounds the product
rigorously); the dropped entry radii are carried as one scalar per node,
2 r sum_j B_j + M r^2 per entry (r the largest radius, B_j bounds row j),
added back at the end. The final statement is: Q_N lies in the computed ball
matrix plus [-eps, eps] I in the Loewner order, eps from the quadrature bound,
the dropped-radius bound and the dropped comb mass of price.dh_comb.
"""
from __future__ import annotations

import json
import math
import os
import pickle
import sys
import time
from fractions import Fraction
from math import comb as binom
from pathlib import Path

from flint import acb, arb, arb_mat, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import price  # noqa: E402

PREC = 256
L_DH_WINDOW = Fraction(171079, 100000)
_TABLE_B = 32


# ------------------------------------------------------------------ basis

def a_coef(j: int) -> Fraction:
    return Fraction(binom(2 * j, j), 4 ** j)


def a_coefs(n: int) -> list[Fraction]:
    """a_0..a_{n-1} by the exact recurrence a_j = a_{j-1} (2j - 1)/(2j)."""
    out = [Fraction(1)]
    for j in range(1, n):
        out.append(out[-1] * Fraction(2 * j - 1, 2 * j))
    return out


def cheb_coeffs_even_legendre(i: int) -> list[Fraction]:
    """P_{2i}(u) = sum_k e_k T_{2k}(u), exact: e_0 = a_i^2, e_k = 2 a_{i-k} a_{i+k}."""
    return [a_coef(i) ** 2] + [2 * a_coef(i - k) * a_coef(i + k) for k in range(1, i + 1)]


def K_matrix(L: Fraction, N: int) -> arb_mat:
    """phi_i = sum_k K[i, k] psi_k (lower triangular), phi_i = sqrt((4i+1)/(2L)) P_{2i}(y/L),
    K[i, k] = sqrt((4i+1)/(2L)) e_k(i) with the exact e_k of cheb_coeffs_even_legendre,
    from the a_j converted once to balls (the products then carry Arb's rounding)."""
    La = price.to_arb(L)
    aa = [price.to_arb(x) for x in a_coefs(2 * N)]
    K = arb_mat(N, N)
    for i in range(N):
        sc = ((arb(4 * i + 1) / 2) / La).sqrt()
        K[i, 0] = sc * aa[i] * aa[i]
        for k in range(1, i + 1):
            K[i, k] = sc * (2 * aa[i - k] * aa[i + k])
    return K


def gl_sym(M: int):
    """Gauss-Legendre nodes and weights on [-1, 1], mirrored so that the node
    list is exactly symmetric (node M-1-j is the negation of node j)."""
    half = [arb.legendre_p_root(M, k, weight=True) for k in range((M + 1) // 2)]
    if M % 2:
        mid = half[-1]
        half = half[:-1]
        return half + [(arb(0), mid[1])] + [(-x, w) for x, w in reversed(half)]
    return half + [(-x, w) for x, w in reversed(half)]


# ------------------------------------------------------------------ one node

def node_gram(s: arb, nodes, N: int, La: arb):
    """G(x)_{kl} = int psi_k(y) psi_l(y - x) dy at x = s L, exactly: the Gauss
    sum with M >= 2N - 1 mirrored nodes on [s - 1, 1] (in u = y/L).

    Row j of V is V[j, k] = sqrt(L (1 - s/2) W_j) cos(2k arccos u_j), u_j =
    s/2 + (1 - s/2) xi_j, built from a two-level table of direct sin_cos values
    (k = 32a + b, one rotation per entry, as a rank-2 product T = R2 R1).
    Since psi_l is even, psi_l(u_j - s) is psi_l at the mirrored node, so
    G = V^T J V (J reverses rows), and pairing node j with its mirror gives
    G = X^T Y + (X^T Y)^T (+ the middle row's outer product): one product of
    half length. Products use exact midpoints; returned with eps, the bound on
    what the dropped radii can change in any entry: 2 r sum_j B_j + M r^2, r
    the largest entry radius read off the balls, B_j = sqrt(L (1 - s/2) W_j)."""
    B = _TABLE_B
    A = (N + B - 1) // B
    M = len(nodes)
    h = M // 2
    half_s = s / 2
    rows = []
    rmax = 0.0
    sumB = arb(0)
    for xi, w in nodes:
        u = half_s + (1 - half_s) * xi
        phi = 2 * u.acos()
        sq = (La * (1 - half_s) * w).sqrt()
        cs1 = [(b * phi).sin_cos() for b in range(B)]
        cs2 = [(B * a * phi).sin_cos() for a in range(A)]
        R1 = arb_mat(2, B, [c for _, c in cs1] + [sn for sn, _ in cs1])
        R2 = arb_mat(A, 2, [x for sn, c in cs2 for x in (c * sq, -(sn * sq))])
        e = (R2 * R1).entries()[:N]
        rows.append(e)
        rmax = max(rmax, max(float(x.rad()) for x in e))
        sumB += arb(sq.upper())
    X = arb_mat(h, N, [x for j in range(h) for x in rows[j]]).mid()
    Y = arb_mat(h, N, [x for j in range(h) for x in rows[M - 1 - j]]).mid()
    P = X.transpose() * Y
    G = P + P.transpose()
    if M % 2:
        vm = arb_mat(1, N, rows[h]).mid()
        G = G + vm.transpose() * vm
    r = arb(rmax) * (1 + arb(2) ** -40)
    eps = 2 * r * sumB + M * r * r
    return G, float(eps.upper()) * (1 + 2.0 ** -40)


# ------------------------------------------------------------------ the pieces

def w_kernel(x: arb, a: Fraction = Fraction(3, 4)) -> arb:
    """w_a(x) = 2 e^{-2 a x} / (1 - e^{-2x}); a = 3/4 is DH (Gamma((s+1)/2)),
    e^{-x/2}/sinh x. a = 1/4 (zeta's Gamma(s/2)) is used only as a planted fault."""
    aa = price.to_arb(a)
    return 2 * (-2 * aa * x).exp() / (1 - (-2 * x).exp())


def kappa0(a: Fraction = Fraction(3, 4), conductor: int = 5) -> arb:
    """log(q/pi) + digamma(a): log(5/pi) + digamma(3/4) for DH."""
    return (arb(conductor) / arb.pi()).log() + acb(price.to_arb(a)).digamma().real


def w_tail(L: Fraction, a: Fraction = Fraction(3, 4), J: int = 60) -> arb:
    """int_{2L}^inf w_a = sum_j 2 e^{-(2a+2j) 2L}/(2a+2j), truncated at J with
    the geometric remainder added as a radius."""
    twoL = 2 * price.to_arb(L)
    aa = price.to_arb(a)
    tot = arb(0)
    for j in range(J):
        mu = 2 * aa + 2 * j
        tot += 2 * (-mu * twoL).exp() / mu
    mu = 2 * aa + 2 * J
    rem = 2 * (-mu * twoL).exp() / mu / (1 - (-2 * twoL).exp())
    return tot + arb(0, rem.upper())


def comb(L: Fraction):
    """[(n, c_n)] and the dropped l1 mass: the scout's DH comb (price.dh_comb)."""
    out, dropped = price.dh_comb(L, with_dropped=True)
    with ctx.workprec(ctx.prec):
        return [(n, +c) for n, c in out], float(arb(dropped.upper()).upper())


def x_nodes(L: Fraction, Nx: int):
    """Gauss-Legendre on [0, 2L]: [(s = x/L, omega)]."""
    out = []
    for xi, w in gl_sym(Nx):
        out.append((1 + xi, price.to_arb(L) * w))   # x = L (1 + xi), dx = L dxi
    return out


def plan_points(L: Fraction, N: int, Nx: int, a: Fraction = Fraction(3, 4)):
    """Every node at which a Gram matrix is needed: ('g0', s=0), the arch
    nodes ('arch', s, coefficient omega w(x)) and the comb ('comb', s, c_n)."""
    La = price.to_arb(L)
    pts = [("g0", arb(0), arb(1))]
    for s, om in x_nodes(L, Nx):
        pts.append(("arch", s, om * w_kernel(s * La, a)))
    cmb, _ = comb(L)
    for n, c in cmb:
        pts.append(("comb", arb(n).log() / La, c))
    return pts


def unit(L: Fraction, N: int, Nx: int, i0: int, i1: int, prec: int = PREC,
         a: Fraction = Fraction(3, 4)):
    """Partial sums over points i0..i1-1 of plan_points: G0 (if present), the
    arch sum A = sum omega w G(x), the scalar a = sum omega w, the comb sum
    P = sum c_n G(log n), and the dropped-radius bound E (sum |coef| eps)."""
    ctx.prec = prec
    La = price.to_arb(L)
    M = 2 * N - 1
    nodes = gl_sym(M)
    pts = plan_points(L, N, Nx, a)
    out = {"G0": None, "A": arb_mat(N, N), "a": arb(0), "P": arb_mat(N, N), "E": 0.0, "eps0": 0.0}
    for kind, s, coef in pts[i0:i1]:
        G, eps = node_gram(s, nodes, N, La)
        if kind == "g0":
            out["G0"] = G
            out["eps0"] = eps
        elif kind == "arch":
            out["A"] += coef * G
            out["a"] += coef
            out["E"] += float(abs(coef).upper()) * eps
        else:
            out["P"] += coef * G
            out["E"] += float(abs(coef).upper()) * eps
    return out


# ------------------------------------------------------------------ error bounds

def ellipse_bound(L: Fraction, rho: arb, pieces: int = 4096) -> arb:
    """Upper bound of |r(z)| = |z e^{-z/2}/sinh z| on the Bernstein ellipse of
    [0, 2L] with parameter rho, from Arb evaluation on boxes covering the
    boundary (max modulus). Raises if a box meets a zero of sinh."""
    La = price.to_arb(L)
    best = arb(0)
    two_pi = 2 * arb.pi()
    for k in range(pieces):
        th = (arb(k) + arb(0.5)) / pieces * two_pi
        th = arb(th.mid(), (two_pi / pieces / 2).upper())
        e = acb(th.cos(), th.sin())
        z = La + La * (rho * e + e.conjugate() / rho) / 2
        sh = z.sinh()
        if sh.contains(0):
            raise RuntimeError("box meets a zero of sinh")
        v = abs(z * (-z / 2).exp() / sh)
        best = max(best, arb(v.upper()))
    return best


def quad_error_bound(L: Fraction, N: int, Nx: int, rho: Fraction = Fraction(7, 2)) -> float:
    """Bound on |v^T (Q_exact - Q_GL) v| for unit coefficient vectors v in the
    phi basis (scout normalization), from the Gauss-Legendre error in x."""
    La = price.to_arb(L)
    D = 2 * N - 2
    m = 2 * Nx - 1 - 2 * D
    if m < 1:
        raise ValueError("Nx too small for the degree")
    rh = price.to_arb(rho)
    # rho must keep +-i pi outside the ellipse
    a = La * (rh + 1 / rh) / 2
    b = La * (rh - 1 / rh) / 2
    if not bool((La / a) ** 2 + (arb.pi() / b) ** 2 > 1):
        raise ValueError("ellipse reaches i pi")
    Mr = ellipse_bound(L, rh)
    cheb = 2 * Mr * rh ** (-m) / (rh - 1)
    # sup|f|^2 <= sum_i (4i+1)/(2L); ||f'||_2^2 <= sum_i (4i+1)/(2L^2) 2i(2i+1)
    sinf2 = sum((arb(4 * i + 1) / (2 * La) for i in range(N)), arb(0))
    dfl2 = sum((arb(4 * i + 1) / (2 * La * La) * (2 * i) * (2 * i + 1) for i in range(N)), arb(0))
    supq = sinf2 + dfl2.sqrt()
    return float((4 * La * supq * cheb).upper())


# ------------------------------------------------------------------ assembly

def reduce_parts(L: Fraction, N: int, parts, prec: int = PREC, a: Fraction = Fraction(3, 4),
                 conductor: int = 5, comb_scale: int | Fraction = 1):
    """Q_psi from unit outputs, then Q_phi = K Q_psi K^T, and the scalar
    entrywise bound E_psi (dropped radii) and the comb-mass and quadrature
    terms are returned separately."""
    ctx.prec = prec
    G0 = None
    A = arb_mat(N, N)
    P = arb_mat(N, N)
    asum = arb(0)
    E = 0.0
    eps0 = 0.0
    for p in parts:
        if p["G0"] is not None:
            G0 = p["G0"]
            eps0 = p["eps0"]
        A += p["A"]
        P += p["P"]
        asum += p["a"]
        E += p["E"]
    if G0 is None:
        raise ValueError("no G0 part")
    kap = kappa0(a, conductor) + w_tail(L, a)
    Qpsi = (kap + asum) * G0 - A - price.to_arb(Fraction(comb_scale)) * P
    E += float(abs(kap + asum).upper()) * eps0
    K = K_matrix(L, N)
    Q = K * Qpsi * K.transpose()
    I_chk = K * G0 * K.transpose()
    return {"Q": Q, "Qpsi": Qpsi, "G0": G0, "E_psi": E, "K": K, "I_check": I_chk}


def spectral_eps(L: Fraction, N: int, Nx: int, E_psi: float, K: arb_mat, dropped_l1: float) -> float:
    """eps with Q_exact in Q_computed + [-eps, eps] I: quadrature, dropped
    radii (entrywise E_psi in the psi basis; ||K E K^T||_2 <= N E ||K||_F^2) and
    dropped comb mass (|g| <= ||f||^2)."""
    kf2 = sum((K[i, j] ** 2 for i in range(N) for j in range(i + 1)), arb(0))
    e_mid = float((N * arb(E_psi) * kf2).upper())
    return quad_error_bound(L, N, Nx) + e_mid + dropped_l1


def default_Nx(N: int, margin: int = 90) -> int:
    return 2 * N - 1 + margin


# ------------------------------------------------------------------ vectors

def quad_form(Q: arb_mat, v) -> arb:
    """v^T Q v / v^T v in ball arithmetic, v exact (list of arb)."""
    n = Q.nrows()
    x = arb_mat(n, 1, list(v))
    Qx = Q * x
    num = sum((x[i, 0] * Qx[i, 0] for i in range(n)), arb(0))
    den = sum((x[i, 0] ** 2 for i in range(n)), arb(0))
    return num / den


def legendre_coeffs_of(f_vals_at, L: Fraction, N: int, prec: int = PREC):
    """Coefficients <f, phi_i> of an even polynomial f of degree <= 2N - 2
    given as a callable on arb y, exactly (Gauss with 2N nodes)."""
    ctx.prec = prec
    La = price.to_arb(L)
    nodes = gl_sym(2 * N)
    K = K_matrix(L, N)
    # psi_k(y) at nodes: cos(2k acos u)
    out = [arb(0)] * N
    for xi, w in nodes:
        y = La * xi
        fy = f_vals_at(y)
        phi = 2 * xi.acos()
        for k in range(N):
            out[k] += La * w * fy * (k * phi).cos()
    # <f, phi_i> = sum_k K[i,k] <f, psi_k>
    return [sum((K[i, k] * out[k] for k in range(i + 1)), arb(0)) for i in range(N)]


# ------------------------------------------------------------------ the driver
#
# Units of consecutive points run on a spawn pool; the parent adds each unit's
# partial sums to running sums and saves them (with the list of finished units)
# atomically after every unit, so a restart redoes only the units in flight.

def enc_mat(M: arb_mat, sym: bool = True):
    out = []
    for i in range(M.nrows()):
        for j in range(i + 1 if sym else M.ncols()):
            m, e = M[i, j].mid().man_exp()
            out.append((int(m), int(e), float(M[i, j].rad())))
    return out


def dec_mat(rows, N: int, sym: bool = True) -> arb_mat:
    M = arb_mat(N, N)
    it = iter(rows)
    for i in range(N):
        for j in range(i + 1 if sym else N):
            m, e, r = next(it)
            v = arb(m) * arb(2) ** e if m else arb(0)
            if r:
                v = v + arb(0, r * (1 + 2.0 ** -40))
            M[i, j] = v
            if sym:
                M[j, i] = v
    return M


def _job(args):
    L, N, Nx, i0, i1, prec = args
    t0 = time.time()
    u = unit(L, N, Nx, i0, i1, prec)
    return (i0, i1, None if u["G0"] is None else enc_mat(u["G0"]), enc_mat(u["A"]), enc_mat(u["P"]),
            (u["a"].mid().man_exp(), float(u["a"].rad())), u["E"], u["eps0"], time.time() - t0)


def _atomic(path: Path, data: bytes):
    tmp = path.with_name(path.name + ".tmp")
    with open(tmp, "wb") as fh:
        fh.write(data)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def assemble(L: Fraction, N: int, Nx: int, state_dir: Path, procs: int = 8, unit_points: int = 24,
             prec: int = PREC, stop_after: int | None = None):
    """All units, streamed into running sums under state_dir (resumable).
    Returns the reduce_parts dict when every unit is done, else None."""
    import multiprocessing as mpc
    ctx.prec = prec
    state_dir = Path(state_dir)
    state_dir.mkdir(parents=True, exist_ok=True)
    npts = len(plan_points(L, N, Nx))
    units = [(i, min(i + unit_points, npts)) for i in range(0, npts, unit_points)]
    params = {"L": f"{L.numerator}/{L.denominator}", "N": N, "Nx": Nx, "prec": prec, "units": units}
    sp = state_dir / "state.pkl"
    if sp.exists():
        st = pickle.loads(sp.read_bytes())
        if st["params"] != params:
            raise SystemExit("state made with other parameters")
        A, P = dec_mat(st["A"], N), dec_mat(st["P"], N)
        G0 = dec_mat(st["G0"], N) if st["G0"] is not None else None
        (am, ae), ar = st["a"]
        asum = arb(am) * arb(2) ** ae + arb(0, ar) if am else arb(0, ar)
    else:
        st = {"params": params, "done": [], "E": 0.0, "eps0": 0.0, "seconds": [], "G0": None}
        A, P, G0, asum = arb_mat(N, N), arb_mat(N, N), None, arb(0)
    todo = [u for u in units if list(u) not in [list(d) for d in st["done"]]]
    jobs = [(L, N, Nx, i0, i1, prec) for i0, i1 in todo]
    pool = mpc.get_context("spawn").Pool(procs) if procs > 1 else None
    n = 0
    try:
        it = pool.imap_unordered(_job, jobs, chunksize=1) if pool else map(_job, jobs)
        for i0, i1, g0, Ae, Pe, (amx, ar), E, eps0, sec in it:
            A += dec_mat(Ae, N)
            P += dec_mat(Pe, N)
            am, ae = amx
            asum += (arb(am) * arb(2) ** ae if am else arb(0)) + arb(0, ar * (1 + 2.0 ** -40))
            if g0 is not None:
                st["G0"] = g0
                G0 = dec_mat(g0, N)
                st["eps0"] = eps0
            st["E"] += E
            st["done"].append([i0, i1])
            st["seconds"].append(sec)
            st["A"], st["P"] = enc_mat(A), enc_mat(P)
            st["a"] = (asum.mid().man_exp(), float(asum.rad()))
            _atomic(sp, pickle.dumps(st, protocol=5))
            n += 1
            print(json.dumps({"unit": [i0, i1], "seconds": round(sec, 1), "done": len(st["done"]),
                              "of": len(units), "mem_available_gib": round(_mem_gib(), 1)}), flush=True)
            if stop_after is not None and n >= stop_after:
                break
    finally:
        if pool:
            pool.terminate()
            pool.join()
    if len(st["done"]) < len(units):
        return None
    part = {"G0": G0, "A": A, "P": P, "a": asum, "E": st["E"], "eps0": st["eps0"]}
    red = reduce_parts(L, N, [part], prec)
    red["unit_seconds"] = st["seconds"]
    return red



# ------------------------------------------------------------------ spectral analysis of Q_N

def ldl_inertia(A: arb_mat, balls: bool = True):
    """LDL^T without pivoting. balls=True: in ball arithmetic, so when no pivot
    ball contains 0 the counts hold for every symmetric matrix in the ball
    matrix A (Sylvester's law of inertia). balls=False: on midpoints
    (measured). Returns (n_neg, n_pos, n_undecided, min |pivot| midpoint)."""
    n = A.nrows()
    a = [[(A[i, j] if balls else A[i, j].mid()) for j in range(i + 1)] for i in range(n)]
    piv = []
    neg = pos = und = 0
    small = None
    for k in range(n):
        ak = a[k]
        d = ak[k]
        for m in range(k):
            d -= ak[m] * ak[m] * piv[m]
        if not balls:
            d = d.mid()
        piv.append(d)
        if bool(d < 0):
            neg += 1
        elif bool(d > 0):
            pos += 1
        else:
            und += 1
        ad = abs(d.mid())
        small = ad if small is None or bool(ad < small) else small
        if d.contains(0):
            return neg, pos, und + (n - k - 1), float(small)
        dinv = 1 / d
        lk = [ak[m] * piv[m] for m in range(k)]
        for i in range(k + 1, n):
            ai = a[i]
            sv = ai[k]
            for m in range(k):
                sv -= ai[m] * lk[m]
            ai[k] = sv * dinv if balls else (sv * dinv).mid()
    return neg, pos, und, float(small)


def inverse_iteration(Am: arb_mat, shift: arb | None = None, x0=None, iters: int = 12, deflate=()):
    """Eigenvalue of the midpoint matrix Am nearest the shift and its unit
    eigenvector (midpoints), with the residual ||A x - lam x||. Measured."""
    n = Am.nrows()
    A = Am if shift is None else Am - shift * arb_mat(n, n, [1 if i == j else 0 for i in range(n) for j in range(n)])
    x = arb_mat(n, 1, list(x0) if x0 is not None else [arb(1) / (1 + i) for i in range(n)])
    for _ in range(iters):
        for d in deflate:
            c = sum((d[i] * x[i, 0] for i in range(n)), arb(0))
            x = arb_mat(n, 1, [x[i, 0] - c * d[i] for i in range(n)])
        y = A.solve(x, algorithm="approx")
        nrm = sum((y[i, 0] ** 2 for i in range(n)), arb(0)).sqrt()
        x = arb_mat(n, 1, [(y[i, 0] / nrm).mid() for i in range(n)])
    Ax = Am * x
    lam = sum((x[i, 0] * Ax[i, 0] for i in range(n)), arb(0))
    res = sum(((Ax[i, 0] - lam * x[i, 0]) ** 2 for i in range(n)), arb(0)).sqrt()
    return lam.mid(), [x[i, 0] for i in range(n)], float(res.upper())


def lowest_eigenpair(Am: arb_mat, x0=None, sigma0: float = -1e-30):
    """The negative eigenvalue of a midpoint matrix with exactly one negative
    eigenvalue, and its eigenvector: a shift sigma < 0 is nearer to it than to
    any positive eigenvalue, so inverse iteration at sigma0 finds it, and a
    second pass at 1.5 times its estimate sharpens it. Measured."""
    lam, x, res = inverse_iteration(Am, shift=arb(sigma0), x0=x0, iters=8)
    if bool(lam < 0):
        lam, x, res = inverse_iteration(Am, shift=arb(3) / 2 * lam, x0=x, iters=8)
    return lam, x, res


def _sub(Am: arb_mat, n: int) -> arb_mat:
    return arb_mat(n, n, [Am[i, j] for i in range(n) for j in range(n)])


def _vec_dec(xs, digits: int = 40):
    return [x.mid().str(digits, radius=False) for x in xs]


def analyze(q_path: Path, out_path: Path, vec_path: Path, v800_path: Path | None = None,
            state_dir: Path | None = None, env_path: Path | None = None, blocks=(), prec: int = PREC):
    """The spectral record of Q_N (see the module docstring for what is
    enclosure-carrying): midpoint and ball inertia, the lowest eigenvalue and
    its eigenvector, the witness Rayleigh quotient (40-digit decimal vector,
    evaluated on balls containing it) with the spectral eps, leading blocks,
    Q at the T# = 800 eigenvector of R(800), and the comparison with R(800)
    from the stored state."""
    import scout
    ctx.prec = prec
    d = pickle.loads(Path(q_path).read_bytes())
    N, L = d["N"], Fraction(d["L"])
    Q = dec_mat(d["Q"], N)
    eps = 2 * arb(d["eps_spectral"])   # doubled: covers the float roundings in the error budget
    Qm = Q.mid()
    rec = {"L": d["L"], "N": N, "Nx": d["Nx"], "prec": prec, "eps_spectral": d["eps_spectral"],
           "quad_bound": d["quad_bound"], "E_psi": d["E_psi"], "dropped_l1": d["dropped_l1"],
           "max_dev_K_G0_KT_from_I": d["max_dev_K_G0_KT_from_I"],
           "assembly_unit_core_seconds": d["unit_core_seconds"], "assembly_wall_seconds": d["wall_seconds"],
           "max_entry_radius": max(float(Q[i, j].rad()) for i in range(N) for j in range(i + 1))}
    t0 = time.time()
    neg, pos, und, small = ldl_inertia(Qm, balls=False)
    rec["inertia_midpoint"] = {"neg": neg, "pos": pos, "undecided": und, "min_abs_pivot": small}
    print(json.dumps(rec["inertia_midpoint"]), time.time() - t0, flush=True)
    # (a ball LDL without pivoting loses its radius after about 50 pivots on these
    # matrices, by dependency growth, so the count of negative eigenvalues is
    # recorded at the measured grade only; the strict negative enclosure is the
    # witness Rayleigh quotient below)
    # the eigenvalue nearest 0, then the lowest
    lam0, x0, r0 = inverse_iteration(Qm)
    rec["lam_nearest_0"] = {"lam": lam0.str(15, radius=False), "residual": r0}
    lam1, x1, r1 = lowest_eigenpair(Qm, x0) if neg >= 1 else (lam0, x0, r0)
    rec["lam_min"] = {"lam": lam1.str(15, radius=False), "residual": r1}
    print(json.dumps(rec["lam_min"]), flush=True)
    # the witness: the decimals of the eigenvector, as balls that contain them
    vdec = _vec_dec(x1)
    v = [arb(s) for s in vdec]
    rq = quad_form(Q, v)
    upper = rq + arb(0, eps.upper())
    rec["witness"] = {"vector_file": Path(vec_path).name, "digits": 40,
                      "rq_mid": rq.mid().str(15, radius=False), "rq_rad": float(rq.rad()),
                      "rq_upper_with_eps": float(upper.upper()), "negative": bool(upper < 0),
                      "boundary_value_f_L": None}
    La = price.to_arb(L)
    mu = sum((v[i] * ((arb(4 * i + 1) / 2) / La).sqrt() for i in range(N)), arb(0))
    rec["witness"]["boundary_value_f_L"] = mu.mid().str(6, radius=False)
    Path(vec_path).write_text(json.dumps({"L": d["L"], "N": N, "basis": "scout even T_{2i}, i < N",
                                          "v": vdec}, indent=0))
    print(json.dumps(rec["witness"]), flush=True)
    # leading blocks (principal submatrices): where the negativity sets in
    rec["leading_blocks"] = []
    for n2 in blocks:
        A2 = _sub(Qm, n2)
        ng, ps, ud, sm = ldl_inertia(A2, balls=False)
        row = {"N": n2, "neg": ng, "undecided": ud}
        if ng >= 1:
            l2, x2, rr2 = lowest_eigenpair(A2, x1[:n2])
            v2 = [arb(s) for s in _vec_dec(x2)]
            q2 = quad_form(_sub(Q, n2), v2)
            row.update(lam=l2.str(12, radius=False), residual=rr2, rq_upper_with_eps=float((q2 + arb(0, eps.upper())).upper()))
        else:
            l2, _, rr2 = inverse_iteration(A2, x0=x1[:n2])
            row.update(lam_nearest_0=l2.str(12, radius=False), residual=rr2)
        rec["leading_blocks"].append(row)
        print(json.dumps(row), flush=True)
    # Q at the T# = 800 eigenvector of R(800)
    if v800_path is not None:
        x8 = [arb(s) for s in json.loads(Path(v800_path).read_text())["x"]]
        q8 = quad_form(Q, x8)
        mu8 = sum((x8[i] * ((arb(4 * i + 1) / 2) / La).sqrt() for i in range(N)), arb(0)) / \
            sum((x * x for x in x8), arb(0)).sqrt()
        rec["v800"] = {"Q_rq_mid": q8.mid().str(12, radius=False), "Q_rq_rad": float(q8.rad()),
                       "Q_rq_lower_with_eps": float((q8 - arb(0, eps.upper())).lower()),
                       "positive": bool(q8 - arb(0, eps.upper()) > 0), "boundary_value_f_L": mu8.mid().str(6, radius=False)}
        print(json.dumps(rec["v800"]), flush=True)
    # against R(800) from the stored state (measured comparisons)
    if state_dir is not None:
        with ctx.workprec(1280):
            meta, C, G = scout._load_state(Path(state_dir), N)
            S, _, kind = scout.load_envelope(Path(env_path), with_kind=True)
            T = Fraction(1, 2) * meta["k1"]
            beta = scout.beta_star(kind, price.to_arb(T), price.to_arb(S))
            I = arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])
            R = C + beta * (I - G)
        R256 = arb_mat(N, N, [+(R[i, j].mid()) for i in range(N) for j in range(N)])   # rounded to prec
        del C, G, R
        Dm = (Qm - R256).mid()
        rv = quad_form(R256, v)
        rec["vs_R800"] = {"T": float(T), "R800_at_witness": rv.mid().str(12, radius=False)}
        if v800_path is not None:
            r8 = quad_form(R256, x8)
            rec["vs_R800"]["R800_at_v800"] = r8.mid().str(12, radius=False)
            rec["vs_R800"]["tail_at_v800"] = (q8 - r8).mid().str(6, radius=False)
        dneg, dpos, dund, dsmall = ldl_inertia(Dm, balls=False)
        rec["vs_R800"]["inertia_Q_minus_R800_midpoint"] = {"neg": dneg, "pos": dpos, "undecided": dund,
                                                            "min_abs_pivot": dsmall}
        ln, _, lr = inverse_iteration(Dm, shift=-arb(10) ** -40)
        rec["vs_R800"]["Q_minus_R800_eig_nearest_-1e-40"] = {"lam": ln.str(6, radius=False), "residual": lr}
        print(json.dumps(rec["vs_R800"]), flush=True)
    Path(out_path).write_text(json.dumps(rec, indent=1))
    return rec

def _mem_gib() -> float:
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 2 ** 20
    except OSError:
        pass
    return float("inf")


def main():
    import argparse
    ap = argparse.ArgumentParser(description="position-space DH Weil form on the scout basis")
    ap.add_argument("--L", default="171079/100000")
    ap.add_argument("--N", type=int, default=856)
    ap.add_argument("--Nx", type=int, default=None)
    ap.add_argument("--prec", type=int, default=PREC)
    ap.add_argument("--procs", type=int, default=8)
    ap.add_argument("--unit-points", type=int, default=24)
    ap.add_argument("--dir", default=None, help="state directory (running sums, resumable)")
    ap.add_argument("--out", required=True, help="write the assembled Q (lower triangle) and summary here (.pkl)")
    ap.add_argument("--time-node", action="store_true", help="time one node and exit")
    ap.add_argument("--analyze", default=None, help="analyze an assembled Q (.pkl) instead: write --out (.json)")
    ap.add_argument("--vec-out", default=None, help="analyze: witness vector file (.json)")
    ap.add_argument("--v800", default=None, help="analyze: JSON with the T# = 800 eigenvector of R(800) under 'x'")
    ap.add_argument("--state", default=None, help="analyze: run-B restart state directory (read only)")
    ap.add_argument("--env", default=str(HERE / "k2env_dh_L_DH.json"))
    ap.add_argument("--blocks", nargs="*", type=int, default=[])
    args = ap.parse_args()
    L = Fraction(args.L)
    Nx = args.Nx or default_Nx(args.N)
    ctx.prec = args.prec
    if args.analyze:
        analyze(Path(args.analyze), Path(args.out), Path(args.vec_out), Path(args.v800) if args.v800 else None,
                Path(args.state) if args.state else None, Path(args.env), args.blocks, args.prec)
        return
    if args.time_node:
        nodes = gl_sym(2 * args.N - 1)
        t = time.time()
        node_gram(arb(1), nodes, args.N, price.to_arb(L))
        print(json.dumps({"node_seconds": time.time() - t, "points": len(plan_points(L, args.N, Nx))}))
        return
    t0 = time.time()
    red = assemble(L, args.N, Nx, Path(args.dir), args.procs, args.unit_points, args.prec)
    if red is None:
        raise SystemExit(3)
    _, dropped = comb(L)
    eps = spectral_eps(L, args.N, Nx, red["E_psi"], red["K"], dropped)
    I_dev = max(float(abs(red["I_check"][i, j] - (1 if i == j else 0)).upper())
                for i in range(args.N) for j in range(args.N))
    out = {"L": args.L, "N": args.N, "Nx": Nx, "prec": args.prec, "Q": enc_mat(red["Q"]),
           "E_psi": red["E_psi"], "eps_spectral": eps, "quad_bound": quad_error_bound(L, args.N, Nx),
           "dropped_l1": dropped, "max_dev_K_G0_KT_from_I": I_dev,
           "unit_core_seconds": sum(red["unit_seconds"]), "wall_seconds": time.time() - t0}
    _atomic(Path(args.out), pickle.dumps(out, protocol=5))
    print(json.dumps({k: v for k, v in out.items() if k != "Q"}), flush=True)




# ------------------------------------------------------------------ the stage-A form at one vector
#
# v^T R(T#) v for the scout's discrete block (Gauss-Legendre q per panel of
# width h on [0, T#], the snapped nodes of scout.unit) with every step in Arb,
# from data independent of the stored state: F_v(t) = 2 int_0^L f_v(y) cos(ty) dy
# by Gauss-Legendre in y with a Bernstein-ellipse bound (instead of the fast
# Bessel column), and Psi + H from scout.Symbol. A second bound turns the
# discrete sum into the exact integrals of R(T#).

def f_values(v, L: Fraction, ys) -> list:
    """f_v(y) = sum_i v_i phi_{2i}(y) at the points ys, through the Chebyshev
    coefficients K^T v and the one-rotation table."""
    N = len(v)
    K = K_matrix(L, N)
    b = [sum((v[i] * K[i, k] for i in range(k, N)), arb(0)) for k in range(N)]
    La = price.to_arb(L)
    B = _TABLE_B
    A = (N + B - 1) // B
    bm = arb_mat(N, 1, b)
    out = []
    for y in ys:
        phi = 2 * (y / La).acos()
        cs1 = [(j * phi).sin_cos() for j in range(B)]
        cs2 = [(B * a * phi).sin_cos() for a in range(A)]
        R1 = arb_mat(2, B, [c for _, c in cs1] + [sn for sn, _ in cs1])
        R2 = arb_mat(A, 2, [x for sn, c in cs2 for x in (c, -sn)])
        row = arb_mat(1, N, (R2 * R1).entries()[:N])
        out.append((row * bm)[0, 0])
    return out


def sup_f_bound(v, L: Fraction) -> arb:
    """sup_{[-L, L]} |f_v| <= sum_i |v_i| sqrt((4i+1)/(2L))."""
    La = price.to_arb(L)
    return sum((abs(v[i]) * ((arb(4 * i + 1) / 2) / La).sqrt() for i in range(len(v))), arb(0))


def y_quad_bound(v, L: Fraction, n_y: int, t_max: arb, rho: Fraction = Fraction(2), supf: arb | None = None) -> arb:
    """|F_v(t) - 2 GL_{n_y}[f_v cos(t .)]| for 0 <= t <= t_max: Gauss-Legendre on
    [0, L] errs by at most (64/15) M rho^{-2n}/(rho^2 - 1) (L/2) for an integrand
    bounded by M on the Bernstein ellipse; |f_v| <= sup|f_v| rho^D (Bernstein,
    D = 2N - 2) and |cos(tz)| <= cosh(t b), b = (L/4)(rho - 1/rho)."""
    La = price.to_arb(L)
    rh = price.to_arb(rho)
    D = 2 * len(v) - 2
    b = La / 4 * (rh - 1 / rh)
    M = (sup_f_bound(v, L) if supf is None else supf) * rh ** D * (t_max * b).cosh()
    return 2 * arb(64) / 15 * M * rh ** (-2 * n_y) / (rh * rh - 1) * (La / 2)


def _stage_a_panels(args):
    (L, env_path, v_enc, k0, k1, q, h, prec, n_y, rho_y, T_max) = args
    ctx.prec = prec
    import scout
    _, clusters, kind = scout.load_envelope(Path(env_path), with_kind=True)
    sym = scout.Symbol(L, clusters, kind)
    v = [arb(m) * arb(2) ** e if m else arb(0) for m, e in v_enc]
    La = price.to_arb(L)
    ha = price.to_arb(h)
    ys, wy = [], []
    for xi, w in gl_sym(n_y):
        ys.append(La * (1 + xi) / 2)
        wy.append(La * w / 2)
    fy = f_values(v, L, ys)
    supf = sup_f_bound(v, L)
    gl = [arb.legendre_p_root(q, k, weight=True) for k in range(q)]
    deltas = [ha * (1 + x) / 2 for x, _ in gl]
    # row i: [cos(delta_i y_j)]_j then [-sin(delta_i y_j)]_j, so that with
    # ab = [w f cos(a0 y)] + [w f sin(a0 y)], (CS ab)_i = sum_j w_j f_j cos((a0 + delta_i) y_j)
    flat = []
    for d in deltas:
        sc_d = [(d * y).sin_cos() for y in ys]
        flat.extend(c for _, c in sc_d)
        flat.extend(-sn for sn, _ in sc_d)
    CS = arb_mat(q, 2 * n_y, flat)
    snap = arb(2) ** -1200          # the scout snaps tL to a 1280-bit midpoint (shift below 2^-1268)
    # |F_v'(t)| = |2 int_0^L y f_v(y) sin(ty) dy| <= 2 L sqrt(L/2) |v|: widens F for the snap
    Fsnap = 2 * La * (La / 2).sqrt() * sum((x * x for x in v), arb(0)).sqrt() * snap
    vCv, vGv = arb(0), arb(0)
    for k in range(k0, k1):
        a0 = ha * k
        ab = []
        sc = [(a0 * y).sin_cos() for y in ys]
        ab = [wy[j] * fy[j] * sc[j][1] for j in range(n_y)] + [wy[j] * fy[j] * sc[j][0] for j in range(n_y)]
        Fq = CS * arb_mat(2 * n_y, 1, ab)
        Ey = y_quad_bound(v, L, n_y, ha * (k + 1), rho_y, supf)
        for i, (x, w) in enumerate(gl):
            t = a0 + deltas[i]
            t = t + arb(0, snap.upper())
            F = 2 * Fq[i, 0] + arb(0, (Ey + Fsnap).upper())     # Ey: this panel's y-quadrature bound
            ww = w * ha / 2 / arb.pi()
            F2 = F * F
            vGv += ww * F2
            vCv += ww * (sym.psi(t) + sym.H(t)) * F2
    return k0, k1, (vCv.mid().man_exp(), float(vCv.rad())), (vGv.mid().man_exp(), float(vGv.rad()))


def _dec_arb(x):
    (m, e), r = x
    return (arb(m) * arb(2) ** e if m else arb(0)) + arb(0, r * (1 + 2.0 ** -40))


def t_quad_bound(L: Fraction, env_path: Path, v, h: Fraction, q: int, T: Fraction, b: Fraction = Fraction(1)) -> arb:
    """|sum_k w_k phi(t_k) - int_0^T phi| for phi = (Psi + H) F_v^2 / pi and for
    phi = F_v^2 / pi (the larger bound is returned): per panel of width h,
    Gauss-Legendre errs by at most (64/15) M rho^{-2q}/(rho^2 - 1) (h/2), rho the
    ellipse through +-i b, M the maximum of |phi| there. On |Im z| <= b < 3/2:
    |F_v(z)| <= 2 cosh(L b) sqrt(L/2) |v|; |H| <= sum |h_k| cosh(omega_k b);
    |P| <= sum |c_n| cosh(b log n); Re digamma and log(5/pi) are bounded by
    Arb on boxes covering 3/4 - b/2 <= Re w <= 3/4 + b/2, |Im w| <= T/2 + 1."""
    import scout
    _, clusters, kind = scout.load_envelope(Path(env_path), with_kind=True)
    La = price.to_arb(L)
    ba = price.to_arb(b)
    ha = price.to_arb(h)
    nv = sum((x * x for x in v), arb(0)).sqrt()
    Fb = 2 * (La * ba).cosh() * (La / 2).sqrt() * nv
    Hb = arb(0)
    for primes, om, hs in clusters:
        logs = [arb(p).log() for p in primes]
        for kv, hk in zip(om, hs):
            omega = abs(sum((ki * li for ki, li in zip(kv, logs)), arb(0)))
            Hb += abs(price.to_arb(hk)) * (omega * ba).cosh()
    Pb = sum((abs(c) * (ba * arb(n).log()).cosh() for n, c in price.dh_comb(L)), arb(0))
    # digamma(3/4 + i z/2), z = t + i y with |y| <= b: w = 3/4 - y/2 + i t/2
    dg = arb(0)
    lo, hi = arb(3) / 4 - ba / 2, arb(3) / 4 + ba / 2
    re = arb((lo + hi).mid() / 2, ((hi - lo) / 2).upper())
    top = int(math.ceil(float(T) / 2)) + 2
    for m in range(-1, top):
        im = arb(m + arb(1) / 2, arb(1) / 2 + arb(2) ** -30)
        val = abs(acb(re, im).digamma())
        dg = max(dg, arb(val.upper()))
    sym_b = dg + abs((arb(5) / arb.pi()).log()) + Pb + Hb
    M = sym_b * Fb * Fb / arb.pi()
    rho = (ba + (ba * ba + (ha / 2) ** 2).sqrt()) / (ha / 2)
    per = arb(64) / 15 * M * rho ** (-2 * q) / (rho * rho - 1) * (ha / 2)
    npan = int(Fraction(T) / h)
    return per * npan


def stage_a_form(L: Fraction, env_path: Path, v, T: Fraction, q: int = 64, h: Fraction = Fraction(1, 2),
                 prec: int = PREC, n_y: int = 1500, rho_y: Fraction = Fraction(2), procs: int = 8,
                 panels_per_job: int = 50) -> dict:
    """Enclosures of v^T C(T) v, v^T G(T) v and v^T R(T) v / v^T v for the
    scout's discrete stage-A block at T (DH, even, P2 = 0), and the bound
    that turns them into the exact integrals."""
    import multiprocessing as mpc
    import scout
    ctx.prec = prec
    S, _, kind = scout.load_envelope(Path(env_path), with_kind=True)
    if kind != "dh":
        raise ValueError("written for the DH case (no pole term)")
    npan = int(Fraction(T) / h)
    v_enc = [x.mid().man_exp() for x in v]
    jobs = [(L, str(env_path), v_enc, k, min(k + panels_per_job, npan), q, h, prec, n_y, rho_y, T)
            for k in range(0, npan, panels_per_job)]
    t0 = time.time()
    vC, vG = arb(0), arb(0)
    if procs > 1:
        with mpc.get_context("spawn").Pool(procs) as pool:
            res = list(pool.imap_unordered(_stage_a_panels, jobs))
    else:
        res = [_stage_a_panels(j) for j in jobs]
    for _, _, c, g in res:
        vC += _dec_arb(c)
        vG += _dec_arb(g)
    ctx.prec = prec
    vv = sum((x * x for x in v), arb(0))
    beta = scout.beta_star(kind, price.to_arb(Fraction(T)), price.to_arb(S))
    num = vC + beta * (vv - vG)
    tq = t_quad_bound(L, env_path, v, h, q, Fraction(T))
    exact = num + arb(0, ((1 + abs(beta)) * tq).upper())
    return {"T": float(T), "q": q, "n_y": n_y, "beta": beta, "vCv": vC, "vGv": vG, "vv": vv,
            "rq_discrete": num / vv, "rq_exact_integrals": exact / vv, "t_quad_bound": tq,
            "core_seconds": None, "wall_seconds": time.time() - t0}


def stage_a_main(argv=None):
    """CLI: python witness.py stage-a VEC.json KEY T OUT.json [q] [procs]
    (KEY is the vector's key in VEC.json, 'x' or 'v')."""
    import scout
    argv = argv if argv is not None else sys.argv[2:]
    vec_path, key, T, out = Path(argv[0]), argv[1], Fraction(argv[2]), Path(argv[3])
    q = int(argv[4]) if len(argv) > 4 else 64
    procs = int(argv[5]) if len(argv) > 5 else 2
    ctx.prec = PREC
    v = [arb(s) for s in json.loads(vec_path.read_text())[key]]
    v = [x.mid() for x in v]          # the vector evaluated is this exact dyadic one
    r = stage_a_form(L_DH_WINDOW, HERE / "k2env_dh_L_DH.json", v, T, q=q, procs=procs)
    S, _, _ = scout.load_envelope(HERE / "k2env_dh_L_DH.json", with_kind=True)
    rec = {"vector": vec_path.name, "key": key, "N": len(v), "T": float(T), "q": q, "h": "1/2", "n_y": r["n_y"],
           "prec": PREC, "beta": r["beta"].mid().str(15, radius=False),
           "rq_discrete_mid": r["rq_discrete"].mid().str(15, radius=False), "rq_discrete_rad": float(r["rq_discrete"].rad()),
           "rq_discrete_upper": float(r["rq_discrete"].upper()),
           "rq_exact_integrals_mid": r["rq_exact_integrals"].mid().str(15, radius=False),
           "rq_exact_integrals_upper": float(r["rq_exact_integrals"].upper()),
           "t_quad_bound": float(r["t_quad_bound"].upper()),
           "mass_above_T_mid": ((r["vv"] - r["vGv"]) / r["vv"]).mid().str(8, radius=False),
           "mass_above_T_upper": float(((r["vv"] - r["vGv"]) / r["vv"]).upper()),
           "wall_seconds": r["wall_seconds"], "procs": procs}
    out.write_text(json.dumps(rec, indent=1))
    print(json.dumps(rec), flush=True)


# ------------------------------------------------------------------ derived records (reproducible drivers)
#
# The pieces of witness_q856.json beyond the analysis: leading blocks, the
# block witness at the onset, its re-assembly by this code at its own size,
# and the Sylvester counts of Q_N - R(800) + sigma I. Each reads the assembled
# Q (q856.pkl); `record` merges them as committed.

def _load_q(q_path: Path):
    ctx.prec = PREC
    d = pickle.loads(Path(q_path).read_bytes())
    return d, dec_mat(d["Q"], d["N"]), 2 * arb(d["eps_spectral"])


def leading_blocks(q_path: Path, sizes) -> list[dict]:
    """Midpoint LDL inertia of the leading n x n blocks of Q (measured) and,
    where a negative pivot appears, the lowest eigenpair and the enclosed
    Rayleigh upper bound (with the doubled eps of the full assembly) at its
    40-digit eigenvector."""
    d, Q, eps = _load_q(q_path)
    Qm = Q.mid()
    out = []
    for n in sizes:
        A = _sub(Qm, n)
        ng, ps, ud, sm = ldl_inertia(A, balls=False)
        row = {"N": n, "neg": ng, "undecided": ud}
        if ng >= 1:
            lam, x, r = lowest_eigenpair(A)
            q = quad_form(_sub(Q, n), [arb(s) for s in _vec_dec(x)])
            row.update(lam=lam.str(12, radius=False), residual=r,
                       rq_upper_with_eps=float((q + arb(0, eps.upper())).upper()))
        else:
            lam, _, r = inverse_iteration(A)
            row.update(lam_nearest_0=lam.str(12, radius=False), residual=r)
        out.append(row)
        print(json.dumps(row), flush=True)
    return out


def block_witness(q_path: Path, n: int) -> dict:
    """The n-mode block witness: lowest eigenpair of the leading block, its
    40-digit vector and enclosed quotient (witness_v101.json for n = 101)."""
    d, Q, eps = _load_q(q_path)
    lam, x, r = lowest_eigenpair(_sub(Q.mid(), n))
    vd = _vec_dec(x)
    v = [arb(s) for s in vd]
    q = quad_form(_sub(Q, n), v)
    La = price.to_arb(Fraction(d["L"]))
    mu = sum((v[i] * ((arb(4 * i + 1) / 2) / La).sqrt() for i in range(n)), arb(0))
    return {"L": d["L"], "N": n, "basis": f"scout even T_{{2i}}, i < N (the leading {n} modes of Q_{d['N']})",
            "v": vd, "rq_mid": q.mid().str(15, radius=False), "rq_rad": float(q.rad()),
            "eps_used": float(eps.upper()), "rq_upper_with_eps": float((q + arb(0, eps.upper())).upper()),
            "lam": lam.str(15, radius=False), "residual": r, "boundary_value_f_L": mu.mid().str(6, radius=False)}


def reassemble(vec_path: Path, prec: int = 320, L: Fraction = L_DH_WINDOW) -> dict:
    """Q_N assembled again by this code at its own size N = len(v) (its own
    Gauss nodes in y and x, precision prec) and evaluated at the stored vector,
    with its own error budget (eps doubled). Not an independent implementation."""
    v = json.loads(Path(vec_path).read_text())["v"]
    N = len(v)
    ctx.prec = prec
    Nx = default_Nx(N)
    t0 = time.time()
    red = reduce_parts(L, N, [unit(L, N, Nx, 0, 10 ** 9, prec=prec)], prec)
    _, dropped = comb(L)
    eps = 2 * spectral_eps(L, N, Nx, red["E_psi"], red["K"], dropped)
    q = quad_form(red["Q"], [arb(s) for s in v])
    return {"N": N, "Nx": Nx, "M": 2 * N - 1, "prec": prec, "seconds": time.time() - t0,
            "rq_mid": q.mid().str(15, radius=False), "rq_rad": float(q.rad()), "eps": eps,
            "rq_upper_with_eps": float((q + arb(0, eps)).upper())}


def shifted_counts(q_path: Path, state_dir: Path, env_path: Path, exps=(-66, -64, -62, -60, -55, -50)) -> dict:
    """Sylvester counts of (Q_N - R(T#)) + sigma I on midpoints at 256 bits,
    R(T#) = C + beta*(I - G) from the stored restart state (read only, 1280
    bits, rounded). Measured."""
    import scout
    d, Q, _ = _load_q(q_path)
    N = d["N"]
    with ctx.workprec(1280):
        meta, C, G = scout._load_state(Path(state_dir), N)
        S, _, kind = scout.load_envelope(Path(env_path), with_kind=True)
        T = Fraction(1, 2) * meta["k1"]
        beta = scout.beta_star(kind, price.to_arb(T), price.to_arb(S))
        I = arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])
        R = C + beta * (I - G)
    R256 = arb_mat(N, N, [+(R[i, j].mid()) for i in range(N) for j in range(N)])
    del C, G, R
    D = (Q.mid() - R256).mid()
    I = arb_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])
    out = {"N": N, "T": float(T), "counts": []}
    for e in exps:
        neg, pos, und, sm = ldl_inertia((D + arb(10) ** e * I).mid(), balls=False)
        row = {"sigma": f"1e{e}", "neg": neg, "pos": pos, "undecided": und}
        out["counts"].append(row)
        print(json.dumps(row), flush=True)
    return out


def merge_record(analysis: Path, blocks, onset_vec: Path, reassembled: Path, counts: Path, responses: Path,
                 slices: Path, q_pkl_sha256: str) -> dict:
    """witness_q856.json: the analysis record with the leading blocks merged in
    order of size, the onset, the counts, the re-assembly, the responses of the
    stored T# = 800 block and the timed slices."""
    rec = json.loads(Path(analysis).read_text())
    by = {b["N"]: b for b in rec["leading_blocks"]}
    for f in blocks:
        for b in json.loads(Path(f).read_text()):
            by[b["N"]] = b
    rec["leading_blocks"] = [by[n] for n in sorted(by)]
    first = min(n for n, b in by.items() if b["neg"] >= 1)
    last = max(n for n, b in by.items() if b["neg"] == 0 and n < first)
    rec["onset"] = {"last_block_without_negative_pivot": last, "first_block_with_one": first,
                    "witness_file": Path(onset_vec).name}
    rec["Q_minus_R800_shifted_counts"] = json.loads(Path(counts).read_text())["counts"]
    rec["reassembled_101"] = json.loads(Path(reassembled).read_text())
    rec["assembly_q856_pkl_sha256"] = q_pkl_sha256
    rec["grade"] = ("hardened: ball enclosures carry every step of the witness quotients (exact Gauss sums for g, "
                    "Arb-bounded Gauss-Legendre error in x, carried dropped-radius bound, dropped comb mass); "
                    "inertia counts and lambda values are midpoint (measured)")
    r = json.loads(Path(responses).read_text())
    rec["responses_T800"] = {"source": "scout.py --responses-at-state on the run-B restart state at T# = 800 "
                                       "(1280 bits)", "responses": r["responses"], "seconds": r["responses_seconds"]}
    rec["timed_slices"] = [json.loads(line) for line in Path(slices).read_text().splitlines() if line.startswith("{")]
    return rec


def derived_main(argv):
    """CLI for the derived records: blocks Q.pkl OUT N...; block-witness Q.pkl n OUT;
    reassemble VEC prec OUT; shifted-counts Q.pkl STATE OUT; record OUT analysis
    onset_vec reassembled counts responses slices q_sha blocks..."""
    cmd = argv[0]
    if cmd == "blocks":
        res = leading_blocks(Path(argv[1]), [int(x) for x in argv[3:]])
        Path(argv[2]).write_text(json.dumps(res, indent=1))
    elif cmd == "block-witness":
        res = block_witness(Path(argv[1]), int(argv[2]))
        Path(argv[3]).write_text(json.dumps(res, indent=0))
        print(json.dumps({k: v for k, v in res.items() if k != "v"}))
    elif cmd == "reassemble":
        res = reassemble(Path(argv[1]), int(argv[2]))
        Path(argv[3]).write_text(json.dumps(res, indent=1))
        print(json.dumps(res))
    elif cmd == "shifted-counts":
        res = shifted_counts(Path(argv[1]), Path(argv[2]), HERE / "k2env_dh_L_DH.json")
        Path(argv[3]).write_text(json.dumps(res, indent=1))
    elif cmd == "record":
        out, analysis, onset_vec, reas, counts, resp, slices, sha = argv[1:9]
        res = merge_record(Path(analysis), argv[9:], Path(onset_vec), Path(reas), Path(counts), Path(resp),
                           Path(slices), sha)
        Path(out).write_text(json.dumps(res, indent=1))
    else:
        raise SystemExit(f"unknown command {cmd}")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "stage-a":
        stage_a_main()
    elif len(sys.argv) > 1 and sys.argv[1] in ("blocks", "block-witness", "reassemble", "shifted-counts", "record"):
        derived_main(sys.argv[1:])
    else:
        main()
