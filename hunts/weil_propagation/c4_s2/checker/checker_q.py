"""checker/: an independent implementation of the Weil form Q on the shared basis.

Built from theory ``RESULTS.md`` s0 (Zhu arXiv:2608.24827 eq. (2)-(3),
Lemma 2.5 normalisation) and nothing else. It does not import or port
``hunts/rogue_frontier/weil_trunc/galerkin.py``; that module is used only as
an oracle in the tests.

The form (theory s0), for a window of length L = log c and real f on [0, L]
with autocorrelation g(x) = int f(y) f(y - x) dy:

    Q(f) = P(f) + A(f) - sum_{log n < L} 2 Lambda(n) n^{-1/2} g(log n),
    P(f) = 2 int g(x) cosh(x/2) dx,
    A(f) = -[gamma + log pi + log(1 - e^{-2L})] g(0)
           + int_0^L 2 [e^{-2x} g(0) - e^{-x/2} g(x)] / (1 - e^{-2x}) dx.

Basis and matrix (derivation, done here). U_n(y) = L^{-1/2} exp(2 pi i n y/L),
n = -N..N, f = sum v_n U_n. For complex f the form only sees the symmetrised
correlation w(x) = g(x) + g(-x) = 2 Re g(x) on x in [0, L], and
w(x) = v^* K(x) v with the real symmetric kernel

    K_ab(x) = [sin(w_a x) - sin(w_b x)] / (pi (b - a))    (a != b),
    K_aa(x) = 2 (1 - x/L) cos(w_a x),                      w_k = 2 pi k / L.

(For f = U_a: g(x) = (1 - x/L) e^{i w_a x} on [0, L]; the off-diagonal entry
follows from int_x^L e^{2 pi i (b-a) y/L} dy.) In terms of w the form reads,
with g = w/2 and g(0) = w(0)/2:

    P(w)     = 2 int_0^L w(x) cosh(x/2) dx,
    A(w)     = -[gamma + log pi + log(1 - e^{-2L})] w(0)/2
               + int_0^L [e^{-2x} w(0) - e^{-x/2} w(x)] / (1 - e^{-2x}) dx,
    prime(w) = - sum_{log n < L} Lambda(n) n^{-1/2} w(log n),

and M_ab = Q(K_ab). The matrix is real symmetric and F(f) = v^* M v.

**The x -> 0 limit, analytically.** The A integrand is 0/0 at x = 0. It is
evaluated in the rearranged form

    [ e^{-2x} D(x) + w(x) e^{-x/2} expm1(-3x/2) ] / (-expm1(-2x)),
    D(x) := w(0) - w(x)   (supplied in closed, cancellation-free form),

in which every factor carries full relative precision near 0, so no finite
difference and no subtraction of O(1) quantities occurs. For the basis
kernels D is exact: D = -K_ab for a != b (K_ab(0) = 0), and
D = 4 sin^2(w_a x/2) + (2x/L) cos(w_a x) on the diagonal. The limits are
A-integrand(0) = -w'(0)/2 - 3 w(0)/4, i.e. 1/L - 3/2 on the diagonal and
-(w_a - w_b)/(2 pi (b - a)) = 1/L off it; ``a_integrand_limit`` states them
and a test compares them with the integrand at x = 1e-30.

The pole block P is in closed form (elementary exponential integrals, using
e^{i w_k L} = 1). House rules: mpmath only, every public function takes an
explicit dps and uses ``mp.workdps``; nothing leaves global state modified.
"""

from __future__ import annotations

from mpmath import mp

# --------------------------------------------------------------------------
# arithmetic: atoms of the zeta Weil distribution inside the window
# --------------------------------------------------------------------------


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def zeta_atoms(c) -> list[tuple[int, int]]:
    """[(n, p)]: prime powers n = p^k with log n < log c, i.e. n < c (strict).

    Theory s0 sums over log n < l. On c in [2, 3) this is [(2, 2)]."""
    out = []
    n = 2
    while n < c:
        p = next(d for d in range(2, n + 1) if n % d == 0)  # least prime factor
        m = n
        while m % p == 0:
            m //= p
        if m == 1:
            out.append((n, p))
        n += 1
    return out


# --------------------------------------------------------------------------
# the scalar functional on a symmetrised correlation w
# --------------------------------------------------------------------------


def _panels(L, k: int, breaks=()):
    m = max(4, 2 * abs(int(k)))
    pts = [L * mp.mpf(i) / m for i in range(m + 1)]
    return sorted(set(pts + [mp.mpf(b) for b in breaks if 0 < b < L]))


def a_integrand(w, D, x):
    """The rearranged A integrand at x > 0 (see module docstring)."""
    num = mp.e ** (-2 * x) * D(x) + w(x) * mp.e ** (-x / 2) * mp.expm1(-3 * x / 2)
    return num / (-mp.expm1(-2 * x))


def a_constant(L):
    """-[gamma + log pi + log(1 - e^{-2L})], the coefficient of w(0)/2."""
    return -(mp.euler + mp.log(mp.pi) + mp.log(-mp.expm1(-2 * L)))


def pole_part(w, L, k_hint: int = 0, breaks=()):
    return 2 * mp.quad(lambda x: w(x) * mp.cosh(x / 2), _panels(L, k_hint, breaks))


def arch_part(w, D, w0, L, k_hint: int = 0, breaks=()):
    integral = mp.quad(lambda x: a_integrand(w, D, x), _panels(L, k_hint, breaks))
    return a_constant(L) * w0 / 2 + integral


def prime_part(w, c, atoms=None):
    atoms = zeta_atoms(c) if atoms is None else atoms
    return -mp.fsum(mp.log(p) / mp.sqrt(n) * w(mp.log(n)) for n, p in atoms)


def q_of_w(w, D, c, dps: int = 40, k_hint: int = 0, atoms=None, breaks=()) -> dict:
    """Q on a symmetrised correlation w = g(x) + g(-x) on [0, L], by quadrature.

    ``D(x) = w(0) - w(x)`` must be supplied in a cancellation-free form.
    Valid for any w of a function supported in a window of length <= L.
    ``breaks``: points in (0, L) where w has a kink (panel boundaries).
    Returns the three parts and their sum, at ``dps``."""
    with mp.workdps(dps + 10):
        c_ = mp.mpf(c)
        L = mp.log(c_)
        w0 = w(mp.mpf(0))
        P = pole_part(w, L, k_hint, breaks)
        A = arch_part(w, D, w0, L, k_hint, breaks)
        R = prime_part(w, c_, atoms)
        out = {"pole": P, "arch": A, "prime": R, "Q": P + A + R}
    with mp.workdps(dps):
        return {k: +v for k, v in out.items()}


# --------------------------------------------------------------------------
# the matrix on the shared basis
# --------------------------------------------------------------------------


def a_integrand_limit(L, kind: str, a: int = 0, b: int = 0):
    """Analytic value of the A integrand at x = 0 for a basis kernel.

    General: lim = -w'(0)/2 - 3 w(0)/4. Diagonal: w(0) = 2, w'(0) = -2/L,
    so 1/L - 3/2. Off-diagonal: w(0) = 0, w'(0) = (w_a - w_b)/(pi (b - a))
    = -2/L, so 1/L."""
    if kind == "diag":
        return 1 / L - mp.mpf(3) / 2
    return 1 / L


def _pole_sine(L, k: int):
    """P(s_k), s_k(x) = sin(w_k x): 2 int_0^L sin(w x) cosh(x/2) dx.

    Closed form: -w (e^{L/2} + e^{-L/2} - 2) / (1/4 + w^2), since
    int_0^L e^{(beta + i w) x} dx = (e^{beta L} - 1)/(beta + i w)."""
    om = 2 * mp.pi * k / L
    return -om * 4 * mp.sinh(L / 4) ** 2 / (mp.mpf(1) / 4 + om * om)


def _pole_diag(L, k: int):
    """P(c_k), c_k(x) = 2 (1 - x/L) cos(w_k x).

    int_0^L (1 - x/L) e^{z x} dx = -1/z + (e^{z L} - 1)/(L z^2) with
    e^{z L} = e^{beta L} for z = beta + i w_k; P = 2 Re[J(1/2+iw) + J(-1/2+iw)]."""
    om = 2 * mp.pi * k / L
    tot = mp.mpf(0)
    for beta in (mp.mpf(1) / 2, -mp.mpf(1) / 2):
        z = mp.mpc(beta, om)
        tot += mp.re(-1 / z + (mp.e ** (beta * L) - 1) / (L * z * z))
    return 2 * tot


def _arch_sine(L, k: int):
    """A(s_k): w = s_k, w(0) = 0, D = -s_k."""
    om = 2 * mp.pi * k / L
    s = lambda x: mp.sin(om * x)
    return arch_part(s, lambda x: -s(x), mp.mpf(0), L, k)


def _arch_diag(L, k: int):
    """A(c_k): w(0) = 2, D = 4 sin^2(w x/2) + (2x/L) cos(w x)."""
    om = 2 * mp.pi * k / L
    w = lambda x: 2 * (1 - x / L) * mp.cos(om * x)
    D = lambda x: 4 * mp.sin(om * x / 2) ** 2 + (2 * x / L) * mp.cos(om * x)
    return arch_part(w, D, mp.mpf(2), L, k)


def _prime_sine(c, L, k: int):
    om = 2 * mp.pi * k / L
    return prime_part(lambda x: mp.sin(om * x), c)


def _prime_diag(c, L, k: int):
    om = 2 * mp.pi * k / L
    return prime_part(lambda x: 2 * (1 - x / L) * mp.cos(om * x), c)


def _gl_nodes(L, n_panels: int, degree: int):
    """Composite Gauss-Legendre rule on [0, L]: n_panels equal panels, each
    with the 3 * 2^(degree-1) point rule of mpmath (at the ambient precision)."""
    from mpmath.calculus.quadrature import GaussLegendre

    gl = GaussLegendre(mp)
    out = []
    for i in range(n_panels):
        a = L * mp.mpf(i) / n_panels
        b = L * mp.mpf(i + 1) / n_panels
        out.extend(gl.get_nodes(a, b, degree, mp.prec))
    return out


def _arch_sequences_gl(L, N: int, nodes):
    """A(s_k), k = 1..N, and A(c_k), k = 0..N, on one shared node set.

    The sine integrand reduces to s_k(x) rho(x), rho = -e^{-x/2}/(-expm1(-2x));
    the diagonal integrand is the rearranged form of the module docstring."""
    const = a_constant(L)
    xs = [x for x, _ in nodes]
    ws = [w for _, w in nodes]
    rho = [-mp.e ** (-x / 2) / (-mp.expm1(-2 * x)) for x in xs]
    e2 = [mp.e ** (-2 * x) for x in xs]
    em = [mp.e ** (-x / 2) * mp.expm1(-3 * x / 2) for x in xs]
    den = [-mp.expm1(-2 * x) for x in xs]
    S = [mp.mpf(0)]
    Dg = []
    for k in range(N + 1):
        om = 2 * mp.pi * k / L
        tot_s = []
        tot_d = []
        for x, w, r, a2, am, dd in zip(xs, ws, rho, e2, em, den):
            sn = mp.sin(om * x)
            cs = mp.cos(om * x)
            sh = mp.sin(om * x / 2)
            if k > 0:
                tot_s.append(w * sn * r)
            wx = 2 * (1 - x / L) * cs
            Dx = 4 * sh * sh + (2 * x / L) * cs
            tot_d.append(w * (a2 * Dx + wx * am) / dd)
        if k > 0:
            S.append(mp.fsum(tot_s))
        Dg.append(const + mp.fsum(tot_d))
    return S, Dg


def q_parts(c, N: int, dps: int = 40, method: str = "gl", with_error: bool = False) -> dict:
    """The three blocks and Q as (2N+1) x (2N+1) real symmetric mpmath matrices.

    Index 0 is n = -N. Entries for |n|, |m| <= N do not depend on N (fixed
    form, fixed orthonormal basis), so a smaller N is a central principal
    submatrix. Keys: "pole", "arch", "prime", "Q"; all at ``dps``.

    method "gl": composite Gauss-Legendre with max(8, N) panels of degree 5
    (48 nodes each) shared by every k; with_error=True reruns the arch
    sequences at degree 6 and reports the largest change as "quad_err".
    method "ts": mpmath tanh-sinh per entry (slow; used as a cross-check)."""
    N = int(N)
    with mp.workdps(dps + 10):
        c_ = mp.mpf(c)
        L = mp.log(c_)
        pole = ([mp.mpf(0)] + [_pole_sine(L, k) for k in range(1, N + 1)],
                [_pole_diag(L, k) for k in range(N + 1)])
        prime = ([mp.mpf(0)] + [_prime_sine(c_, L, k) for k in range(1, N + 1)],
                 [_prime_diag(c_, L, k) for k in range(N + 1)])
        quad_err = None
        if method == "gl":
            n_pan = max(8, N)
            arch = _arch_sequences_gl(L, N, _gl_nodes(L, n_pan, 5))
            if with_error:
                arch6 = _arch_sequences_gl(L, N, _gl_nodes(L, n_pan, 6))
                quad_err = max(
                    [abs(x - y) for x, y in zip(arch[0], arch6[0])]
                    + [abs(x - y) for x, y in zip(arch[1], arch6[1])]
                )
        elif method == "ts":
            arch = ([mp.mpf(0)] + [_arch_sine(L, k) for k in range(1, N + 1)],
                    [_arch_diag(L, k) for k in range(N + 1)])
        else:
            raise ValueError(method)
        mats = {}
        for name, (S, Dg) in (("pole", pole), ("arch", arch), ("prime", prime)):
            sgn = lambda k, S=S: S[k] if k >= 0 else -S[-k]
            M = mp.matrix(2 * N + 1)
            for i, a in enumerate(range(-N, N + 1)):
                M[i, i] = Dg[abs(a)]
                for j in range(i + 1, 2 * N + 1):
                    b = j - N
                    v = (sgn(a) - sgn(b)) / (mp.pi * (b - a))
                    M[i, j] = v
                    M[j, i] = v
            mats[name] = M
        mats["Q"] = mats["pole"] + mats["arch"] + mats["prime"]
    with mp.workdps(dps):
        out = {k: v * 1 for k, v in mats.items()}
        if quad_err is not None:
            out["quad_err"] = +quad_err
        return out


def Q_matrix(c, N: int, dps: int = 40):
    """The checker's Q on the shared basis: F(f) = v^* Q v, index 0 is n = -N."""
    return q_parts(c, N, dps)["Q"]


def central_block(M, N_small: int):
    """Central (2 N_small + 1) principal submatrix of a (2N+1) matrix
    (entries copied without rounding)."""
    N = (M.rows - 1) // 2
    off = N - N_small
    n = 2 * N_small + 1
    with mp.workdps(max(mp.dps, 80)):
        B = mp.matrix(n)
        for i in range(n):
            for j in range(n):
                B[i, j] = M[i + off, j + off]
    return B


# --------------------------------------------------------------------------
# linear functionals on v: the transform at 0 and at -+ i/2
# --------------------------------------------------------------------------


def transform_rows(c, N: int, dps: int = 40) -> dict:
    """Row vectors r with (r . v) = a transform value of f = sum v_n U_n.

    "zero":  int_0^L f(y) dy = L^{1/2} v_0                    (f-hat(0)),
    "minus": int_0^L f(y) e^{-y/2} dy, entry L^{-1/2}(e^{-L/2} - 1)/(i w_n - 1/2),
    "plus":  int_0^L f(y) e^{+y/2} dy, entry L^{-1/2}(e^{+L/2} - 1)/(i w_n + 1/2).

    Connes-Consani arXiv:2006.13771 use F(g)(s) = int g(v) v^{-is} d*v (their
    (22)); with v = e^{x}, x = y - L/2, g-hat(-i/2) = int g v^{-1/2} d*v is
    e^{L/4} times "minus", and g-hat(+i/2) is e^{-L/4} times "plus"."""
    with mp.workdps(dps + 10):
        L = mp.log(mp.mpf(c))
        sq = mp.sqrt(L)
        z = [mp.mpc(0)] * (2 * N + 1)
        z[N] = mp.mpc(sq)
        mi, pl = [], []
        for n in range(-N, N + 1):
            om = 2 * mp.pi * n / L
            mi.append((mp.e ** (-L / 2) - 1) / (sq * mp.mpc(-mp.mpf(1) / 2, om)))
            pl.append((mp.e ** (L / 2) - 1) / (sq * mp.mpc(mp.mpf(1) / 2, om)))
    with mp.workdps(dps):
        return {
            "zero": [+x for x in z],
            "minus": [+x for x in mi],
            "plus": [+x for x in pl],
        }


def constraint_basis(rows, dim: int, dps: int = 40):
    """Orthonormal basis (as columns of a dim x (dim - k) matrix) of
    {v : r . v = 0 for every r in rows}, by modified Gram-Schmidt.

    The constraint r . v = 0 is <conj(r), v> = 0 for the Hermitian product,
    so the subspace is the orthogonal complement of the conj(r)."""
    with mp.workdps(dps + 10):
        vecs = [[mp.conj(x) for x in r] for r in rows]
        vecs += [[mp.mpc(1) if i == j else mp.mpc(0) for i in range(dim)] for j in range(dim)]
        basis = []
        for v in vecs:
            v = list(v)
            for _ in range(2):  # reorthogonalise once
                for u in basis:
                    ip = mp.fsum(mp.conj(u[i]) * v[i] for i in range(dim))
                    v = [v[i] - ip * u[i] for i in range(dim)]
            nrm = mp.sqrt(mp.fsum(abs(x) ** 2 for x in v))
            if nrm > mp.mpf(10) ** (-(dps // 2)):
                basis.append([x / nrm for x in v])
        keep = basis[len(rows):]
        B = mp.matrix(dim, len(keep))
        for j, u in enumerate(keep):
            for i in range(dim):
                B[i, j] = u[i]
    with mp.workdps(dps):
        return B * 1


def compress(M, B, dps: int = 40):
    """B^* M B for a basis matrix B (columns orthonormal), at ``dps``."""
    with mp.workdps(dps):
        return B.H * M * B


# --------------------------------------------------------------------------
# spectra
# --------------------------------------------------------------------------


def eigvals_hermitian(M, dps: int = 40):
    """Ascending eigenvalues of a Hermitian mpmath matrix (real or complex)."""
    with mp.workdps(dps):
        complex_entries = any(
            isinstance(M[i, j], mp.mpc) and mp.im(M[i, j]) != 0
            for i in range(M.rows)
            for j in range(M.cols)
        )
        if complex_entries:
            E = mp.eighe(M, eigvals_only=True)
        else:
            R = mp.matrix(M.rows)
            for i in range(M.rows):
                for j in range(M.cols):
                    R[i, j] = mp.re(M[i, j])
            E = mp.eigsy(R, eigvals_only=True)
        return sorted(mp.re(e) for e in E)


def inertia(evals, tol) -> tuple[int, int, int]:
    """(n_minus, n_undecided, n_plus): an eigenvalue within tol of 0 is undecided."""
    neg = sum(1 for e in evals if e < -tol)
    pos = sum(1 for e in evals if e > tol)
    return neg, len(evals) - neg - pos, pos
