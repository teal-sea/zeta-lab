"""positivity_geometry: Weil's positivity proof for curves, its exact finite-field shadow,
and the arithmetic hypotheses that do not replace it.

Hunt #150 (`hunts/rh_moonshot/`), mechanism 4. Grades and the full argument are in
`NOTES.md`; this module is the computation behind them. Nothing here is a result about
the zeros of zeta.

The construction
----------------
For a smooth projective curve C of genus g over F_q, let S = C x C, F1 = {pt} x C,
F2 = C x {pt}, and for n >= 0 let G_n be the graph of the n-th power of Frobenius
(G_0 = the diagonal); for n < 0 let G_n be the transpose of G_{|n|}. With N_k the
number of points of C over F_{q^k} and N_0 := 2 - 2g, the intersection numbers are

    F1.F1 = F2.F2 = 0,   F1.F2 = 1,
    G_n.F1 = 1,  G_n.F2 = q^n            (n >= 0; swapped for n < 0),
    G_a.G_b = q^min(|a|,|b|) N_|a-b|     (a, b of the same sign, or one of them 0),
    G_a.G_b = N_|a-b|                    (a, b of opposite signs).

(Derivation in NOTES.md section 2: projection formula for (Frob^b x 1)^* and
transversality of a horizontal and a vertical graph; self-reviewed.) The Hodge index
theorem on S says the Gram matrix of ANY finite family of classes has at most one
positive eigenvalue. Projecting the graphs off the hyperbolic plane <F1, F2> and
normalizing by q^(-|n|/2) turns the Gram matrix into minus the Toeplitz matrix
t_{a-b}, t_k = q^(-|k|/2) (q^|k| + 1 - N_|k|) = sum_i (alpha_i / sqrt q)^|k|, which is
the Weil explicit-formula form of the function field. So, on the Frobenius span,
Hodge index = Weil positivity = RH for C.

What the module computes
------------------------
* point counts N_n by brute force over F_{p^n} (no zeta function, no eigenvalues),
* the exact integer Gram matrix of {F1, F2, G_...} and its inertia, by two exact routes
  (characteristic polynomial with Descartes' rule, and symmetric elimination over Q),
* planted violations ("fake curves"): rational zeta functions with the curve's pole
  structure, the exact functional equation and an Euler product with nonnegative
  integer exponents, whose Frobenius eigenvalues lie off the circle |alpha| = sqrt(q),
* whether a fake also admits a quadratic-character Euler product over F_q(t),
* the number-field rival table: which of the geometric preconditions (proper
  intersections are nonnegative point counts; the trivial part is one hyperbolic
  plane) zeta, Davenport-Heilbronn, Epstein (1,1,6) and W_{1/4} satisfy.

Conventions: exact Python integers and fractions wherever a sign or an equality is
decided; numpy only for the vectorized field arithmetic (integers, no floats); mpmath
with explicit workdps for eigenvalue moduli and residues, no global mpmath state left
modified.
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from functools import lru_cache
from typing import Mapping, Sequence

import numpy as np
from mpmath import mp

# ---------------------------------------------------------------------------
# A. exact inertia of an integer symmetric matrix, two independent routes
# ---------------------------------------------------------------------------


def _sign_changes(coeffs: Sequence[int]) -> int:
    nz = [c for c in coeffs if c != 0]
    return sum(1 for u, v in zip(nz, nz[1:]) if (u > 0) != (v > 0))


def inertia_charpoly(mat: Sequence[Sequence[int]]) -> tuple[int, int, int]:
    """(n_plus, n_minus, n_zero) from the exact characteristic polynomial.

    The characteristic polynomial of a real symmetric matrix has only real roots, and
    for such a polynomial Descartes' rule of signs is exact: the number of positive
    roots equals the number of sign changes of its coefficients. Computed with
    python-flint's integer charpoly; no floating point anywhere.
    """
    import flint

    n = len(mat)
    if n == 0:
        return (0, 0, 0)
    cp = flint.fmpz_mat([[int(x) for x in row] for row in mat]).charpoly()
    coeffs = [int(c) for c in cp.coeffs()]  # ascending powers
    coeffs += [0] * (n + 1 - len(coeffs))
    z = 0
    while z <= n and coeffs[z] == 0:
        z += 1
    red = coeffs[z:]
    n_plus = _sign_changes(red)
    n_minus = _sign_changes([c * (-1) ** k for k, c in enumerate(red)])
    if n_plus + n_minus + z != n:  # pragma: no cover - would contradict real-rootedness
        raise ArithmeticError("Descartes count inconsistent: matrix not symmetric?")
    return (n_plus, n_minus, z)


def inertia_ldl(mat: Sequence[Sequence[int]]) -> tuple[int, int, int]:
    """(n_plus, n_minus, n_zero) by symmetric elimination over Q (Sylvester's law).

    A nonzero diagonal pivot d contributes sign(d); when the whole remaining diagonal is
    zero, a nonzero off-diagonal entry b gives the 2x2 pivot [[0, b], [b, 0]] of inertia
    (1, 1). Each step replaces the matrix by its Schur complement, a congruence, so the
    inertia is preserved exactly. Shares no code with :func:`inertia_charpoly`.
    """
    A = [[Fraction(int(x)) for x in row] for row in mat]
    n_plus = n_minus = n_zero = 0
    while A:
        k = len(A)
        piv = next((i for i in range(k) if A[i][i] != 0), None)
        if piv is not None:
            d = A[piv][piv]
            if d > 0:
                n_plus += 1
            else:
                n_minus += 1
            rest = [i for i in range(k) if i != piv]
            A = [[A[i][j] - A[i][piv] * A[piv][j] / d for j in rest] for i in rest]
            continue
        pair = next(
            ((i, j) for i in range(k) for j in range(i + 1, k) if A[i][j] != 0), None
        )
        if pair is None:
            n_zero += k
            break
        i, j = pair
        b = A[i][j]
        n_plus += 1
        n_minus += 1
        rest = [r for r in range(k) if r not in (i, j)]
        A = [
            [A[r][s] - (A[r][i] * A[j][s] + A[r][j] * A[i][s]) / b for s in rest]
            for r in rest
        ]
    return (n_plus, n_minus, n_zero)


def inertia(mat: Sequence[Sequence[int]]) -> tuple[int, int, int]:
    """Exact inertia; raises if the two exact routes disagree."""
    a = inertia_charpoly(mat)
    b = inertia_ldl(mat)
    if a != b:  # pragma: no cover - a disagreement is a bug in one of them
        raise ArithmeticError(f"inertia routes disagree: charpoly {a}, ldl {b}")
    return a


# ---------------------------------------------------------------------------
# B. F_{p^n} and brute-force point counts on y^2 = f(x)
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def irreducible_modulus(p: int, n: int) -> tuple[int, ...]:
    """Low coefficients (m_0, ..., m_{n-1}) of the lexicographically first monic
    irreducible m(t) = t^n + sum m_k t^k over F_p (sympy decides irreducibility; the
    field self-check in :class:`PrimePowerField` re-verifies it independently)."""
    if n == 1:
        return (0,)
    from sympy import Poly, symbols

    t = symbols("t")
    for low in itertools.product(range(p), repeat=n):
        if low[0] == 0:
            continue
        if Poly([1] + list(reversed(low)), t, modulus=p).is_irreducible:
            return tuple(low)
    raise RuntimeError(f"no irreducible polynomial of degree {n} over F_{p}")  # pragma: no cover


class PrimePowerField:
    """F_{p^n} = F_p[t]/(m(t)); elements are integer vectors (low degree first).

    ``elems`` lists all p^n elements, element i having base-p digits of i as its
    coefficients, so ``index`` inverts the listing. Arithmetic is vectorized over rows.
    """

    def __init__(self, p: int, n: int):
        self.p, self.n = int(p), int(n)
        self.low = np.array(irreducible_modulus(self.p, self.n), dtype=np.int64)
        self.size = self.p ** self.n
        idx = np.arange(self.size, dtype=np.int64)
        self.elems = np.stack([(idx // self.p ** k) % self.p for k in range(self.n)], axis=1)
        self._w = self.p ** np.arange(self.n, dtype=np.int64)

    def index(self, X: np.ndarray) -> np.ndarray:
        return (X % self.p) @ self._w

    def mul(self, A: np.ndarray, B: np.ndarray) -> np.ndarray:
        p, n = self.p, self.n
        if n == 1:
            return (A * B) % p
        C = np.zeros((A.shape[0], 2 * n - 1), dtype=np.int64)
        for i in range(n):
            C[:, i : i + n] += A[:, i : i + 1] * B
        C %= p
        for k in range(2 * n - 2, n - 1, -1):
            c = C[:, k]
            C[:, k - n : k] -= c[:, None] * self.low[None, :]
            C[:, k - n : k] %= p
        return C[:, :n] % p

    def is_field(self) -> bool:
        """Every nonzero x satisfies x^(p^n - 1) = 1 (false in any ring with zero
        divisors, so this independently confirms the modulus is irreducible)."""
        X = self.elems[1:]
        e = self.size - 1
        acc = np.zeros_like(X)
        acc[:, 0] = 1
        base = X.copy()
        while e:
            if e & 1:
                acc = self.mul(acc, base)
            base = self.mul(base, base)
            e >>= 1
        one = np.zeros_like(acc)
        one[:, 0] = 1
        return bool(np.array_equal(acc, one))


def _nmod_poly(f_desc: Sequence[int], p: int):
    import flint

    return flint.nmod_poly([int(c) % p for c in reversed(list(f_desc))], p)


def _check_curve_poly(f_desc: Sequence[int], p: int) -> int:
    """Validate y^2 = f(x) (f with integer coefficients, highest degree first): odd degree
    >= 3 mod p and squarefree mod p, so the projective model is smooth with one point at
    infinity. Returns the genus (deg f - 1) / 2."""
    f = _nmod_poly(f_desc, p)
    d = f.degree()
    if d < 3 or d % 2 == 0 or int(f_desc[0]) % p == 0:
        raise ValueError(f"need odd degree >= 3 with unit leading coefficient mod {p}")
    if f.gcd(f.derivative()).degree() != 0:
        raise ValueError(f"f is not squarefree mod {p}: the curve is singular")
    return (d - 1) // 2


def count_points(f_desc: Sequence[int], p: int, n: int, field: PrimePowerField | None = None) -> int:
    """#C(F_{p^n}) for the smooth projective model of y^2 = f(x), deg f odd.

    Literal enumeration: tabulate y -> y^2 over all of F_{p^n}, evaluate f at every x by
    Horner's rule, and add the one point at infinity. No character sums, zeta functions
    or eigenvalues are used.
    """
    _check_curve_poly(f_desc, p)
    F = field if field is not None else PrimePowerField(p, n)
    X = F.elems
    roots = np.bincount(F.index(F.mul(X, X)), minlength=F.size)
    acc = np.zeros_like(X)
    acc[:, 0] = int(f_desc[0]) % p
    for c in f_desc[1:]:
        acc = F.mul(acc, X)
        acc[:, 0] = (acc[:, 0] + int(c)) % p
    return int(roots[F.index(acc)].sum()) + 1


def point_counts(f_desc: Sequence[int], p: int, n_max: int) -> dict[int, int]:
    """{n: #C(F_{p^n})} for 1 <= n <= n_max, each by brute force."""
    return {n: count_points(f_desc, p, n) for n in range(1, n_max + 1)}


# ---------------------------------------------------------------------------
# C. the Weil polynomial from counts (an independent route to RH for C)
# ---------------------------------------------------------------------------


def power_sums_from_counts(q: int, counts: Mapping[int, int], n_max: int) -> list[int]:
    """[s_1, ..., s_n_max] with s_n = q^n + 1 - N_n = sum_i alpha_i^n."""
    return [q ** n + 1 - counts[n] for n in range(1, n_max + 1)]


def weil_polynomial(q: int, counts: Mapping[int, int], g: int) -> list[int]:
    """Ascending integer coefficients of P(T) = prod_i (1 - alpha_i T), degree 2g, from
    N_1..N_g by Newton's identities k c_k = -sum_{n<=k} s_n c_{k-n}, completed by the
    functional equation c_{2g-k} = q^(g-k) c_k. Raises if a coefficient is not integral
    (which would mean the counts are not those of a genus-g curve)."""
    s = power_sums_from_counts(q, counts, g)
    c = [Fraction(1)]
    for k in range(1, g + 1):
        c.append(-sum(Fraction(s[i - 1]) * c[k - i] for i in range(1, k + 1)) / k)
    for k in range(g + 1, 2 * g + 1):
        c.append(Fraction(q) ** (k - g) * c[2 * g - k])
    if any(x.denominator != 1 for x in c):
        raise ArithmeticError(f"non-integral Weil coefficients {c}")
    return [int(x) for x in c]


def counts_from_weil_polynomial(q: int, P: Sequence[int], n_max: int) -> dict[int, int]:
    """{n: q^n + 1 - s_n} with the power sums s_n of the inverse roots of P."""
    s: list[int] = []
    for n in range(1, n_max + 1):
        cn = P[n] if n < len(P) else 0
        val = -n * cn - sum(s[i - 1] * (P[n - i] if n - i < len(P) else 0) for i in range(1, n))
        s.append(val)
    return {n: q ** n + 1 - s[n - 1] for n in range(1, n_max + 1)}


def _roots_with_multiplicity(P: Sequence[int]) -> list:
    """Complex roots of the integer polynomial P (ascending coefficients), each listed
    with its multiplicity: P is first factored over Z (python-flint), so mpmath's
    polyroots only ever sees squarefree irreducible factors and converges."""
    import flint

    _, facs = flint.fmpz_poly([int(c) for c in P]).factor()
    roots = []
    for fac, mult in facs:
        cs = [int(c) for c in fac.coeffs()]
        if len(cs) == 2:
            rs = [mp.mpf(-cs[0]) / cs[1]]
        else:
            rs = mp.polyroots([mp.mpf(c) for c in reversed(cs)], maxsteps=500, extraprec=2 * mp.prec)
        roots.extend(rs * mult)
    return roots


def eigenvalue_moduli_ratio(q: int, P: Sequence[int], dps: int = 30) -> list:
    """[|alpha_i| / sqrt(q)] for the inverse roots alpha_i of P (mpmath, explicit dps)."""
    with mp.workdps(dps + 10):
        out = sorted(abs(1 / r) / mp.sqrt(q) for r in _roots_with_multiplicity(P))
    with mp.workdps(dps):
        return [+x for x in out]


# ---------------------------------------------------------------------------
# D. the intersection lattice of the Frobenius span on C x C
# ---------------------------------------------------------------------------


def _N(counts: Mapping[int, int], g: int, k: int) -> int:
    return 2 - 2 * g if k == 0 else int(counts[k])


def graph_dot(q: int, counts: Mapping[int, int], g: int, a: int, b: int) -> int:
    """G_a.G_b on C x C (exact integer)."""
    if a * b >= 0:
        return q ** min(abs(a), abs(b)) * _N(counts, g, abs(a - b))
    return _N(counts, g, abs(a - b))


def graph_dot_F1(q: int, n: int) -> int:
    return 1 if n >= 0 else q ** (-n)


def graph_dot_F2(q: int, n: int) -> int:
    return q ** n if n >= 0 else 1


def window_indices(window: int, symmetric: bool) -> list[int]:
    return list(range(-window, window + 1)) if symmetric else list(range(window))


def frobenius_gram(
    q: int, counts: Mapping[int, int], g: int, window: int, symmetric: bool = False
) -> list[list[int]]:
    """Exact Gram matrix of [F1, F2, G_n for n in the window].

    One-sided window m: G_0, ..., G_{m-1} (needs N_1..N_{m-1}). Symmetric window M:
    G_{-M}, ..., G_M (needs N_1..N_{2M}); the transposes test the second intersection
    formula against the first.
    """
    idx = window_indices(window, symmetric)
    size = 2 + len(idx)
    G = [[0] * size for _ in range(size)]
    G[0][1] = G[1][0] = 1
    for i, a in enumerate(idx):
        G[0][2 + i] = G[2 + i][0] = graph_dot_F1(q, a)
        G[1][2 + i] = G[2 + i][1] = graph_dot_F2(q, a)
        for j, b in enumerate(idx):
            G[2 + i][2 + j] = graph_dot(q, counts, g, a, b)
    return G


def projected_gram(
    q: int, counts: Mapping[int, int], g: int, window: int, symmetric: bool = False
) -> list[list[int]]:
    """Gram matrix of the graphs projected off <F1, F2>: D0 = D - (D.F2) F1 - (D.F1) F2,
    so D0.E0 = D.E - (D.F1)(E.F2) - (D.F2)(E.F1). Hodge index: this is <= 0."""
    idx = window_indices(window, symmetric)
    return [
        [
            graph_dot(q, counts, g, a, b)
            - graph_dot_F1(q, a) * graph_dot_F2(q, b)
            - graph_dot_F2(q, a) * graph_dot_F1(q, b)
            for b in idx
        ]
        for a in idx
    ]


def castelnuovo_severi_margins(q: int, counts: Mapping[int, int], g: int, n_max: int) -> list[int]:
    """[4 g^2 q^n - (q^n + 1 - N_n)^2 for n = 1..n_max]: the 2x2 minor of the projected
    form on {G_0, G_n}; nonnegative for every n is |N_n - q^n - 1| <= 2g q^(n/2)."""
    return [4 * g * g * q ** n - (q ** n + 1 - counts[n]) ** 2 for n in range(1, n_max + 1)]


def weil_toeplitz_symbols(q: int, counts: Mapping[int, int], g: int, k_max: int, dps: int = 30) -> list:
    """[t_0, ..., t_k_max] with t_k = q^(-k/2) (q^k + 1 - N_k), t_0 = 2g (mpmath)."""
    with mp.workdps(dps):
        return [mp.mpf(2 * g)] + [
            (mp.mpf(q) ** k + 1 - counts[k]) / mp.sqrt(q) ** k for k in range(1, k_max + 1)
        ]


def hodge_index_report(q: int, counts: Mapping[int, int], g: int, window: int, symmetric: bool = False) -> dict:
    """Inertia of the full Gram matrix and of the projected one (both exact)."""
    full = inertia(frobenius_gram(q, counts, g, window, symmetric))
    proj = inertia(projected_gram(q, counts, g, window, symmetric))
    return {
        "full_inertia": full,
        "projected_inertia": proj,
        "hodge_index_holds": full[0] == 1,
        "projected_rank": proj[0] + proj[1],
    }


# ---------------------------------------------------------------------------
# E. planted violations: fake curves with every arithmetic hypothesis but RH
# ---------------------------------------------------------------------------


def lucas_traces(q: int, a: int, n_max: int) -> list[int]:
    """[t_0, ..., t_n_max], t_n = alpha^n + beta^n for x^2 - a x + q."""
    t = [2, a]
    for _ in range(2, n_max + 1):
        t.append(a * t[-1] - q * t[-2])
    return t[: n_max + 1]


def fake_genus1_counts(q: int, a: int, n_max: int) -> dict[int, int]:
    """The 'point counts' N_n = q^n + 1 - t_n of Z(T) = (1 - aT + qT^2)/((1-T)(1-qT))."""
    t = lucas_traces(q, a, n_max)
    return {n: q ** n + 1 - t[n] for n in range(1, n_max + 1)}


def counts_from_polynomial(q: int, P: Sequence[int], n_max: int) -> dict[int, int]:
    """Point counts of Z(T) = P(T)/((1-T)(1-qT)) for any integer P with P(0) = 1."""
    return counts_from_weil_polynomial(q, P, n_max)


def is_self_reciprocal(q: int, P: Sequence[int]) -> bool:
    """The curve functional equation q^g T^(2g) P(1/(qT)) = P(T), i.e. c_{2g-k} = q^(g-k) c_k."""
    d = len(P) - 1
    if d % 2:
        return False
    g = d // 2
    return all(P[2 * g - k] == q ** (g - k) * P[k] for k in range(g + 1))


def poly_mul(A: Sequence[int], B: Sequence[int]) -> list[int]:
    out = [0] * (len(A) + len(B) - 1)
    for i, x in enumerate(A):
        for j, y in enumerate(B):
            out[i + j] += x * y
    return out


def _mobius(n: int) -> int:
    from sympy import factorint

    f = factorint(n)
    if any(e > 1 for e in f.values()):
        return 0
    return -1 if len(f) % 2 else 1


def _divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def closed_point_counts(counts: Mapping[int, int], d_max: int) -> list[int]:
    """[b_1, ..., b_d_max], b_d = (1/d) sum_{e|d} mu(d/e) N_e: the exponents in
    Z(T) = prod_d (1 - T^d)^(-b_d) (closed points of degree d for a real curve).
    Exact; raises if some b_d is not an integer."""
    out = []
    for d in range(1, d_max + 1):
        num = sum(_mobius(d // e) * counts[e] for e in _divisors(d))
        if num % d:
            raise ArithmeticError(f"b_{d} = {num}/{d} is not an integer")
        out.append(num // d)
    return out


def fake_genus1_threshold(q: int, a: int, d_cap: int = 200, dps: int = 50) -> int:
    """Smallest D0 >= 2 at which the tail inequality

        1 - rho^d - alpha^(-d) > k q^(1 - d/2) / (q - 1) + (d/2) q^(-d),

    rho = |alpha|/q, alpha the larger root of x^2 - |a| x + q, k = 1 for a > 0 and 3 for
    a < 0, holds. Both sides are monotone in d for d >= 2 (left increasing, right
    decreasing), so it then holds for every d >= D0, and NOTES.md section 4 shows that
    it implies b_d > 0. Requires 2 sqrt(q) < |a| < q + 1. The inequality is evaluated
    at 50 digits and accepted only with a margin above 1e-20."""
    if not (a * a > 4 * q and abs(a) < q + 1):
        raise ValueError("need 2 sqrt(q) < |a| < q + 1")
    k = 1 if a > 0 else 3
    with mp.workdps(dps):
        A = mp.mpf(abs(a))
        alpha = (A + mp.sqrt(A * A - 4 * q)) / 2
        rho = alpha / q
        for d in range(2, d_cap + 1):
            lhs = 1 - rho ** d - alpha ** (-d)
            rhs = k * mp.mpf(q) ** (1 - mp.mpf(d) / 2) / (q - 1) + mp.mpf(d) / 2 * mp.mpf(q) ** (-d)
            if lhs - rhs > mp.mpf(10) ** (-20):
                return d
    raise RuntimeError("threshold not reached")  # pragma: no cover


def max_inverse_root_modulus(P: Sequence[int], dps: int = 40):
    """max_i |alpha_i| over the inverse roots of P (mpmath)."""
    with mp.workdps(dps + 10):
        A = max(abs(1 / r) for r in _roots_with_multiplicity(P))
    with mp.workdps(dps):
        return +A


def fake_threshold_general(q: int, P: Sequence[int], d_cap: int = 400, dps: int = 50) -> int:
    """Tail threshold for b_d >= 0 for any P of degree 2g with A = max |alpha_i| < q.

    With N_e = q^e + 1 - s_e and |s_e| <= 2g A^e: d b_d >= N_d - sum_{e <= d/2} N_e
    (valid once every N_e >= 0) and the right side exceeds
    q^d - 2g A^d - q^(d/2+1)/(q-1) - d/2 - 2g A^(d/2+1)/(A-1), so b_d > 0 once
        1 - 2g (A/q)^d > q^(1-d/2)/(q-1) + (d/2) q^(-d) + 2g A^(d/2+1) q^(-d)/(A-1),
    a condition monotone in d. Also N_e >= q^e + 1 - 2g A^e > 0 past the same point.
    Returns the smallest d >= 2 where it holds (margin above 1e-20 at 50 digits)."""
    g = (len(P) - 1) // 2
    with mp.workdps(dps):
        A = max_inverse_root_modulus(P, dps)
        if not (1 < A < q):
            raise ValueError("need 1 < max |alpha| < q")
        Q = mp.mpf(q)
        for d in range(2, d_cap + 1):
            lhs = 1 - 2 * g * (A / Q) ** d
            rhs = (
                Q ** (1 - mp.mpf(d) / 2) / (Q - 1)
                + mp.mpf(d) / 2 * Q ** (-d)
                + 2 * g * A ** (mp.mpf(d) / 2 + 1) * Q ** (-d) / (A - 1)
            )
            if lhs - rhs > mp.mpf(10) ** (-20):
                return d
    raise RuntimeError("threshold not reached")  # pragma: no cover


def quadratic_tail_threshold(q: int, P: Sequence[int], r_max: int = 4, d_cap: int = 400, dps: int = 50) -> int:
    """Smallest D1 >= 2 past which the quadratic Euler decomposition has s_d, i_d >= 0
    whenever s_d is an integer. Sufficient: pi(d) - r_d >= |c_d| + pi(d/2), and with
    d pi(d) >= q^d - q^(d/2+1)/(q-1), d |c_d| <= 2g (A^d + A^(d/2+1)/(A-1)),
    pi(d/2) <= q^(d/2) + 1, it holds once
        1 - q^(1-d/2)/(q-1) - d r_max q^(-d)
            >= 2g ((A/q)^d + A^(d/2+1) q^(-d)/(A-1)) + d (q^(-d/2) + q^(-d)),
    which is monotone in d (NOTES.md section 5)."""
    g = (len(P) - 1) // 2
    with mp.workdps(dps):
        A = max_inverse_root_modulus(P, dps)
        if not (1 < A < q):
            raise ValueError("need 1 < max |alpha| < q")
        Q = mp.mpf(q)
        for d in range(2, d_cap + 1):
            D = mp.mpf(d)
            lhs = 1 - Q ** (1 - D / 2) / (Q - 1) - D * r_max * Q ** (-d)
            rhs = 2 * g * ((A / Q) ** d + A ** (D / 2 + 1) * Q ** (-d) / (A - 1)) + D * (
                Q ** (-D / 2) + Q ** (-d)
            )
            if lhs - rhs > mp.mpf(10) ** (-20):
                return d
    raise RuntimeError("threshold not reached")  # pragma: no cover


def mod2_reference_curve(P: Sequence[int], q: int, ram: Mapping[int, int]):
    """An honest elliptic curve y^2 = x^3 + c2 x^2 + c1 x + c0 over F_q whose L-function
    P_E = [1, -a_q, q] is congruent to P mod 2 and whose double cover y^2 = f(x) -> P^1
    has the ramification degrees ``ram``. By the mod-2 argument of NOTES.md section 5,
    the quadratic Euler decomposition of P is then integral in every degree.
    Returns (f_desc, P_E) or None."""
    want = {int(d): int(r) for d, r in ram.items() if r}
    for c2, c1, c0 in itertools.product(range(q), repeat=3):
        f = (1, c2, c1, c0)
        try:
            _check_curve_poly(f, q)
        except ValueError:
            continue
        if curve_ramification(f, q) != want:
            continue
        N1 = count_points(f, q, 1)
        PE = [1, -(q + 1 - N1), q]
        if all((x - y) % 2 == 0 for x, y in zip(PE, P)) and len(PE) == len(P):
            return f, PE
    return None


def split_inert_bruteforce(f_desc: Sequence[int], q: int, d: int) -> tuple[int, int, int]:
    """(split, inert, ramified) finite places of degree d for y^2 = f(x) -> P^1, counted
    directly: a place of degree d is the orbit of an x in F_{q^d} lying in no proper
    subfield, and it splits, is inert or ramifies as f(x) is a nonzero square, a
    nonsquare or zero in F_{q^d}. No L-function is used."""
    F = PrimePowerField(q, d)
    X = F.elems
    roots = np.bincount(F.index(F.mul(X, X)), minlength=F.size)

    def frob(Y, times):
        for _ in range(times):
            e, acc, base = q, None, Y.copy()
            while e:
                if e & 1:
                    acc = base.copy() if acc is None else F.mul(acc, base)
                base = F.mul(base, base)
                e >>= 1
            Y = acc
        return Y

    exact = np.ones(F.size, dtype=bool)
    for e in _divisors(d)[:-1]:
        exact &= ~np.all(frob(X, e) == X, axis=1)
    acc = np.zeros_like(X)
    acc[:, 0] = int(f_desc[0]) % q
    for c in f_desc[1:]:
        acc = F.mul(acc, X)
        acc[:, 0] = (acc[:, 0] + int(c)) % q
    nroots = roots[F.index(acc)][exact]
    split, inert, ram = int((nroots == 2).sum()), int((nroots == 0).sum()), int((nroots == 1).sum())
    assert split % d == 0 and inert % d == 0 and ram % d == 0
    return split // d, inert // d, ram // d


def places_of_degree(q: int, d: int) -> int:
    """Number of places of F_q(t) of degree d: monic irreducibles of degree d, plus the
    place at infinity when d = 1."""
    m = sum(_mobius(d // e) * q ** e for e in _divisors(d))
    assert m % d == 0
    return m // d + (1 if d == 1 else 0)


def euler_exponents(P: Sequence[int], d_max: int) -> list[int]:
    """[c_1, ..., c_d_max] with P(T) = prod_d (1 - T^d)^(-c_d) (integers for integral P
    with P(0) = 1). Uses L_n = n [T^n] log P from T P' = P (T P'/P)."""
    L: list[int] = []
    for n in range(1, d_max + 1):
        pn = P[n] if n < len(P) else 0
        L.append(n * pn - sum((P[k] if k < len(P) else 0) * L[n - k - 1] for k in range(1, n)))
    out = []
    for d in range(1, d_max + 1):
        num = sum(_mobius(d // e) * L[e - 1] for e in _divisors(d))
        if num % d:
            raise ArithmeticError(f"c_{d} not integral")  # pragma: no cover
        out.append(num // d)
    return out


def quadratic_euler_decomposition(P: Sequence[int], q: int, ram: Mapping[int, int], d_max: int) -> dict:
    """Try P(T) = prod over unramified places v of F_q(t) of (1 - chi(v) T^deg v)^(-1)
    with chi(v) in {+1, -1}, and ram[d] places of degree d where chi = 0.

    Only the number s_d of chi = +1 and i_d of chi = -1 places of each degree matters
    (all places of degree d have the same local factor shape), and comparing
    Z_{P^1} P = prod_d (1 - T^d)^(-(2 s_d + r_d)) (1 - T^(2d))^(-i_d) with
    prod_d (1 - T^d)^(-(pi_q(d) + c_d)) gives the recursion
        s_d = (pi_q(d) + c_d - r_d - i_{d/2}) / 2,   i_d = pi_q(d) - r_d - s_d.
    Returns the per-degree data and the first degree where s_d or i_d is not a
    nonnegative integer (None if there is none up to d_max). The conductor condition
    sum_d d r_d = deg P + 2 is reported, not enforced.
    """
    c = euler_exponents(P, d_max)
    s: dict[int, int] = {}
    i: dict[int, int] = {}
    failure = None
    for d in range(1, d_max + 1):
        pi = places_of_degree(q, d)
        r = int(ram.get(d, 0))
        half = i.get(d // 2, 0) if d % 2 == 0 else 0
        num = pi + c[d - 1] - r - half
        if num % 2:
            failure = (d, "parity")
            break
        sd = num // 2
        idd = pi - r - sd
        if sd < 0 or idd < 0:
            failure = (d, "sign")
            break
        s[d], i[d] = sd, idd
    return {
        "split": s,
        "inert": i,
        "failure": failure,
        "conductor": sum(d * r for d, r in ram.items()),
        "conductor_ok": sum(d * r for d, r in ram.items()) == len(P) - 1 + 2,
    }


def ramification_configurations(total: int) -> list[dict[int, int]]:
    """All {degree: count} with sum degree*count = total (partitions of total)."""
    out = []

    def rec(rem, maxpart, cur):
        if rem == 0:
            conf: dict[int, int] = {}
            for part in cur:
                conf[part] = conf.get(part, 0) + 1
            out.append(conf)
            return
        for part in range(min(rem, maxpart), 0, -1):
            rec(rem - part, part, cur + [part])

    rec(total, total, [])
    return out


def curve_ramification(f_desc: Sequence[int], p: int) -> dict[int, int]:
    """Ramification of the double cover y^2 = f(x) -> P^1 by degree: the irreducible
    factors of f mod p (by degree) and, for odd deg f, the place at infinity."""
    ram: dict[int, int] = {}
    _, facs = _nmod_poly(f_desc, p).factor()
    for fac, mult in facs:
        if mult != 1:
            raise ValueError("f not squarefree")
        d = fac.degree()
        ram[d] = ram.get(d, 0) + 1
    if (len(f_desc) - 1) % 2:
        ram[1] = ram.get(1, 0) + 1
    return ram


# ---------------------------------------------------------------------------
# F. the number-field rival table: geometric preconditions G1 and G2
# ---------------------------------------------------------------------------

#: Shift of the W_a rival, as in zeta.epstein (SHIFTED_PRODUCT_SHIFT = 1/4).
W_SHIFT = Fraction(1, 4)


def _is_prime_power(n: int) -> bool:
    from sympy import factorint

    return n > 1 and len(factorint(n)) == 1


def nf_log_derivative_profile(n_max: int = 60, dps: int = 30) -> dict[str, dict]:
    """G1 on the number-field side: for each function, Lambda_F(n) for n <= n_max read
    off its Dirichlet coefficients alone (zeta.epstein.log_derivative_coefficients), and
    the first n where Lambda_F(n) < 0 and the first non-prime-power n where
    Lambda_F(n) != 0. In the geometric dictionary Lambda_F(n) n^(-1/2) is the
    intersection number of two distinct scaling graphs at ratio n, which for effective
    curves meeting properly is a point count: nonnegative and carried by prime powers."""
    from zeta import epstein as E

    ifaces = {
        "zeta": E.zeta_interface(dps),
        "davenport_heilbronn": E.dh_interface(dps),
        "epstein_1_1_6": E.epstein_interface((1, 1, 6), dps),
        "shifted_product_quarter": E.shifted_interface(dps=dps),
    }
    tol = mp.mpf(10) ** (-(dps - 8))
    out = {}
    for name, iface in ifaces.items():
        lam = E.log_derivative_coefficients(iface["coefficient"], n_max, dps)
        first_neg = next((n for n in range(2, n_max + 1) if lam[n] < -tol), None)
        first_off = next(
            (n for n in range(2, n_max + 1) if not _is_prime_power(n) and abs(lam[n]) > tol), None
        )
        out[name] = {
            "first_negative": first_neg,
            "first_off_prime_power": first_off,
            "lam": [float(x) for x in lam],
        }
    return out


def nf_pole_residues(dps: int = 30) -> dict[str, list]:
    """G2 on the number-field side: residues eps * F(s0 + eps), eps = 1e-(dps//2), at the
    candidate poles in Re s > 1/2 (s0 = 1; for W_a also 1 +- a). Each simple pole s0
    adds the hyperbolic pair f^(s0 - 1/2) f^(1/2 - s0) to the trivial part of the Weil
    form, so the number of poles is the number of hyperbolic planes there."""
    from zeta import epstein as E

    out: dict[str, list] = {}
    with mp.workdps(dps + 10):
        eps = mp.mpf(10) ** (-(dps // 2))
        a = mp.mpf(W_SHIFT.numerator) / W_SHIFT.denominator
        out["zeta"] = [(1, eps * mp.zeta(1 + eps))]
        out["davenport_heilbronn"] = [(1, eps * E.dh_f(1 + eps, dps=dps + 10))]
        out["epstein_1_1_6"] = [(1, eps * E.epstein_zeta(1 + eps, (1, 1, 6), dps=dps + 10))]
        out["shifted_product_quarter"] = [
            (float(1 + a), eps * mp.zeta(1 + 2 * a + eps) * mp.zeta(1 + eps)),
            (float(1 - a), eps * mp.zeta(1 + eps) * mp.zeta(1 - 2 * a + eps)),
        ]
    with mp.workdps(dps):
        return {k: [(s0, +r) for s0, r in v] for k, v in out.items()}


def nf_rival_table(n_max: int = 60, dps: int = 30) -> dict[str, dict]:
    """The G1/G2 verdicts per function, with the numbers behind them."""
    lam = nf_log_derivative_profile(n_max, dps)
    res = nf_pole_residues(dps)
    table = {}
    with mp.workdps(dps):
        for name in lam:
            poles = [(s0, r) for s0, r in res[name] if abs(r) > mp.mpf(10) ** (-(dps // 3))]
            table[name] = {
                "G1_nonnegative_to_n_max": lam[name]["first_negative"] is None,
                "G1_prime_power_support_to_n_max": lam[name]["first_off_prime_power"] is None,
                "first_negative": lam[name]["first_negative"],
                "first_off_prime_power": lam[name]["first_off_prime_power"],
                "poles_right_of_half": len(poles),
                "residues": [(s0, float(r)) for s0, r in poles],
                "G2_one_hyperbolic_plane": len(poles) == 1,
            }
    return table
