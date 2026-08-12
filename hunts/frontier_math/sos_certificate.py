"""The joint obligation as a Gram-matrix inequality, and an SDP relaxation of it.

WHAT THIS MODULE IS ABOUT.  ``joint_universal.py`` reduced the whole
multi-pair verdict to one universally quantified statement,

    E[F_on + F_p]  >=  theta E[F_on] + (1-theta) n + 4k,     theta = 995/1000,

with ``E[G] = (1/A^2) int_{-1}^{1} c2(w) |G(w)|^2 dw``, ``c2`` the
autocorrelation of ``g(u) = cos(sqrt2 u) 1_{|u|<=1/2}``,
``A = int g = sqrt2 sin(1/sqrt2)``, ``F_on(w) = sum_j e^{i x_j w}`` and
``F_p(w) = sum_i 2 cosh(y_i w) e^{i t_i w}``.

The pair-only shadow of that statement --- ``E[F_p] >= 4k`` --- is a
kernel-checked theorem (``zeta23ext/Zeta23Ext/PairEnergy.lean``,
``pair_energy_ge``, zero ``sorry``).  Its proof is entirely matricial:
every exponential in ``F_p`` is an *atom* ``zeta = +/- y_i + i t_i``, the
energy is ``sum_{a,b} Q(a,b)^2`` for the Gram matrix
``Q(a,b) = Psi(zeta_a + conj zeta_b)/A``, ``Psi(z) = int g(u) e^{zu} du``,
and an inertia argument on that Gram matrix produces the ``4k``.

This module carries the SAME atoms-and-Gram language across the full
obligation --- on-line atoms included --- and asks what a semidefinite
relaxation of the resulting matrix inequality can and cannot see.

SECTION 1 (the matrix form, exact).  Put the on-line atoms
``zeta = i x_j`` and the pair atoms ``zeta = +/- y_i + i t_i`` into ONE
atom set of size ``N = n + 2k``, let ``sigma`` be the involution that
swaps the two atoms of each pair and FIXES every on-line atom, and let
``Q(a,b) = Psi(zeta_a + conj zeta_b)/A`` on that set.  Then (section 1 of
the code, :func:`target_from_Q`, :func:`matrix_form_defect`):

    E[F_on + F_p] - theta E[F_on] - (1-theta) n - 4k
        =  sum_{a,b in Pr} Q(a,b)^2                       (pair block)
         + 2 Re sum_{a in On, b in Pr} Q(a,b)^2           (cross block)
         + (1-theta) sum_{a != b in On} Q(a,b)^2          (on-line block)
         - 4k,

i.e. the obligation is ``Xi(Q) := sum_{a,b} c(a,b) Q(a,b)^2 - 4k >= 0``
with the block-constant real weights ``c = 1`` everywhere except the
on-line diagonal (``c = 0``) and the on-line off-diagonal
(``c = 1 - theta``).  Measured defect against ``joint_universal.
verdict_fourier_gap`` on mixed configurations: ~1e-11, quadrature-limited
(the reference side integrates ``c2`` on a grid; the matrix side is
closed-form, so the defect is the *reference*'s error).

The three summands are the three regimes: the pair block is what
``PairEnergy.lean`` bounds by ``4k``, the on-line block is
``(1-theta) R`` with ``R = sum_{j != l} (Phi2(x_j-x_l)/A)^2 >= 0``, and
the cross block is exactly ``-D``, the damage.  So all of the remaining
content is the cross block's sign.

SECTION 2 (what a real configuration forces on Q).  Five facts, each
derived where it is stated in the code:

  (Q1) ``Q`` is positive semidefinite --- Gram matrix of ``u |-> e^{zeta_a u}``
       against the nonnegative weight ``g`` (PairEnergy.lean,
       ``gram_posSemidef``);
  (Q2) ``Q(a, sigma a) = 1`` for EVERY atom, on-line ones included:
       ``zeta_a + conj zeta_{sigma a} = 0`` and ``Psi(0) = A``;
  (Q3) ``Q(sigma a, sigma b) = Q(b, a)``, from ``Psi`` even;
  (Q4) ``Q(a,a) = Psi(2 Re zeta_a)/A >= 1``, since
       ``Psi(s) = int g cosh(su) du >= int g = A`` (``g >= 0``); equality
       iff ``Re zeta_a = 0``, i.e. iff the atom is on-line;
  (Q5) ``|Q(a,b)| <= sqrt(Q(a,a) Q(b,b))`` --- implied by (Q1), listed
       because the lift uses it at the moment level where it is NOT
       implied.

(Q2) + (Q3) applied to two on-line atoms already force their block to be
real, which is the matrix shadow of ``Phi2`` being real on the reals.

SECTION 3 (the relaxation).  ``Xi`` is a quadratic form in the entries of
``Q`` and it is INDEFINITE (the cross block enters as
``Re Q^2 = (Re Q)^2 - (Im Q)^2``), so minimising it over the cone
(Q1)-(Q5) is not a convex program.  :func:`relax` builds the Shor lift:
the real coordinates ``p`` of ``Q`` (``X = Re Q`` symmetric, ``Y = Im Q``
antisymmetric, ``d = N^2`` of them), a moment matrix ``Z`` with
``[[1, p'],[p, Z]] >= 0``, the structural equalities of (Q2)-(Q3) plus
their localisations ``L Z = c p'`` (without those the lift forgets the
equalities), (Q1) and (Q4) at the first-moment level, (Q5) at the second-
moment level, and the Schur constraint ``M = Q o Q >= 0`` (Hadamard
square of a PSD matrix is PSD), which is linear in ``Z``.  ``Xi`` is
linear in ``Z``, so the minimum over the lift is a valid LOWER BOUND for
the minimum of ``Xi`` over every real configuration.

WHAT COMES OUT, in four findings; the numbers are in :data:`SDP_RECORD`,
:data:`CONE_RECORD` and :func:`audit`.

  (F1) The matrix form is exact: worst defect 2.55e-11 against
       ``verdict_fourier_gap`` over eight mixed configurations
       (n = 0..6, k = 0..4, depths 0.02..0.49), and the residual is the
       reference's quadrature error --- it falls as the grid is refined.

  (F2) THE CONE IS NOT ENOUGH, and by an unbounded amount.
       :func:`cone_violator` is an exactly rational Hermitian matrix
       satisfying (Q1)-(Q5) --- so, in particular, every hypothesis of
       ``PairEnergy.four_n_le_sum_sq`` with ``sigma`` allowed fixed
       points --- with ``Xi = (1-theta) n(n-1) + 2(1+2t^2)^2 - 2 - 4nt^2``,
       which is ``-47/100`` at ``n = 3, t = 1/2`` and tends to
       ``-infinity`` like ``-n^2/2``.  Its positive semidefiniteness is a
       two-line algebraic identity and is re-checked in
       :mod:`fractions` (:func:`cone_violator_exact`).  So NO argument
       from positive semidefiniteness, the involution and the diagonal
       bound alone can establish the obligation: the proof must use the
       analytic shape of ``Psi`` beyond ``g >= 0``.  The witness is not a
       configuration (relative fit residual 0.135), which is exactly the
       gap named above.

  (F3) The derived window ranges shrink the cone's deficit by ~50x and
       do NOT remove it (``CONE_RECORD["ranged"]``: -0.045 at (3,1),
       -0.134 at (6,1), -0.245 at (4,2), still growing with n and k).  A
       pointwise bound on single entries cannot close a joint
       obligation; what is missing is the trade-off between the on-line
       charge ``R`` and the damage ``D``, i.e. the fact that the on-line
       atoms cannot all sit at the damage minimum at once.

  (F4) The degree-2 (Shor) lift is loose one level further down: it
       returns ``-4k`` at ``n = 0``, i.e. it does not even reproduce the
       kernel-checked ``E[F_p] >= 4k`` beyond ``k = 1``, although the
       cone's own minimum there IS 0.  The diagnosis is exact: at
       ``n = 0, k = 2`` the lift's first moment is a genuine
       configuration with ``Xi = +7.18``, so the ``-8`` lives entirely
       in the moment matrix ``Z != p p'``.  The proof of the pair bound
       is an inertia argument --- a statement about how many positive
       eigenvalues ``perm(sigma)`` has --- and that is not a degree-2
       fact about the entries of ``Q``.

The one thing that DOES generalise size-independently is the inertia
bound itself, :func:`inertia_bound`: with ``sigma`` carrying ``n`` fixed
points, ``P = 2 perm(sigma)`` splits as ``V V^H - W W^H`` with ``n+k`` and
``k`` columns, and ``PairEnergy.trace_sq_ge`` applies verbatim to give

    sum_{a,b} Q(a,b)^2  >=  (n + 2k)^2 / (n + k),

which is ``4k`` at ``n = 0``.  Its multiplier is a fixed kernel
``h(a,b) = 2 [b = sigma a]`` with no size dependence at all --- and it
is short of the obligation by exactly ``nk/(n+k) + theta R``
(:func:`inertia_shortfall`), so a size-independent multiplier exists and
is not sufficient.

Nothing here computes a proportion and nothing here is evidence about RH.
No claim in this file is a proof of the universally quantified statement;
where a bound is a relaxation value it is labelled as one.

Run ``.venv/bin/python hunts/frontier_math/sos_certificate.py`` (~1.5 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import A, MEAN_GAP, phipap  # noqa: E402

#: the retention grid point the chain reports (joint_universal.THETA_FULL)
THETA_FULL = 0.995


# ---------------------------------------------------------------------------
# 1. atoms, Psi, and the Gram matrix Q
# ---------------------------------------------------------------------------


def Psi(z):
    """``Psi(z) = int_{-1/2}^{1/2} cos(sqrt2 u) e^{zu} du``, in closed form.

    ``phipap`` is the same transform along the imaginary direction:
    ``phipap(v) = int g(u) e^{i v u} du = Psi(i v)``, so ``Psi(z) =
    phipap(-i z)``.  Reusing ``phipap`` rather than re-deriving the closed
    form keeps this module on exactly the field ``paper_chain.py`` fixes.
    """
    return phipap(-1j * np.asarray(z, complex))


def atoms(online, pairs):
    """The combined atom set and its involution.

    Returns ``(zeta, sigma, kinds)``: ``zeta`` the complex exponents,
    ``sigma`` the involution index array, ``kinds`` an int array with 0
    for on-line atoms and 1 for pair atoms.

    An on-line ordinate ``x`` contributes ONE atom ``zeta = i x`` (its own
    involution partner, because ``i x + conj(i x) = 0``); a pair
    ``(t, y)`` contributes TWO, ``zeta = +/- y + i t``, which are each
    other's partners.  This is ``PairEnergy.zeta`` extended by the
    on-line atoms, and the extension is exactly where ``sigma`` stops
    being fixed-point free.
    """
    xs = [float(x) for x in online]
    ps = [(float(t), float(y)) for t, y in pairs]
    n = len(xs)
    zeta = [1j * x for x in xs]
    kinds = [0] * n
    sigma = list(range(n))
    for t, y in ps:
        a = len(zeta)
        zeta += [y + 1j * t, -y + 1j * t]
        kinds += [1, 1]
        sigma += [a + 1, a]
    return (np.array(zeta, complex), np.array(sigma, int),
            np.array(kinds, int))


def qmat(zeta) -> np.ndarray:
    """``Q(a,b) = Psi(zeta_a + conj zeta_b) / A`` --- ``PairEnergy.Qmat``
    on the combined atom set."""
    z = np.asarray(zeta, complex)
    return Psi(z[:, None] + np.conj(z)[None, :]) / A


def weight_matrix(kinds, theta: float) -> np.ndarray:
    """The block-constant weights ``c(a,b)`` of the matrix form.

    ``c = 1`` on the pair block and on both cross blocks, ``c = 1-theta``
    on the on-line off-diagonal, ``c = 0`` on the on-line diagonal.  The
    single line that produces them: the obligation is ``E[F_on+F_p] -
    theta E[F_on] - (1-theta) n - 4k`` and ``E[F_on]`` is the on-line
    block of ``sum Q^2`` whose diagonal is exactly ``n`` by (Q2)/(Q4).
    """
    k = np.asarray(kinds, int)
    on = (k == 0).astype(float)
    c = np.ones((len(k), len(k)))
    both_on = on[:, None] * on[None, :]
    c = c - theta * both_on
    np.fill_diagonal(c, np.where(k == 0, 0.0, 1.0))
    return c


def target_from_Q(Q, kinds, theta: float, k_pairs: int,
                  constant: float | None = None) -> float:
    """``Xi(Q) = sum_{a,b} c(a,b) Q(a,b)^2 - 4k``, the matrix form of the
    obligation.  The claim to be established is ``Xi >= 0`` for every Q
    arising from a real configuration.

    ``constant`` overrides the ``4k`` (used by the planted-infeasibility
    control, which raises it above the true optimum)."""
    Q = np.asarray(Q, complex)
    c = weight_matrix(kinds, theta)
    val = float(np.real((c * Q**2).sum()))
    return val - (4 * k_pairs if constant is None else constant)


def target_from_config(online, pairs, theta: float = THETA_FULL) -> float:
    """:func:`target_from_Q` straight from a configuration."""
    z, _, kinds = atoms(online, pairs)
    return target_from_Q(qmat(z), kinds, theta, len(list(pairs)))


def target_terms(online, pairs, theta: float = THETA_FULL) -> dict:
    """The three blocks of the matrix form separately.

    ``pair_block - 4k`` is the budget (nonnegative by PairEnergy.lean),
    ``cross_block`` is ``-D``, ``online_block`` is ``(1-theta) R``.
    """
    z, _, kinds = atoms(online, pairs)
    Q = qmat(z)
    on = kinds == 0
    pr = kinds == 1
    Q2 = Q**2
    pair_block = float(np.real(Q2[np.ix_(pr, pr)].sum()))
    cross = float(np.real(Q2[np.ix_(on, pr)].sum())) * 2
    onb = Q2[np.ix_(on, on)]
    online_block = (1 - theta) * float(np.real(onb.sum() - np.trace(onb)))
    k = len(list(pairs))
    return {"pair_block": pair_block, "budget": pair_block - 4 * k,
            "cross_block": cross, "online_block": online_block,
            "n": int(on.sum()), "k": k,
            "target": pair_block + cross + online_block - 4 * k}


# ---------------------------------------------------------------------------
# 1b. validation of the matrix form against the existing evaluators
# ---------------------------------------------------------------------------

#: six mixed configurations: varying n, k, depths and spacings.  Includes
#: the two extremes (no pairs, no on-line points) because those are the
#: two places where a block of the identity drops out and a sign error
#: would hide.
VALIDATION_CONFIGS = [
    ("n=1 k=1 deep", [0.7], [(0.0, 0.49)]),
    ("n=3 k=1 lattice", [0.0, MEAN_GAP, 2 * MEAN_GAP], [(3.1, 0.30)]),
    ("n=2 k=2 mixed depths", [-1.4, 2.6], [(0.0, 0.10), (5.5, 0.45)]),
    ("n=4 k=3 tight cluster", [0.0, 0.3, 0.9, 1.7],
     [(0.05, 0.49), (0.21, 0.49), (0.44, 0.02)]),
    ("n=5 k=2 sparse", [-12.0, -4.0, 0.0, 6.5, 15.2],
     [(-8.0, 0.25), (11.0, 0.40)]),
    ("n=0 k=2 pairs only", [], [(0.0, 0.49), (2.05 * MEAN_GAP, 0.49)]),
    ("n=3 k=0 on-line only", [0.0, 1.1, 7.9], []),
    ("n=6 k=4 dense", [0.0, 1.0, 2.0, 3.0, 4.0, 5.0],
     [(0.5, 0.49), (1.5, 0.31), (2.5, 0.17), (3.5, 0.05)]),
]


def matrix_form_defect(theta: float = THETA_FULL, n_quad: int = 400001):
    """The matrix form against ``joint_universal.verdict_fourier_gap``.

    Returns a list of records with both values and the absolute defect.
    The reference is quadrature over ``c2`` on a grid of ``n_quad``
    points; the matrix form is closed-form, so the residual is the
    reference's discretisation error and shrinks with ``n_quad``.
    """
    from joint_universal import verdict_fourier_gap  # local: heavy import
    out = []
    for name, online, pairs in VALIDATION_CONFIGS:
        mine = target_from_config(online, pairs, theta)
        if pairs:
            ref = verdict_fourier_gap(online, pairs, theta,
                                      n=n_quad)["fourier"]
        else:
            # verdict_fourier_gap needs a pair block; with no pairs the
            # obligation is (1-theta) R, computed from the same grid.
            from joint_universal import energy
            xs = np.array(list(online), float)

            def F_on(w):
                return np.exp(1j * xs[:, None] * w[None, :]).sum(axis=0)
            ref = (1 - theta) * (energy(F_on, n_quad) - len(xs))
        out.append({"name": name, "matrix": mine, "reference": ref,
                    "defect": abs(mine - ref)})
    return out


# ---------------------------------------------------------------------------
# 2. what a real configuration forces on Q (each fact derived at its site)
# ---------------------------------------------------------------------------

#: ``Psi(1)/A``: the largest a pair atom's diagonal can be when the depth
#: is in [0, 1/2].  DERIVED: ``Q(a,a) = Psi(2y)/A = int g cosh(2yu) du / A``
#: and ``|2yu| <= 1/2`` on the support, so ``Q(a,a) <= cosh(1/2)``; the
#: exact transform value below is sharper and is what the code uses.  It
#: is an OPTIONAL constraint (``depth_cap=True``) because PairEnergy.lean
#: establishes its bound for all real y, with no depth hypothesis at all.
DIAG_CAP = float(np.real(Psi(1.0))) / A

#: ``min_g Phi2(g)/A`` over real g: the smallest an on-line-block entry
#: can be.  DERIVED numerically from the closed form ``phipap`` on a fine
#: grid plus a golden-section refinement of the minimising g; it is a
#: measured constant, and is used only as an OPTIONAL constraint.
def _phi_min() -> float:
    gs = np.linspace(0.0, 60.0, 600001)
    v = np.real(phipap(gs)) / A
    i = int(np.argmin(v))
    lo, hi = gs[max(i - 1, 0)], gs[min(i + 1, len(gs) - 1)]
    for _ in range(200):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if float(np.real(phipap(m1))) < float(np.real(phipap(m2))):
            hi = m2
        else:
            lo = m1
    return float(np.real(phipap(0.5 * (lo + hi)))) / A


PHI_MIN = _phi_min()

#: ``psi(1/2) = Psi(1/2)/A``: the largest ``|Q(a,b)|`` can be when ``a`` is
#: on-line (``Re zeta_a = 0``) and ``b`` has depth ``y <= 1/2``.  DERIVED:
#: ``|Q(a,b)| = |int g(u) e^{(y)u} e^{i(x-t)u} du| / A <= Psi(y)/A`` and
#: ``Psi`` is increasing on ``[0, inf)``.  Sharper than Cauchy-Schwarz,
#: which gives ``sqrt(Psi(2y)/A)``: log-convexity of ``Psi`` (Cauchy-
#: Schwarz on ``int g e^{su/2} e^{tu/2}``) puts ``Psi(y)^2 <= A Psi(2y)``.
PSI_HALF = float(np.real(Psi(0.5))) / A

#: ``psi(1) = Psi(1)/A``, the same bound for two atoms of depth <= 1/2.
PSI_ONE = DIAG_CAP


def structural_facts(online, pairs, theta: float = THETA_FULL) -> dict:
    """Measure (Q1)-(Q5) on a real configuration, so that the constraint
    list of :func:`relax` is checked against the objects it claims to
    contain rather than asserted."""
    z, sig, kinds = atoms(online, pairs)
    Q = qmat(z)
    N = len(z)
    ev = np.linalg.eigvalsh((Q + Q.conj().T) / 2)
    diag = np.real(np.diag(Q))
    invol = np.array([Q[a, sig[a]] for a in range(N)])
    sym = max((abs(Q[sig[a], sig[b]] - Q[b, a])
               for a in range(N) for b in range(N)), default=0.0)
    cs = max((abs(Q[a, b]) - math.sqrt(diag[a] * diag[b])
              for a in range(N) for b in range(N)), default=-1.0)
    herm = float(np.abs(Q - Q.conj().T).max()) if N else 0.0
    on = kinds == 0
    return {
        "N": N,
        "Q1_min_eig": float(ev.min()) if N else 0.0,
        "Q1_hermitian_defect": herm,
        "Q2_involution_defect": float(np.abs(invol - 1).max()) if N else 0.0,
        "Q3_symmetry_defect": float(sym),
        "Q4_min_diag": float(diag.min()) if N else 1.0,
        "Q4_online_diag_defect": (float(np.abs(diag[on] - 1).max())
                                  if on.any() else 0.0),
        "Q5_worst_cauchy_schwarz": float(cs),
        "online_block_imag": (float(np.abs(np.imag(Q[np.ix_(on, on)])).max())
                              if on.any() else 0.0),
        "max_pair_diag": float(diag.max()) if N else 1.0,
        "diag_cap": DIAG_CAP,
    }


# ---------------------------------------------------------------------------
# 3. the Shor lift of the matrix obligation
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LiftIndex:
    """Real coordinates of a Hermitian ``N x N`` matrix, and the atom
    combinatorics of a size-``(n, k)`` configuration.

    ``X = Re Q`` is symmetric and ``Y = Im Q`` antisymmetric, so the free
    real coordinates are ``X[a,b]`` for ``a <= b`` and ``Y[a,b]`` for
    ``a < b`` --- ``d = N^2`` of them.  ``ix`` and ``iy`` map an index
    pair to its coordinate; ``sy`` carries the sign that antisymmetry
    puts on ``Y[b,a]``.
    """

    n: int
    k: int
    N: int
    d: int
    sigma: np.ndarray
    kinds: np.ndarray
    ix: np.ndarray
    iy: np.ndarray
    sy: np.ndarray


def lift_index(n: int, k: int) -> LiftIndex:
    N = n + 2 * k
    sigma = np.arange(N)
    kinds = np.zeros(N, int)
    for i in range(k):
        a = n + 2 * i
        sigma[a], sigma[a + 1] = a + 1, a
        kinds[a] = kinds[a + 1] = 1
    ix = np.zeros((N, N), int)
    iy = np.zeros((N, N), int)
    sy = np.zeros((N, N))
    c = 0
    for a in range(N):
        for b in range(a, N):
            ix[a, b] = ix[b, a] = c
            c += 1
    for a in range(N):
        for b in range(a + 1, N):
            iy[a, b] = iy[b, a] = c
            sy[a, b], sy[b, a] = 1.0, -1.0
            c += 1
    return LiftIndex(n=n, k=k, N=N, d=c, sigma=sigma, kinds=kinds,
                     ix=ix, iy=iy, sy=sy)


def structural_equalities(L: LiftIndex):
    """The linear equalities (Q2) and (Q3) on the real coordinates.

    (Q2) ``Q(a, sigma a) = 1``: ``X[a, sigma a] = 1`` and, when
    ``sigma a != a``, ``Y[a, sigma a] = 0``.  For an on-line atom
    ``sigma a = a`` and the statement is ``X[a,a] = 1`` --- the diagonal
    of the on-line block is pinned, which is where the ``(1-theta) n`` of
    the obligation comes from.

    (Q3) ``Q(sigma a, sigma b) = Q(b,a)``: ``X[sigma a, sigma b] = X[a,b]``
    and ``Y[sigma a, sigma b] = -Y[a,b]``.  Applied to two on-line atoms
    (``sigma`` fixes both) it reads ``Y[a,b] = -Y[a,b]``, i.e. the on-line
    block is real; that is not an extra assumption, it is (Q3).

    Returns ``(Lmat, rhs)`` with ``Lmat @ p == rhs``, duplicate rows
    removed.
    """
    rows, rhs, seen = [], [], set()

    def add(coeffs, val):
        key = (tuple(sorted(coeffs.items())), val)
        if key in seen:
            return
        seen.add(key)
        r = np.zeros(L.d)
        for j, w in coeffs.items():
            r[j] += w
        rows.append(r)
        rhs.append(val)

    for a in range(L.N):
        s = int(L.sigma[a])
        add({L.ix[a, s]: 1.0}, 1.0)
        if s != a:
            add({L.iy[a, s]: L.sy[a, s]}, 0.0)
    for a in range(L.N):
        for b in range(L.N):
            sa, sb = int(L.sigma[a]), int(L.sigma[b])
            c1 = {}
            c1[L.ix[sa, sb]] = c1.get(L.ix[sa, sb], 0.0) + 1.0
            c1[L.ix[a, b]] = c1.get(L.ix[a, b], 0.0) - 1.0
            if any(abs(v) > 0 for v in c1.values()):
                add(c1, 0.0)
            if sa != sb and a != b:
                c2 = {}
                c2[L.iy[sa, sb]] = c2.get(L.iy[sa, sb], 0.0) + L.sy[sa, sb]
                c2[L.iy[a, b]] = c2.get(L.iy[a, b], 0.0) + L.sy[a, b]
                if any(abs(v) > 1e-12 for v in c2.values()):
                    add(c2, 0.0)
            elif sa == sb and a != b:
                add({L.iy[a, b]: L.sy[a, b]}, 0.0)
    if not rows:
        return np.zeros((0, L.d)), np.zeros(0)
    return np.array(rows), np.array(rhs)


def objective_coefficients(L: LiftIndex, theta: float):
    """``Xi + 4k = sum_{a,b} c(a,b) (X[a,b]^2 - Y[a,b]^2)`` as coefficients
    on the second-moment coordinates.

    ``Re(Q^2) = X^2 - Y^2`` entrywise, and the imaginary parts cancel in
    the double sum because ``X`` is symmetric and ``Y`` antisymmetric, so
    the whole objective is real and quadratic in ``p``.
    """
    c = weight_matrix(L.kinds, theta)
    idx_i, idx_j, w = [], [], []
    for a in range(L.N):
        idx_i.append(L.ix[a, a]); idx_j.append(L.ix[a, a]); w.append(c[a, a])
        for b in range(a + 1, L.N):
            idx_i.append(L.ix[a, b]); idx_j.append(L.ix[a, b])
            w.append(2 * c[a, b])
            idx_i.append(L.iy[a, b]); idx_j.append(L.iy[a, b])
            w.append(-2 * c[a, b])
    return np.array(idx_i), np.array(idx_j), np.array(w)


def relax(n: int, k: int, theta: float = THETA_FULL, constant=None,
          depth_cap: bool = False, phi_range: bool = False,
          cross_cap: bool = False,
          schur: bool = True, cauchy_schwarz: bool = True,
          shor: bool = True, solver: str = "CLARABEL", verbose: bool = False,
          **solver_opts) -> dict:
    """Minimise ``Xi`` over the Shor lift of the cone (Q1)-(Q5).

    Every constraint is derived in :func:`structural_equalities` or in the
    comment at its own line; none is a margin and none is fitted.  The
    value returned is a LOWER BOUND for ``min Xi`` over real
    configurations of that size, because every real configuration
    produces a feasible point (``p`` its own coordinates, ``Z = p p'``).

    ``constant`` replaces the ``4k`` of the obligation; the planted-
    infeasibility control raises it above the true optimum and checks
    that the relaxation goes negative.  ``depth_cap`` and ``phi_range``
    switch on the two optional entry ranges (derived at
    :data:`DIAG_CAP` / :data:`PHI_MIN`); they need a depth hypothesis
    ``y in [0, 1/2]`` that PairEnergy.lean does not need, so they are off
    by default.
    """
    import cvxpy as cp

    L = lift_index(n, k)
    const = 4 * k if constant is None else float(constant)
    Lmat, rhs = structural_equalities(L)
    p = cp.Variable(L.d, name="p")
    cons = []

    # -- first-moment level: Q itself ---------------------------------------
    Xe = cp.reshape(p[L.ix.reshape(-1)], (L.N, L.N), order="C")
    Ye = cp.multiply(L.sy, cp.reshape(p[L.iy.reshape(-1)], (L.N, L.N),
                                      order="C"))
    if L.N:
        # (Q1) Q >= 0, as the real 2N x 2N embedding of a Hermitian matrix
        cons.append(cp.bmat([[Xe, -Ye], [Ye, Xe]]) >> 0)
    if len(rhs):
        cons.append(Lmat @ p == rhs)                       # (Q2), (Q3)
    diag_idx = np.array([L.ix[a, a] for a in range(L.N)], int)
    if L.N:
        cons.append(p[diag_idx] >= 1.0)                    # (Q4)
        if depth_cap:
            cons.append(p[diag_idx] <= DIAG_CAP)           # optional (Q4')
        if phi_range:
            on = np.flatnonzero(L.kinds == 0)
            rr = [L.ix[a, b] for i, a in enumerate(on) for b in on[i + 1:]]
            if rr:
                cons.append(p[np.array(rr, int)] >= PHI_MIN)  # optional
        if cross_cap:
            # optional (Q6): |Q(a,b)| <= Psi(Re zeta_a + Re zeta_b)/A, at
            # the depth hypothesis y in [0, 1/2].  Second-order cone.
            for a in range(L.N):
                for b in range(a + 1, L.N):
                    cap = (1.0 if L.kinds[a] == 0 and L.kinds[b] == 0
                           else PSI_HALF if L.kinds[a] != L.kinds[b]
                           else PSI_ONE)
                    cons.append(cp.norm(cp.hstack([p[L.ix[a, b]],
                                                   p[L.iy[a, b]]])) <= cap)
    if not shor:
        # no lift: the objective is nonconvex, so this branch only exists
        # to expose the cone itself (used by the realizability probe).
        return {"n": n, "k": k, "theta": theta, "index": L,
                "constraints": cons, "p": p}

    # -- second-moment level ------------------------------------------------
    Z = cp.Variable((L.d, L.d), symmetric=True, name="Z")
    cons.append(cp.bmat([[np.ones((1, 1)), cp.reshape(p, (1, L.d), order="C")],
                         [cp.reshape(p, (L.d, 1), order="C"), Z]]) >> 0)
    if len(rhs):
        # localisation: (L p - rhs) p' = 0.  Without this the lift keeps
        # the equalities only in the first moment and forgets them in Z.
        cons.append(Lmat @ Z == np.array(rhs).reshape(-1, 1)
                    @ cp.reshape(p, (1, L.d), order="C"))
    if cauchy_schwarz:
        # (Q5) at the moment level: |Q(a,b)|^2 <= Q(a,a) Q(b,b) is
        # X^2 + Y^2 <= X_aa X_bb, all four terms second moments.
        ii, jj, kk = [], [], []
        for a in range(L.N):
            for b in range(a + 1, L.N):
                ii.append(L.ix[a, b]); jj.append(L.iy[a, b])
                kk.append((L.ix[a, a], L.ix[b, b]))
        if ii:
            ii = np.array(ii); jj = np.array(jj)
            ka = np.array([q[0] for q in kk]); kb = np.array([q[1] for q in kk])
            cons.append(Z[ii, ii] + Z[jj, jj] <= Z[ka, kb])
    if schur and L.N:
        # Schur product theorem: Q >= 0 implies M = Q o Q >= 0, and M is
        # linear in Z (M(a,b) = Q(a,b)^2 = X^2 - Y^2 + 2i X Y).
        xi = np.array([[L.ix[a, b] for b in range(L.N)] for a in range(L.N)])
        yi = np.array([[L.iy[a, b] if a != b else L.ix[a, a]
                        for b in range(L.N)] for a in range(L.N)])
        off = np.array([[0.0 if a == b else 1.0 for b in range(L.N)]
                        for a in range(L.N)])
        ms = np.array([[0.0 if a == b else 2 * L.sy[a, b]
                        for b in range(L.N)] for a in range(L.N)])
        ReM = (cp.reshape(Z[xi.reshape(-1), xi.reshape(-1)], (L.N, L.N),
                          order="C")
               - cp.multiply(off, cp.reshape(Z[yi.reshape(-1), yi.reshape(-1)],
                                             (L.N, L.N), order="C")))
        ImM = cp.multiply(
            ms, cp.reshape(Z[xi.reshape(-1), yi.reshape(-1)], (L.N, L.N),
                           order="C"))
        cons.append(cp.bmat([[ReM, -ImM], [ImM, ReM]]) >> 0)

    oi, oj, ow = objective_coefficients(L, theta)
    obj = Z[oi, oj] @ ow - const
    prob = cp.Problem(cp.Minimize(obj), cons)
    opts = dict(solver_opts)
    prob.solve(solver=solver, verbose=verbose, **opts)
    rec = {"n": n, "k": k, "N": L.N, "d": L.d, "theta": theta,
           "constant": const, "status": prob.status,
           "value": (float(prob.value) if prob.value is not None else None),
           "solver": solver, "index": L, "problem": prob,
           "constraints": cons, "p": p, "Z": Z}
    if p.value is not None:
        rec["Q"] = q_from_p(L, np.asarray(p.value, float))
    return rec


def q_from_p(L: LiftIndex, pv: np.ndarray) -> np.ndarray:
    """The Hermitian matrix encoded by the real coordinate vector."""
    X = pv[L.ix]
    Y = L.sy * pv[L.iy]
    return X + 1j * Y


# ---------------------------------------------------------------------------
# 4. the inertia bound on the COMBINED atom set
# ---------------------------------------------------------------------------


def inertia_bound(n: int, k: int) -> float:
    """``sum_{a,b} Q(a,b)^2 >= (n+2k)^2 / (n+k)`` --- ``PairEnergy.
    four_n_le_sum_sq`` carried to the combined atom set.

    THE DERIVATION, in the notation of ``PairEnergy.lean``.  Let
    ``P = 2 * perm(sigma)`` on the ``N = n+2k`` atoms.  Then, exactly as
    in that file, ``tr (Q P) = 2 sum_a Q(a, sigma a) = 2N`` by (Q2) and
    ``tr ((QP)^2) = 4 sum_{a,b} Q(a,b)^2`` by (Q3).  The only thing that
    changes is the inertia of ``P``: a 2-cycle of ``sigma`` contributes
    eigenvalues ``+2`` and ``-2``, and a FIXED point (an on-line atom)
    contributes ``+2`` only, so ``P = V V^H - W W^H`` with ``V`` carrying
    ``n + k`` columns and ``W`` carrying ``k``.  ``trace_sq_ge`` then
    gives ``(2N)^2 <= (n+k) * 4 sum Q^2``, i.e. the bound above.

    At ``n = 0`` this is ``4k^2/k = 4k``: the theorem of PairEnergy.lean,
    recovered exactly.  The Lean lemma ``trace_sq_ge`` is stated for
    arbitrary ``V``, ``W`` and is reused verbatim; only the construction
    of ``V``, ``W`` (``hP``) has to be redone for a ``sigma`` with fixed
    points.  Nothing in this module compiles that, so this is a derived
    statement checked numerically here (:func:`inertia_defect`), not a
    kernel-checked one.
    """
    if n + k == 0:
        return 0.0
    return (n + 2 * k) ** 2 / (n + k)


def inertia_defect(online, pairs) -> dict:
    """``sum Q^2 - (n+2k)^2/(n+k)`` on a real configuration (must be
    ``>= 0``), plus the two traces the derivation uses."""
    z, sig, kinds = atoms(online, pairs)
    Q = qmat(z)
    N = len(z)
    n = int((kinds == 0).sum())
    k = (N - n) // 2
    P = np.zeros((N, N))
    for a in range(N):
        P[a, sig[a]] = 2.0
    QP = Q @ P
    return {"n": n, "k": k, "sum_sq": float(np.real((Q**2).sum())),
            "bound": inertia_bound(n, k),
            "slack": float(np.real((Q**2).sum())) - inertia_bound(n, k),
            "tr_QP": float(np.real(np.trace(QP))),
            "tr_QP_sq": float(np.real(np.trace(QP @ QP))),
            "tr_identity_defect": abs(float(np.real(np.trace(QP @ QP)))
                                      - 4 * float(np.real((Q**2).sum())))}


def inertia_shortfall(n: int, k: int, R: float, theta: float = THETA_FULL):
    """What the inertia bound leaves on the table.

    ``Xi = sum_all Q^2 - theta (n+R) - (1-theta) n - 4k``, so the inertia
    bound gives ``Xi >= (n+2k)^2/(n+k) - n - 4k - theta R
    = -nk/(n+k) - theta R``, since ``(n+2k)^2 - (n+4k)(n+k) = -nk``.
    The bound therefore NEVER closes the obligation on its own: it is
    short by exactly ``nk/(n+k) + theta R``, and that quantity is the
    precise amount the cross block has to supply.
    """
    return {"n": n, "k": k, "R": R, "theta": theta,
            "inertia": inertia_bound(n, k),
            "needed": n + 4 * k + theta * R,
            "shortfall": (n * k / (n + k) if n + k else 0.0) + theta * R}


# ---------------------------------------------------------------------------
# 5. the cone itself: a local minimiser of Xi over (Q1)-(Q4)
# ---------------------------------------------------------------------------


def cone_local_min(n: int, k: int, theta: float = THETA_FULL, iters: int = 60,
                   seed: int = 0, start=None, solver: str = "CLARABEL",
                   fallback: str = "SCS", **cone_opts) -> dict:
    """Local minimisation of ``Xi`` over the cone (Q1)-(Q4) --- an UPPER
    bound for the cone's minimum, to bracket the relaxation's lower one.

    ``Xi = sum c(a,b) X(a,b)^2 - sum c(a,b) Y(a,b)^2`` with ``c >= 0``, so
    it is a difference of two convex quadratics: a DC program.  Each step
    linearises the ``Y`` part at the current point and solves the
    resulting convex problem over the same cone, which is the standard
    convex-concave procedure; the value decreases monotonically and the
    limit is a stationary point, not a global minimum.  Several seeds are
    the only defence against that and the seeds are reported.
    """
    import cvxpy as cp

    L = lift_index(n, k)
    c = weight_matrix(L.kinds, theta)
    base = relax(n, k, theta, shor=False, **cone_opts)
    p, cons = base["p"], base["constraints"]
    xi, xw, yi, yw = [], [], [], []
    for a in range(L.N):
        xi.append(L.ix[a, a]); xw.append(c[a, a])
        for b in range(a + 1, L.N):
            xi.append(L.ix[a, b]); xw.append(2 * c[a, b])
            yi.append(L.iy[a, b]); yw.append(2 * c[a, b])
    xi, xw = np.array(xi, int), np.array(xw)
    yi, yw = np.array(yi, int), np.array(yw)
    rng = np.random.default_rng(seed)
    yv = (rng.normal(0.0, 0.3, len(yi)) if start is None
          else np.asarray(start, float))
    best, bestp, hist = math.inf, None, []
    for _ in range(iters):
        obj = (cp.sum(cp.multiply(xw, cp.square(p[xi])))
               - 2 * ((yw * yv) @ p[yi]) + float((yw * yv * yv).sum())
               - 4 * k) if len(yi) else (
            cp.sum(cp.multiply(xw, cp.square(p[xi]))) - 4 * k)
        prob = cp.Problem(cp.Minimize(obj), cons)
        try:
            prob.solve(solver=solver)
        except Exception:
            try:
                prob.solve(solver=fallback)
            except Exception:
                break
        if p.value is None:
            break
        pv = np.asarray(p.value, float)
        yn = pv[yi] if len(yi) else yv
        val = float((xw * pv[xi] ** 2).sum()
                    - (yw * yn ** 2).sum()) - 4 * k
        hist.append(val)
        if val < best - 1e-12:
            best, bestp = val, pv.copy()
        if len(yi) and np.linalg.norm(yn - yv) < 1e-9:
            break
        yv = yn
    return {"n": n, "k": k, "theta": theta, "seed": seed, "value": best,
            "history": hist,
            "Q": (q_from_p(L, bestp) if bestp is not None else None)}


def cone_scan(sizes, theta: float = THETA_FULL, seeds: int = 6,
              **cone_opts) -> list:
    """:func:`cone_local_min` over several sizes and seeds."""
    out = []
    for n, k in sizes:
        vals = []
        Qs = None
        for s in range(seeds):
            rec = cone_local_min(n, k, theta, seed=s, **cone_opts)
            if math.isfinite(rec["value"]):
                vals.append(rec["value"])
                if rec["value"] == min(vals):
                    Qs = rec["Q"]
        out.append({"n": n, "k": k, "best": (min(vals) if vals else None),
                    "values": sorted(vals), "Q": Qs})
    return out


# ---------------------------------------------------------------------------
# 6. the exact cone violator: the cone (Q1)-(Q5) does not imply the target
# ---------------------------------------------------------------------------


def cone_violator(n: int, t: Fraction = Fraction(1, 2)):
    """An EXACT Gram matrix satisfying (Q1)-(Q5) at which ``Xi < 0``.

    Read off :func:`cone_local_min`'s minimiser at ``n = 3, k = 1`` (which
    came out on rational coordinates) and then generalised in ``n`` and in
    one parameter ``t``.  With ``d = 1 + 2 t^2`` and atoms ordered
    ``0..n-1`` on-line, ``n`` and ``n+1`` the two atoms of the single
    pair:

        Q(a,b)     = 1        (a, b < n)
        Q(a, n)    = i t,   Q(a, n+1) = -i t        (a < n)
        Q(n,n)     = Q(n+1,n+1) = d,   Q(n, n+1) = 1

    (Q2): the on-line diagonal is 1 and ``Q(n,n+1) = 1``.  (Q3): with
    ``sigma`` fixing ``a < n`` and swapping ``n, n+1``, every relation is
    an entry-for-entry check.  (Q4): ``d >= 1``.  (Q5): ``t^2 <= d``.
    (Q1) is the two-line computation

        x^H Q x = |S|^2 + 2 Re(conj(S) w) + d(|u|^2+|v|^2) + 2 Re(conj(u) v)
                >= -|w|^2 + d(|u|^2+|v|^2) + 2 Re(conj(u) v)
                >= (d - t^2 - 1 - t^2)(|u|^2 + |v|^2)  =  0,

    with ``S = sum_a x_a``, ``w = i t (u - v)`` and ``|w|^2 = t^2 |u-v|^2
    = t^2(|u|^2+|v|^2-2Re(conj(u) v))``; the last step is ``d = 1 + 2t^2``.
    So the matrix is positive semidefinite for EVERY ``t``.

    Its target value is exactly

        Xi = (1-theta) n(n-1) + 2 d^2 - 2 - 4 n t^2,

    which at ``t = 1/2`` is ``(1-theta) n (n-1) + 5/2 - n`` --- negative
    from ``n = 3`` on --- and, optimising ``t`` at ``t^2 = (n-2)/4``,
    reaches ``(1-theta) n(n-1) - n^2/2 + 2n - 2 -> -infinity``.

    Returns ``(ReQ, ImQ)`` as nested lists of :class:`fractions.Fraction`.
    """
    t = Fraction(t)
    d = 1 + 2 * t * t
    N = n + 2
    re = [[Fraction(0) for _ in range(N)] for _ in range(N)]
    im = [[Fraction(0) for _ in range(N)] for _ in range(N)]
    for a in range(n):
        for b in range(n):
            re[a][b] = Fraction(1)
    for a in range(n):
        im[a][n], im[n][a] = t, -t
        im[a][n + 1], im[n + 1][a] = -t, t
    re[n][n] = re[n + 1][n + 1] = d
    re[n][n + 1] = re[n + 1][n] = Fraction(1)
    return re, im


def _psd_exact(M) -> bool:
    """Exact PSD test for a rational symmetric matrix, by LDL' without
    pivoting: a nonpositive pivot fails unless the pivot is zero AND its
    whole remaining row is zero, which is what a PSD matrix forces."""
    M = [row[:] for row in M]
    N = len(M)
    for i in range(N):
        if M[i][i] < 0:
            return False
        if M[i][i] == 0:
            if any(M[i][j] != 0 for j in range(i, N)):
                return False
            continue
        for r in range(i + 1, N):
            f = M[r][i] / M[i][i]
            if f == 0:
                continue
            for c in range(i, N):
                M[r][c] -= f * M[i][c]
    return True


def cone_violator_exact(n: int, t: Fraction = Fraction(1, 2),
                        theta: Fraction = Fraction(995, 1000)) -> dict:
    """Re-check :func:`cone_violator` in exact rational arithmetic.

    Everything below is finite arithmetic on :class:`fractions.Fraction`:
    the involution and symmetry relations, the diagonal bound, the
    Cauchy-Schwarz bound, positive semidefiniteness (via the real
    ``2N x 2N`` embedding, which is PSD exactly when the Hermitian matrix
    is), and the value of ``Xi``.  This is the form a theorem prover can
    replay --- it asserts that the hypotheses of ``PairEnergy.
    four_n_le_sum_sq``, extended to an involution WITH fixed points, do
    not imply the target inequality.
    """
    re, im = cone_violator(n, t)
    N = n + 2
    sigma = list(range(n)) + [n + 1, n]
    kinds = [0] * n + [1, 1]
    herm = all(re[a][b] == re[b][a] and im[a][b] == -im[b][a]
               for a in range(N) for b in range(N))
    invol = all(re[a][sigma[a]] == 1 and im[a][sigma[a]] == 0
                for a in range(N))
    sym = all(re[sigma[a]][sigma[b]] == re[b][a]
              and im[sigma[a]][sigma[b]] == im[b][a]
              for a in range(N) for b in range(N))
    diag = all(re[a][a] >= 1 for a in range(N))
    cs = all((re[a][b] ** 2 + im[a][b] ** 2) <= re[a][a] * re[b][b]
             for a in range(N) for b in range(N))
    emb = [[Fraction(0)] * (2 * N) for _ in range(2 * N)]
    for a in range(N):
        for b in range(N):
            emb[a][b] = re[a][b]
            emb[a][N + b] = -im[a][b]
            emb[N + a][b] = im[a][b]
            emb[N + a][N + b] = re[a][b]
    psd = _psd_exact(emb)
    theta = Fraction(theta)
    xi = Fraction(0)
    for a in range(N):
        for b in range(N):
            if a == b:
                c = Fraction(0) if kinds[a] == 0 else Fraction(1)
            elif kinds[a] == 0 and kinds[b] == 0:
                c = 1 - theta
            else:
                c = Fraction(1)
            # Re(Q^2) = Re^2 - Im^2; the imaginary parts cancel in the sum
            xi += c * (re[a][b] ** 2 - im[a][b] ** 2)
    xi -= 4                                   # k = 1
    return {"n": n, "k": 1, "t": t, "theta": theta,
            "hermitian": herm, "Q2_involution": invol, "Q3_symmetry": sym,
            "Q4_diag": diag, "Q5_cauchy_schwarz": cs, "Q1_psd": psd,
            "Xi": xi, "Xi_float": float(xi), "violates": xi < 0,
            "closed_form": (1 - theta) * n * (n - 1)
            + 2 * (1 + 2 * t * t) ** 2 - 2 - 4 * n * t * t - 4 + 4}


# ---------------------------------------------------------------------------
# 7. the relaxation scan, its duals, and the realizability diagnosis
# ---------------------------------------------------------------------------


def sdp_scan(sizes, theta: float = THETA_FULL, solver: str = "CLARABEL",
             **opts) -> list:
    """:func:`relax` over a list of ``(n, k)``, with the cone's own local
    minimum alongside so the two halves of the gap can be told apart:
    ``relaxation <= cone minimum <= min over real configurations``."""
    out = []
    for n, k in sizes:
        rec = relax(n, k, theta, solver=solver, **opts)
        cone = cone_local_min(n, k, theta, seed=0,
                              **{q: v for q, v in opts.items()
                                 if q in ("depth_cap", "phi_range",
                                          "cross_cap")})
        out.append({"n": n, "k": k, "N": rec["N"], "d": rec["d"],
                    "status": rec["status"], "relaxation": rec["value"],
                    "cone_local": cone["value"],
                    "lift_gap": (cone["value"] - rec["value"]
                                 if rec["value"] is not None else None),
                    "Q": rec.get("Q")})
    return out


def dual_report(rec) -> dict:
    """The dual multipliers of a solved :func:`relax` problem.

    The only multiplier that could carry a size-independent shape is the
    one on (Q1) --- an ``N x N`` (real ``2N x 2N``) PSD matrix indexed by
    atom pairs.  The relaxation knows nothing about where the atoms sit,
    so a size-independent multiplier can only be a function of the atom
    TYPES and of the involution; that is what is measured here.
    """
    cons = rec["constraints"]
    duals = [c.dual_value for c in cons]
    L = rec["index"]
    out = {"n": rec["n"], "k": rec["k"], "value": rec["value"],
           "n_constraints": len(cons)}
    if duals and duals[0] is not None and np.ndim(duals[0]) == 2:
        S = np.asarray(duals[0], float)
        N = L.N
        if S.shape == (2 * N, 2 * N):
            SR, SI = S[:N, :N], S[N:, :N]
            out["Q1_dual_re"] = SR
            out["Q1_dual_im"] = SI
            out["Q1_dual_trace"] = float(np.trace(SR))
            blocks = {}
            for a in range(N):
                for b in range(N):
                    key = (int(L.kinds[a]), int(L.kinds[b]),
                           "sigma" if L.sigma[a] == b else
                           ("diag" if a == b else "off"))
                    blocks.setdefault(key, []).append(SR[a, b])
            out["blocks"] = {str(kk): (float(np.mean(v)), float(np.std(v)))
                             for kk, v in blocks.items()}
    return out


def realizability_report(Q, kinds, sigma, restarts: int = 40,
                         seed: int = 0) -> dict:
    """Is a given ``Q`` the Gram matrix of any real configuration?

    Fits atoms ``zeta`` (on-line ones pinned to the imaginary axis, pair
    ones to ``+/- y + i t``) by least squares against
    ``Psi(zeta_a + conj zeta_b)/A`` and reports the best residual.  A
    residual bounded away from zero says the relaxation's minimiser is
    not a configuration --- which is the whole diagnosis when the value
    is negative.
    """
    from scipy.optimize import minimize as _min
    Q = np.asarray(Q, complex)
    N = Q.shape[0]
    n = int((np.asarray(kinds) == 0).sum())
    k = (N - n) // 2
    rng = np.random.default_rng(seed)

    def build(v):
        xs = v[:n]
        ts = v[n:n + k]
        ys = v[n + k:]
        z = [1j * x for x in xs]
        for i in range(k):
            z += [ys[i] + 1j * ts[i], -ys[i] + 1j * ts[i]]
        return np.array(z, complex)

    def res(v):
        M = qmat(build(v))
        return float(np.abs(M - Q).ravel() @ np.abs(M - Q).ravel())

    best = math.inf
    bv = None
    for _ in range(restarts):
        v0 = np.concatenate([rng.uniform(-20, 20, n),
                             rng.uniform(-20, 20, k),
                             rng.uniform(0.0, 0.5, k)])
        r = _min(res, v0, method="Nelder-Mead",
                 options=dict(maxiter=6000, fatol=1e-14, xatol=1e-10))
        if r.fun < best:
            best, bv = float(r.fun), r.x
    return {"residual_sq": best, "residual": math.sqrt(max(best, 0.0)),
            "frobenius_Q": float(np.linalg.norm(Q)),
            "relative": math.sqrt(max(best, 0.0)) / max(
                float(np.linalg.norm(Q)), 1e-30),
            "fit": (build(bv) if bv is not None else None)}


# ---------------------------------------------------------------------------
# 8. the recorded campaign
# ---------------------------------------------------------------------------

#: What the degree-2 (Shor) lift returns, by size, at theta = 995/1000,
#: solver CLARABEL, all optional constraints OFF.  ``relaxation`` is a
#: valid lower bound for the minimum of Xi over real configurations; the
#: true minimum is 0 (attained in the limit of a single far-separated
#: pair, and of separated on-line points).  Reproduce with
#: ``sdp_scan(SDP_RECORD["sizes"])``.
SDP_RECORD = {
    "theta": THETA_FULL,
    "solver": "CLARABEL",
    "sizes": [(0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (2, 1), (3, 1),
              (4, 1), (2, 2), (4, 2), (6, 1), (8, 1), (2, 3), (4, 3),
              (6, 2)],
    "values": {(0, 1): 0.0, (0, 2): -8.0, (0, 3): -12.0, (0, 4): -16.0,
               (1, 1): -4.0, (2, 1): -7.99, (3, 1): -12.97, (4, 1): -19.94,
               (2, 2): -11.99, (4, 2): -23.94, (6, 1): -39.85,
               (8, 1): -67.72, (2, 3): -15.99, (4, 3): -27.94,
               (6, 2): -43.85},
    # a fit, not a theorem: every scanned size with n >= 2 or k >= 2 came
    # out at (1-theta) n(n-1) - n^2 - 4k to solver accuracy.  Read as: the
    # lift sends the pair energy to 0 (against the kernel-checked 4k), the
    # cross block to -n^2, and the on-line block to its own maximum.
    "observed_fit": "(1-theta) n(n-1) - n^2 - 4k   (n >= 2 or k >= 2)",
    "n0_k1_is_tight": True,
}

#: The cone's own local minima (upper bounds for the cone minimum), same
#: theta.  ``bare`` is (Q1)-(Q5); ``ranged`` adds the three derived window
#: ranges (``depth_cap``, ``phi_range``, ``cross_cap``), which need the
#: depth hypothesis ``y in [0, 1/2]``.
CONE_RECORD = {
    "bare": {(2, 1): 0.0, (3, 1): -0.47, (4, 1): -1.94, (5, 1): -4.40,
             (6, 1): -7.85, (3, 2): -0.636667, (4, 2): -2.606667},
    "ranged": {(2, 1): 0.0, (3, 1): -0.045366, (4, 1): -0.048130,
               (5, 1): -0.095863, (6, 1): -0.133784, (3, 2): -0.117655,
               (4, 2): -0.244541},
    "exact_family": "Xi = (1-theta) n(n-1) + 2(1+2t^2)^2 - 2 - 4 n t^2",
}


# ---------------------------------------------------------------------------
# 9. the one size-independent multiplier there is
# ---------------------------------------------------------------------------


def inertia_multiplier(n: int, k: int) -> np.ndarray:
    """``P = 2 perm(sigma)``: the multiplier behind :func:`inertia_bound`.

    It is a FIXED KERNEL on atom pairs --- ``h(a,b) = 2 [b = sigma a]``,
    with no dependence on ``n``, ``k`` or on where the atoms sit --- which
    is exactly the shape a size-independent certificate would have to
    take.  It is also, on the evidence of :func:`dual_report`, the shape
    the one solved-to-optimality relaxation returns: at ``n = 0, k = 1``
    the multiplier on (Q1) comes out proportional to ``I - perm(sigma)``.

    What it buys is :func:`inertia_bound`, and that is short of the
    obligation by exactly ``nk/(n+k) + theta R`` (:func:`inertia_shortfall`)
    --- so a size-independent multiplier exists, and it is not enough.
    """
    L = lift_index(n, k)
    P = np.zeros((L.N, L.N))
    for a in range(L.N):
        P[a, L.sigma[a]] = 2.0
    return P


def relaxation_is_a_lower_bound(sizes, samples: int = 40, seed: int = 7,
                                theta: float = THETA_FULL) -> list:
    """Control: the relaxation value must sit below ``Xi`` at every real
    configuration of that size.  Random configurations, no descent."""
    rng = np.random.default_rng(seed)
    out = []
    for n, k in sizes:
        val = relax(n, k, theta)["value"]
        worst = math.inf
        for _ in range(samples):
            xs = np.sort(rng.uniform(-30, 30, n))
            ts = np.sort(rng.uniform(-30, 30, k))
            ys = rng.uniform(0.0, 0.5, k)
            worst = min(worst, target_from_config(
                xs, list(zip(ts, ys)), theta))
        out.append({"n": n, "k": k, "relaxation": val,
                    "worst_sampled": worst, "valid": val <= worst + 1e-6})
    return out


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------


def audit():
    print("= 1. THE MATRIX FORM, against joint_universal's evaluators =")
    rows = matrix_form_defect(n_quad=1600001)
    for r in rows:
        print(f"  {r['name']:26s} matrix {r['matrix']:+13.8f}  reference "
              f"{r['reference']:+13.8f}  defect {r['defect']:.2e}")
    print(f"  worst defect {max(r['defect'] for r in rows):.2e} "
          "(quadrature-limited: the reference is the grid side)")
    print("  blocks on one mixed configuration:")
    tt = target_terms([0.0, 1.3, 7.7], [(0.4, 0.49), (9.0, 0.2)])
    print(f"    pair {tt['pair_block']:.5f} (budget {tt['budget']:+.5f}) "
          f"+ cross {tt['cross_block']:+.5f} + on-line {tt['online_block']:+.5f}"
          f" - 4k  =  {tt['target']:+.5f}")

    print("= 2. the structural facts (Q1)-(Q5) on real configurations =")
    for name, on, pr in VALIDATION_CONFIGS[:4]:
        f = structural_facts(on, pr)
        print(f"  {name:24s} min eig {f['Q1_min_eig']:+.2e}  involution "
              f"{f['Q2_involution_defect']:.1e}  symmetry "
              f"{f['Q3_symmetry_defect']:.1e}  min diag {f['Q4_min_diag']:.6f}"
              f"  worst C-S {f['Q5_worst_cauchy_schwarz']:+.1e}")
    print(f"  derived ranges: psi(1)={DIAG_CAP:.6f}  psi(1/2)={PSI_HALF:.6f}"
          f"  min Phi2/A = {PHI_MIN:.6f}")

    print("= 3. the inertia bound on the COMBINED atom set =")
    for name, on, pr in VALIDATION_CONFIGS:
        d = inertia_defect(on, pr)
        print(f"  {name:24s} sum Q^2 {d['sum_sq']:9.5f} >= "
              f"(n+2k)^2/(n+k) = {d['bound']:8.5f}  slack {d['slack']:+9.5f}"
              f"  (trace identity defect {d['tr_identity_defect']:.1e})")
    for n, k in ((1, 1), (3, 2), (8, 4)):
        s = inertia_shortfall(n, k, 0.0)
        print(f"  n={n} k={k}: inertia gives {s['inertia']:.5f}, the "
              f"obligation needs {s['needed']:.5f} at R=0 -- short by "
              f"nk/(n+k) = {s['shortfall']:.5f}")

    print("= 4. THE CONE (Q1)-(Q5) DOES NOT IMPLY THE OBLIGATION =")
    print("  exact rational witnesses (fractions arithmetic end to end):")
    for n in (2, 3, 4, 6):
        for t in (Fraction(1, 2), Fraction(1)):
            r = cone_violator_exact(n, t)
            ok = all([r["hermitian"], r["Q2_involution"], r["Q3_symmetry"],
                      r["Q4_diag"], r["Q5_cauchy_schwarz"], r["Q1_psd"]])
            print(f"    n={n} t={t}: (Q1)-(Q5) all exact {ok}   Xi = "
                  f"{r['Xi']} = {r['Xi_float']:+.4f}   "
                  f"{'VIOLATES' if r['violates'] else 'closes'}")
    print("  the family's value is (1-theta) n(n-1) + 2(1+2t^2)^2 - 2 - 4nt^2;")
    print("  at t^2 = (n-2)/4 it is (1-theta)n(n-1) - n^2/2 + 2n - 2 -> -inf.")
    print("  and the witness is not a configuration:")
    re_, im_ = cone_violator(3)
    Qv = np.array([[float(re_[a][b]) + 1j * float(im_[a][b])
                    for b in range(5)] for a in range(5)])
    rr = realizability_report(Qv, np.array([0, 0, 0, 1, 1]),
                              np.array([0, 1, 2, 4, 3]), restarts=12)
    print(f"    best fit to Psi(zeta_a + conj zeta_b)/A: relative residual "
          f"{rr['relative']:.4f} (a configuration would give ~0)")

    print("= 5. the cone's local minima, bare and with the derived ranges =")
    sizes = [(2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (3, 2), (4, 2)]
    for lab, opts in (("bare", {}),
                      ("+ranges", dict(depth_cap=True, phi_range=True,
                                       cross_cap=True))):
        got = cone_scan(sizes, seeds=3, **opts)
        print(f"  {lab:9s} " + "  ".join(
            f"({r['n']},{r['k']}) {r['best']:+.5f}" for r in got))
    print("  the derived ranges shrink the deficit ~50x and do not remove it:")
    print("  a pointwise entry bound cannot close a joint obligation.")

    print("= 6. THE DEGREE-2 (SHOR) RELAXATION, by size =")
    print("  recorded campaign (SDP_RECORD):")
    for nk, v in SDP_RECORD["values"].items():
        n, k = nk
        print(f"    n={n} k={k}: relaxation {v:+10.5f}   "
              f"(true minimum over configurations is 0)")
    print(f"  observed fit: {SDP_RECORD['observed_fit']}")
    print("  the lift, not the cone, is what is loose here:")
    r = relax(0, 2)
    L = r["index"]
    print(f"    n=0 k=2: relaxation {r['value']:+.5f} while Xi at the "
          f"relaxation's own first moment is "
          f"{target_from_Q(r['Q'], L.kinds, THETA_FULL, 2):+.5f}")
    rr = realizability_report(r["Q"], L.kinds, L.sigma, restarts=10)
    print(f"    and that first moment IS a configuration (relative residual "
          f"{rr['relative']:.2e}) -- so the negative value lives entirely in "
          "the moment matrix Z, which is not p p'.")
    print("  => the relaxation does not even reproduce PairEnergy.lean at "
          "k >= 2, whose proof is an inertia argument, not a degree-2 fact.")

    print("= 7. the size-independent multiplier that does exist =")
    d1 = dual_report(relax(0, 1))
    print("  n=0 k=1 is the one size solved at 0; its (Q1) multiplier is")
    print("   ", np.array2string(np.round(d1["Q1_dual_re"], 5),
                                 prefix="    "))
    print("  i.e. proportional to I - perm(sigma), the same kernel as the "
          "inertia multiplier P = 2 perm(sigma) -- size-independent in "
          "shape, and short by nk/(n+k) + theta R at every larger size.")

    print("= controls =")
    for rec in relaxation_is_a_lower_bound([(1, 1), (2, 1), (0, 2)]):
        print(f"  lower-bound control n={rec['n']} k={rec['k']}: relaxation "
              f"{rec['relaxation']:+.5f} <= worst sampled "
              f"{rec['worst_sampled']:+.5f}: {rec['valid']}")
    print("  planted infeasibility at the one tight size (n=0, k=1):")
    for c in (4.0, 4.25, 5.0):
        v = relax(0, 1, constant=c)["value"]
        print(f"    constant {c}: relaxation {v:+.6f} "
              f"{'(rejected)' if v < -1e-6 else '(accepted)'}")
    print("  CLARABEL vs SCS:")
    for n, k in ((0, 1), (1, 1), (2, 1), (0, 2)):
        a_ = relax(n, k, solver="CLARABEL")["value"]
        b_ = relax(n, k, solver="SCS")["value"]
        print(f"    n={n} k={k}: {a_:+.6f} vs {b_:+.6f}  |diff| "
              f"{abs(a_ - b_):.2e}")


if __name__ == "__main__":
    audit()
