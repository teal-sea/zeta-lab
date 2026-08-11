"""Li's criterion and Jensen polynomials — the real-rootedness lane.

This is the corner of the subject where RH is restated as *"a sequence of
explicit numbers is nonnegative"* or *"a sequence of explicit polynomials has
only real roots"*.  It is the same mathematics that Rodgers–Tao (de
Bruijn–Newman) and Griffin–Ono–Rolen–Zagier (Jensen polynomials) work in, and
a cousin of the interlacing/real-rootedness machinery that settled
Kadison–Singer.

Two criteria live here.

1.  **Li's criterion** (Li 1997; Bombieri–Lagarias 1999).  With

        λ_n = (1/(n−1)!) · d^n/ds^n [ s^{n−1} log ξ(s) ] |_{s=1},

    RH ⟺ λ_n ≥ 0 for every n ≥ 1.  This is a *theorem*, not a heuristic; what
    is open is whether the λ_n are in fact nonnegative.  Equivalently (and this
    is the identity the module leans on)

        λ_n = Σ_ρ [ 1 − (1 − 1/ρ)^n ],

    the sum running over all nontrivial zeros, symmetrically in ρ ↔ 1−ρ.  Both
    sides are implemented independently — :func:`li_coefficient` with
    ``method="cauchy"`` never touches a zero, ``method="zeros"`` never touches
    ξ — and their agreement is the load-bearing test of the module.

    The generating function that makes the first method practical: substituting
    s = 1/(1−z) (which maps |z| < 1 onto Re s > 1/2),

        d/dz log ξ(1/(1−z)) = Σ_{n≥1} λ_n z^{n−1},

    derived in :func:`li_coefficients` and *verified* against the literal
    derivative definition in the tests.  So λ_n = n·[z^n] log ξ(1/(1−z)), and
    the Taylor coefficients come from one Cauchy/trapezoid pass around a
    circle — spectrally accurate, and free of the catastrophic cancellation
    that symbolic n-th derivatives of s^{n−1} log ξ(s) suffer.

    Calibration point:  λ_1 = 1 + γ/2 − log(4π)/2 = 0.02309570896612103381…
    (:func:`li_closed_form_lambda1`), matched to full working precision.

2.  **Jensen polynomials and Pólya's criterion.**  Write

        8·ξ(1/2 + z) = Σ_{n≥0} γ(n) z^{2n}/n!

    (the normalisation of Griffin–Ono–Rolen–Zagier 2019; the prefactor 8 comes
    from (−1+4z²)·Λ(1/2+z) = 8·ξ(1/2+z), with Λ = π^{−s/2}Γ(s/2)ζ(s)).  The
    Jensen polynomial of degree d and shift n is

        J^{d,n}(X) = Σ_{j=0}^{d} C(d,j) γ(n+j) X^j.

    Since ξ(1/2+z) is even, F(w) := 8·ξ(1/2+√w) = Σ γ(n) w^n/n! is entire of
    order 1/2 in w, and RH says exactly that its zeros w = −γ² are all real
    (and negative).  Pólya's classical criterion — a real entire function of
    genus 0 or 1 lies in the Laguerre–Pólya class iff *all* of its Jensen
    polynomials are hyperbolic (have only real roots) — therefore gives

        RH  ⟺  J^{d,n} is hyperbolic for every d ≥ 1 and every n ≥ 0.

    This is again an equivalence, and again one direction is trivial to
    *disprove* numerically and impossible to prove: a single non-hyperbolic
    J^{d,n} would refute RH.  GORZ (2019) proved that for each fixed d, all but
    finitely many n give a hyperbolic J^{d,n}, and that the roots of J^{d,n},
    suitably renormalised, converge as n → ∞ to the roots of the Hermite
    polynomial H_d — the "GUE side" of the picture, since Hermite roots are the
    zeros whose empirical measure is the semicircle law.
    :func:`hyperbolicity_scan` produces the (d, n) table; the honest reading of
    an all-``True`` table is "no violation found", never "evidence for RH"
    (``docs/08``; Littlewood).

A name collision to know about
------------------------------
``zeta.explicit.li`` is the *logarithmic integral* and is re-exported by
``zeta/__init__.py`` as ``zeta.li``.  Importing **this** module rebinds that
attribute: after ``import zeta.li``, ``zeta.li`` is the module, not the
function.  Nothing in the package accesses the function that way (every user
imports it by name), and the tests pin that ``zeta.explicit.li`` keeps working,
but import this module explicitly — ``import zeta.li as li_lane`` or
``from zeta.li import li_coefficients`` — and never rely on ``from zeta import
li`` meaning either one.

Conventions and honesty
-----------------------
Every public function takes ``dps`` and computes with internal guard digits,
leaving no global mpmath state modified.  Two independent methods exist for
both central objects (λ_n: Cauchy vs zero sum; γ(n): Riemann's Mellin integral
vs Cauchy on ξ), and the tests re-run the comparison rather than trusting
either.  Achieved accuracies are quoted in the individual docstrings and pinned
by ``tests/test_li.py``.
"""

from __future__ import annotations

import json
import math
import os
from typing import Any, Sequence

import mpmath
from mpmath import mp, mpf

from .core import DPS_DEFAULT, omega, xi

__all__ = [
    "DATA_DIR",
    "DPS_DEFAULT",
    "GAMMA1",
    "RADIUS_MAX",
    # --- Li's criterion ---------------------------------------------------
    "li_closed_form_lambda1",
    "li_coefficient",
    "li_coefficients",
    "li_asymptotic",
    "li_positivity_scan",
    "li_generating_function_defect",
    # --- Jensen polynomials -----------------------------------------------
    "xi_taylor_coefficients",
    "jensen_polynomial",
    "is_hyperbolic",
    "hyperbolicity_scan",
    "jensen_roots_vs_gue",
]

#: Extra guard digits carried internally and discarded before returning.
_GUARD: int = 10

#: Cache directory for expensive tables (derived from this file, never absolute).
DATA_DIR: str = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data"
)

#: The smallest zero ordinate.  Pinned against ``zeta.zeros.first_n_zeros`` by
#: the tests; used only to certify the radius bound below.
GAMMA1: str = "14.134725141734693790457251983562"

#: Largest Cauchy radius for which ``log xi(1/(1-z))`` is *unconditionally*
#: analytic on |z| <= r.  For every nontrivial zero ρ = β + iγ we have
#: |ρ| >= |γ| >= γ₁, hence the image point z = 1 − 1/ρ obeys
#: |z| >= 1 − 1/|ρ| >= 1 − 1/γ₁ = 0.92925…  So a disk of radius < that contains
#: no image of a zero, whether or not RH holds.
RADIUS_MAX: float = 1.0 - 1.0 / 14.134725141734693790


# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------


def _shrink(value, dps: int):
    """Round a value computed at high precision down to ``dps`` digits."""
    with mp.workdps(dps):
        return +value


def _real_checked(value, work: int, tol_digits: int, label: str, scale=None) -> mpf:
    """Return Re(value) after checking Im(value) is pure round-off.

    ``scale`` is the magnitude against which "pure round-off" is measured.  It
    defaults to max(|Re value|, 1), which is right for an O(1) computation; the
    Cauchy coefficient extractors pass the *round-off floor of the DFT*
    (largest sampled |f| divided by r^n), because dividing by r^n amplifies the
    round-off of the sum by exactly that factor.  Using max(|Re|, 1) there
    would reject perfectly good high-order coefficients.  Measured inside the
    real code path (both rows are re-run by
    ``tests/test_li.py::test_dft_imaginary_residue_needs_the_scaled_tolerance``
    and ``::test_dft_imaginary_residue_at_n_300_the_second_docstring_row``):

    ==================  ============  ============  ===========  ===========
    request             work digits   |Im c_n|      naive tol    DFT floor
    ==================  ============  ============  ===========  ===========
    λ_50  at dps = 20   60            5.1e-48       1.0e-48      7.9e-34
    λ_300 at dps = 20   132           2.4e-45       1.7e-120     1.4e-30
    ==================  ============  ============  ===========  ===========

    The naive tolerance rejects *both*.  The reason is not that c_n is small —
    c_n = λ_n/n is 0.87 at n = 50 and 1.73 at n = 300, so the naive scale is
    ~1 in both rows.  It is that the naive scale is blind to the r^{−n}
    division: at r = 1/2 and n = 300 that multiplies the round-off of the DFT
    sum by 2^300 = 2.037e90, and the measured ratio floor/naive is 8.246e89 —
    which is 2^300 times max|log ξ|/|Re c_n| = 0.7010/1.7323, i.e. the
    amplification exactly, up to an O(1) factor.
    The scaled tolerance accepts both rows with 14 and 15 orders of margin
    (1.5e14 and 6.0e14), and the resulting λ_50 = 43.5310964883…,
    λ_300 = 519.7019656192… are correct — they match the zero side (to 1.4e-8
    at n = 50) and the asymptotic.
    """
    re, im = mp.re(value), mp.im(value)
    base = max(abs(re), mp.mpf(1)) if scale is None else scale
    tol = mp.mpf(10) ** (-work + tol_digits) * base
    if abs(im) >= tol:
        raise ValueError(
            f"{label}: imaginary residue {mp.nstr(im, 8)} exceeds {mp.nstr(tol, 8)}; "
            "increase dps"
        )
    return mp.mpf(re)


def _roots_of_unity(n_points: int) -> list:
    """[e^{2πij/N} : j < N], computed once and reused by the DFT below.

    Building this table is what turns the O(N·n_max) coefficient extraction
    from thousands of transcendental evaluations into thousands of table
    look-ups plus one complex multiplication each.  Measured for
    ``li_coefficients(300, dps=20)`` — which rounds the request up to the cache
    step and so actually runs ``_li_cauchy(304, 20, 0.5)``: 132 working digits,
    751 nodes, 228 304 coefficient terms, ~9 s.  (The numbers for a bare
    ``_li_cauchy(300, …)`` are 131 digits and 744 nodes; both are pinned by
    ``tests/test_li.py::test_working_precision_and_node_counts``.)
    """
    return [mp.expjpi(mp.mpf(2 * j) / n_points) for j in range(n_points)]


def _unwrapped_log(values: Sequence) -> list:
    """log of samples taken *in order* around a closed curve, analytic branch.

    ``mp.log`` returns the *principal* branch, whose imaginary part jumps by 2π
    across the negative real axis.  That is only the analytic branch of
    log f while arg f stays inside (−π, π), which for log ξ(1/(1−z)) fails well
    inside the radius range this module admits: the supremum of |arg ξ| on
    |z| = r is 0.0102 at r = 0.3, 0.0311 at r = 0.5, 0.117 at r = 0.7, at least
    **1.282** at r = 0.9 (1024 nodes; 256 nodes see 1.266 and a 64-node sample
    only 1.100 — the sup is not resolved by coarse sampling), 1.987 at r = 0.92,
    and it keeps climbing towards :data:`RADIUS_MAX`.  An earlier version
    guarded with ``|arg| < π/2`` and marked the branch unreachable; it is in
    fact reached from r ≈ 0.915 up, i.e. the guard rejected legitimate radii.

    So instead of guarding, unwrap.  Node 0 is z = r > 0, where ξ(1/(1−r)) is
    real and positive (s = 1/(1−r) > 1, and ξ > 0 on (1, ∞)), so the analytic
    branch has imaginary part 0 there; each subsequent node takes the 2π shift
    that keeps the imaginary part continuous.

    Two conditions are checked rather than assumed:

    * **no undersampling** — consecutive nodes must move arg by less than π/2,
      otherwise the 2π ambiguity cannot be resolved;
    * **zero winding** — continuing past the last node must land back on node 0
      with no accumulated 2π.  A nonzero winding number would mean ξ∘(1/(1−z))
      has a zero inside the circle, which contradicts :data:`RADIUS_MAX`; it is
      a genuine alarm, not a numerical nuisance.

    For r ≤ 0.9 no node ever needs a shift, so this reproduces ``mp.log``
    exactly: every committed ``data/li_lambda_*.json`` table (144 entries at
    n_max ≤ 64, plus 304 entries at dps 20) recomputes **bit-identically**
    after the change, and r ∈ {0.3, 0.5, 0.7, 0.9} still agree bit for bit.
    What is new is that r = 0.92 and r = 0.929 now work at all.
    """
    two_pi = 2 * mp.pi
    args = [mp.arg(v) for v in values]
    unwrapped = [args[0]]
    for a in args[1:]:
        prev = unwrapped[-1]
        cand = a + mp.nint((prev - a) / two_pi) * two_pi
        if abs(cand - prev) >= mp.pi / 2:
            raise ValueError(
                f"arg xi moves by {mp.nstr(abs(cand - prev), 6)} between adjacent "
                "sample points; the circle is undersampled and the branch of "
                "log xi cannot be resolved"
            )
        unwrapped.append(cand)
    winding = int(mp.nint((unwrapped[-1] - args[0]) / two_pi))
    if winding != 0:
        raise ValueError(
            f"log xi winds {winding} time(s) around the sampling circle; the "
            "disk is not zero-free, which contradicts the radius bound"
        )
    return [mp.mpc(mp.log(abs(v)), a) for v, a in zip(values, unwrapped)]


#: Cached tables are computed and stored at n_max rounded up to a multiple of
#: this, so that a session asking for 9, 17, 24 and 44 coefficients leaves four
#: files (16, 32, 32, 48) rather than four *different* ones — and the 24-request
#: is served from the 32-table.  The extra work is negligible next to the cost
#: of the first evaluation.
_CACHE_STEP: int = 16


def _round_up(n: int, step: int = _CACHE_STEP) -> int:
    return int(step * math.ceil(max(int(n), 1) / step))


def _cache_path(kind: str, **params) -> str:
    tag = "_".join(f"{k}{v}" for k, v in sorted(params.items()))
    return os.path.join(DATA_DIR, f"li_{kind}_{tag}.json")


def _load_table(kind: str, n_max: int, dps: int, **extra) -> list[mpf] | None:
    """Reuse any cached table with at least ``n_max`` entries and >= ``dps``."""
    if not os.path.isdir(DATA_DIR):
        return None
    prefix = f"li_{kind}_"
    for name in sorted(os.listdir(DATA_DIR)):
        if not (name.startswith(prefix) and name.endswith(".json")):
            continue
        try:
            with open(os.path.join(DATA_DIR, name)) as fh:
                blob = json.load(fh)
            if blob.get("kind") != kind:
                continue
            if int(blob.get("n_max", -1)) < n_max or int(blob.get("dps", 0)) < dps:
                continue
            if any(str(blob.get(k)) != str(v) for k, v in extra.items()):
                continue
            with mp.workdps(dps):
                return [+mp.mpf(v) for v in blob["values"][: n_max + 1]]
        except (OSError, ValueError, KeyError, TypeError):  # pragma: no cover
            continue
    return None


def _save_table(kind: str, values: Sequence, n_max: int, dps: int, **extra) -> str:
    os.makedirs(DATA_DIR, exist_ok=True)
    path = _cache_path(kind, n=n_max, dps=dps, **extra)
    with mp.workdps(dps):
        digits = mpmath.libmp.repr_dps(mp.prec)
        payload = {
            "kind": kind,
            "n_max": int(n_max),
            "dps": int(dps),
            "values": [mp.nstr(mp.mpf(v), digits) for v in values],
            **{k: str(v) for k, v in extra.items()},
        }
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(payload, fh, indent=1)
    os.replace(tmp, path)
    return path


# ===========================================================================
# 1.  Li's criterion
# ===========================================================================


def li_closed_form_lambda1(dps: int = DPS_DEFAULT) -> mpf:
    """λ₁ in closed form:  1 + γ/2 − log(4π)/2 = 0.023095708966121033814…

    Derivation.  λ₁ = (d/ds) log ξ(s) |_{s=1} = ξ'(1)/ξ(1).  With
    ξ(s) = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s),

        (log ξ)'(s) = 1/s + 1/(s−1) − ½log π + ½ψ(s/2) + ζ'(s)/ζ(s),

    and near s = 1 the pole of ζ makes ζ'/ζ(s) = −1/(s−1) + γ + O(s−1), which
    cancels the 1/(s−1).  What is left at s = 1 is
    1 + γ − ½log π + ½ψ(1/2) with ψ(1/2) = −γ − 2log 2, i.e.

        λ₁ = 1 + γ/2 − log(4π)/2.

    The tests check this against :func:`li_coefficient` for both methods.
    """
    with mp.workdps(dps + _GUARD):
        value = 1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2
    return _shrink(value, dps)


def _li_cauchy(n_max: int, dps: int, radius) -> list[mpf]:
    """λ_1 … λ_{n_max} from the Taylor coefficients of log ξ(1/(1−z)).

    See :func:`li_coefficients` for the derivation and the error accounting.
    """
    R = mp.mpf(radius)
    if not (0 < R < RADIUS_MAX):
        raise ValueError(
            f"radius must lie in (0, {RADIUS_MAX:.6f}) — beyond that the disk "
            "is no longer unconditionally free of images of zeta zeros"
        )
    decay = float(mp.log10(1 / R))            # digits lost to the 1/R^n division
    work = int(math.ceil(dps + 2 * _GUARD + n_max * decay))
    with mp.workdps(work):
        Rw = mp.mpf(radius)
        n_points = int(mp.ceil(work * mp.log(10) / mp.log(1 / Rw))) + n_max + 8
        w = _roots_of_unity(n_points)
        # --- sample, and build the analytic branch of the logarithm ----------
        xi_vals = [xi(1 / (1 - Rw * wj), work) for wj in w]
        vals = _unwrapped_log(xi_vals)
        biggest = max(abs(v) for v in vals)
        # --- one DFT pass extracts every Taylor coefficient ------------------
        out: list[mpf] = []
        for n in range(1, n_max + 1):
            acc = mp.fsum(
                vals[j] * w[(-(j * n)) % n_points] for j in range(n_points)
            )
            inv = mp.power(Rw, -n)
            c_n = acc * inv / n_points
            out.append(
                n
                * _real_checked(
                    c_n, work, _GUARD + 2, f"lambda_{n}", scale=biggest * inv
                )
            )
    return [_shrink(v, dps) for v in out]


def _phi(t):
    """arg(1 − 1/ρ) for ρ = 1/2 + it — the angle that drives the zero sum.

    1 − 1/ρ = ((t² − 1/4) + it)/(t² + 1/4), whose modulus is *exactly* 1 when
    Re ρ = 1/2 (|ρ − 1| = |ρ| there).  So on RH every zero contributes a point
    of the unit circle, e^{iφ(t)}, and the conjugate pair (ρ, ρ̄) contributes

        [1 − e^{inφ}] + [1 − e^{−inφ}] = 2(1 − cos nφ)  ≥  0,

    which is *why* RH forces λ_n ≥ 0.
    """
    return mp.atan2(t, t * t - mp.mpf(1) / 4)


def _pair_term(n: int, t):
    """2(1 − cos(n·φ(t))): the contribution of the zero pair 1/2 ± it."""
    return 2 * (1 - mp.cos(n * _phi(t)))


def _rs_theta(t):
    """Riemann–Siegel ϑ(t) = Im log Γ(1/4 + it/2) − (t/2) log π."""
    return mp.im(mp.loggamma(mp.mpc(mp.mpf(1) / 4, t / 2))) - t / 2 * mp.log(mp.pi)


def _zero_density(t):
    """dN/dt = ϑ'(t)/π = [½ Re ψ(1/4 + it/2) − ½ log π]/π."""
    return (mp.re(mp.digamma(mp.mpc(mp.mpf(1) / 4, t / 2))) / 2 - mp.log(mp.pi) / 2) / mp.pi


#: Precision at which zero ordinates are requested by the ``"zeros"`` branch.
#: The truncation error of that branch is ~1e-8 relative at 1000 zeros, so the
#: ordinates are never the limiting factor; asking for more digits than the
#: committed ``data/zeros_*.json`` tables carry would silently trigger a
#: multi-minute ``mpmath.zetazero`` recomputation instead of a cache hit.
ZERO_DPS: int = 30


def _li_zeros(
    n_values: Sequence[int], n_zeros: int, dps: int, zero_dps: int | None = None
) -> list[mpf]:
    """λ_n from the zero side, Σ_ρ [1 − (1 − 1/ρ)^n], with a tail correction.

    Write f_n(t) = 2(1 − cos nφ(t)), Ñ(t) = ϑ(t)/π + 1 for the smooth count and
    S = N − Ñ.  Splitting the sum at a height T,

        λ_n = Σ_{γ≤T} f_n(γ) + ∫_T^∞ f_n Ñ' dt − f_n(T)S(T) − ∫_T^∞ f_n' S dt,

    the third term being the boundary term of ∫_T^∞ f_n dS (f_n(∞) = 0).  T is
    taken to solve ϑ(T)/π + 1 = n_zeros + 1/2 and the code uses
    ``head + tail − f_n(T)·(−1/2)`` with ``head`` the sum over the *first
    n_zeros* ordinates.

    **Why the −1/2, when S(T) is often not −1/2.**  Choosing T that way does
    *not* force N(T) = n_zeros; S(T) = k − 1/2 where k = N(T) − n_zeros is the
    number of zeros sitting in (γ_{n_zeros}, T].  Measured, with the committed
    ordinate tables:

    ==========  ==========  ==========  ======  ========
    ``n_zeros`` γ_{n_zeros} T           N(T)    S(T)
    ==========  ==========  ==========  ======  ========
    100         236.524     237.718     100     −1/2
    200         396.382     398.277     201     **+1/2**
    400         679.742     681.206     400     −1/2
    800         1183.713    1185.046    800     −1/2
    1000        1419.423    1420.677    1001    **+1/2**
    ==========  ==========  ==========  ======  ========

    The formula is nevertheless right for every k, because the k missing zeros
    and the k missing units of S(T) cancel:

        head + k·f_n(T) + tail − f_n(T)(k − 1/2)  =  head + tail + f_n(T)/2,

    which is what the code computes — the k drops out identically.  (The
    residual of that cancellation is Σ_{γ_{n_zeros}<γ≤T}[f_n(γ) − f_n(T)], of
    size |f_n'(T)|·(T − γ), which is one of the two oscillating error terms
    tabulated in :func:`li_coefficients`.)  So the −1/2 is not a claim about
    S(T); it is the k-independent form of the boundary term.
    """
    from .zeros import first_n_zeros  # local import: avoids a cycle at import time

    work = dps + _GUARD
    gammas = first_n_zeros(
        int(n_zeros), dps=ZERO_DPS if zero_dps is None else int(zero_dps)
    )
    with mp.workdps(work):
        g_last = gammas[-1]
        # Midpoint truncation height: the smooth count ϑ(T)/π + 1 equals
        # n_zeros + 1/2 there.  S_T below is therefore −1/2 by construction —
        # NOT because N(T) = n_zeros (it often is not; see the docstring), but
        # because that is the k-independent form of the boundary term.
        target = mp.pi * (mp.mpf(n_zeros) - mp.mpf(1) / 2)
        T = mp.findroot(lambda t: _rs_theta(t) - target, g_last + 1)
        if not T > g_last:  # pragma: no cover - Gram-type failure, never seen
            T = g_last + mp.mpf(10) ** (-6)
        S_T = mp.mpf(n_zeros) - _rs_theta(T) / mp.pi - 1
        out = []
        for n in n_values:
            n = int(n)
            head = mp.fsum(_pair_term(n, g) for g in gammas)
            tail = mp.quad(
                lambda t, n=n: _pair_term(n, t) * _zero_density(t),
                [T, 2 * T, 10 * T, 100 * T, mp.inf],
            )
            out.append(head + tail - _pair_term(n, T) * S_T)
    return [_shrink(v, dps) for v in out]


def li_coefficients(
    n_max: int,
    method: str = "cauchy",
    dps: int = DPS_DEFAULT,
    n_zeros: int = 1000,
    radius: Any = "0.5",
    cache: bool = True,
    zero_dps: int | None = None,
) -> list[mpf]:
    """The Li coefficients λ_1 … λ_{n_max} (a list of length ``n_max``).

    Definition (Li 1997):

        λ_n = (1/(n−1)!) · d^n/ds^n [ s^{n−1} log ξ(s) ] |_{s=1},

    and **Li's criterion is a theorem**: RH ⟺ λ_n ≥ 0 for all n ≥ 1.

    Two independent implementations.

    ``method="cauchy"`` — *no zeros are used*.  Substitute s = 1/(1−z).  Since
    |z| < 1 ⟺ |1 − 1/s| < 1 ⟺ Re s > 1/2, the unit z-disk is the right half of
    the critical strip and beyond.  From the Hadamard product
    log ξ(s) = log ξ(0) + Σ_ρ log(1 − s/ρ) one computes, with w_ρ = 1 − 1/ρ,

        d/dz log ξ(1/(1−z)) = Σ_ρ [ 1/(1−z) − 1/(w_ρ − z) ]
                            = Σ_ρ Σ_{n≥0} (1 − w_ρ^{−(n+1)}) z^n,

    and since the zero set is invariant under ρ ↦ 1−ρ, and 1 − 1/(1−ρ) = 1/w_ρ,
    the coefficient of z^{n−1} is exactly Σ_ρ [1 − (1 − 1/ρ)^n] = λ_n.  Hence

        **λ_n = n · [z^n] log ξ(1/(1−z))**,

    and the Taylor coefficients are extracted by one equispaced trapezoid pass
    around |z| = ``radius`` — the Cauchy integral, which for an analytic
    integrand converges geometrically.  The identity itself is *verified*, not
    assumed: :func:`li_generating_function_defect` compares this against the
    literal n-th-derivative definition.

    The disk |z| ≤ r is **unconditionally** free of images of zeta zeros for
    r < 1 − 1/γ₁ = 0.92925… (:data:`RADIUS_MAX`), because |1 − 1/ρ| ≥ 1 − 1/|ρ|
    and |ρ| ≥ |Im ρ| ≥ γ₁ = 14.1347… for every nontrivial zero — no appeal to
    RH anywhere.  ξ is entire and nonvanishing there, so a single-valued
    analytic branch of log ξ exists on the disk.  It is **not** the principal
    branch throughout that range: the sampled max of |arg ξ| on |z| = r is
    0.0311 at r = 0.5 but 1.266 at r = 0.9 (256 nodes; 1024 nodes give 1.282 —
    the sup is not resolved by coarse sampling) and 1.987 at r = 0.92, so
    :func:`_unwrapped_log` builds the analytic branch by continuity from
    z = r (where ξ is real and positive) and checks the winding number is 0.
    The operative evidence that the branch is right is *tested*: a branch error
    would be radius-dependent, and the coefficients are identical to all
    returned digits for r ∈ {0.3, 0.5, 0.7, 0.9, 0.92, 0.929}, and match the
    literal d^n/ds^n definition to ~50 significant digits.

    Error accounting: aliasing contributes Σ_{k≥1} c_{n+kN} r^{kN} with
    c_m = λ_m/m growing only like log m, so N ≈ work·ln10/ln(1/r) nodes puts it
    below the round-off floor; round-off is amplified by r^{−n}, i.e.
    n·log₁₀(1/r) digits, which the working precision carries explicitly.

    ``method="zeros"`` — *ξ is never evaluated*.  The zero side

        λ_n = Σ_ρ [1 − (1 − 1/ρ)^n] = Σ_{γ>0} 2(1 − cos(n φ(γ))),
        φ(t) = arg((t² − 1/4) + it) = arctan(t/(t² − 1/4)),

    summed over the first ``n_zeros`` cached ordinates, plus a tail
    ∫_T^∞ 2(1−cos nφ(t))·(ϑ'(t)/π) dt from the smooth zero density, plus the
    Euler–Maclaurin boundary correction −f_n(T)·(−1/2).  See :func:`_li_zeros`
    for why the −1/2 is right even though S(T) is frequently +1/2; without the
    correction the estimate is ~3 orders of magnitude worse.  This branch
    *uses* RH for the zeros it consumes (they are the verified critical-line
    ordinates), so it is a cross-check of two formulas, never evidence for RH.

    Measured agreement of the two methods at ``dps=25``, over n ≤ 8 (this is
    the module's load-bearing test; see ``tests/test_li.py``):

    ==========  =======  ==========================  ==================
    ``n_zeros`` T        max |cauchy − zeros|, n≤8   sign of cauchy−zeros
    ==========  =======  ==========================  ==================
    100         237.7    1.913e-06                   + for every n
    200         398.3    1.914e-07                   + for every n
    400         681.2    1.469e-07                   **−** for every n
    800         1185.0   1.023e-08                   + for every n
    1000        1420.7   1.550e-08                   + for every n
    ==========  =======  ==========================  ==================

    Two honest readings of that table.  (i) The discrepancy has the *same sign
    for every n* — it is a multiple of f_n(T) — but its sign in ``n_zeros`` is
    not fixed: at n_zeros = 400 the zero side overshoots.  (ii) It shrinks with
    ``n_zeros`` only *on average*: 800 zeros beat 1000 here.  The residual is
    ∫_T^∞ f_n'(t) S(t) dt plus the mismatch between f_n(T) and f_n at the last
    few zeros below T, and both oscillate with T.  Over the decade 100 → 1000
    the observed shrink factor is 123, against 36 for a pure 1/T² law.

    Results are cached under ``data/li_lambda_*.json``.
    """
    n_max = int(n_max)
    if n_max < 1:
        return []
    if method == "cauchy":
        if not cache:
            return _li_cauchy(n_max, dps, radius)
        hit = _load_table("lambda", n_max, dps, method="cauchy", radius=radius)
        if hit is not None:
            return hit[:n_max]
        n_store = _round_up(n_max)
        out = _li_cauchy(n_store, dps, radius)
        try:
            _save_table("lambda", out, n_store, dps, method="cauchy", radius=radius)
        except OSError:  # pragma: no cover - read-only fs
            pass
        return out[:n_max]
    if method == "zeros":
        return _li_zeros(range(1, n_max + 1), n_zeros, dps, zero_dps)
    raise ValueError(f"unknown method {method!r} (use 'cauchy' or 'zeros')")


def li_coefficient(
    n: int,
    method: str = "cauchy",
    dps: int = DPS_DEFAULT,
    n_zeros: int = 1000,
    radius: Any = "0.5",
    zero_dps: int | None = None,
) -> mpf:
    """A single Li coefficient λ_n.  See :func:`li_coefficients` for the maths.

    λ_1 = 0.023095708966121033814…, λ_2 = 0.092345735228046670386…,
    λ_3 = 0.207638920554324803791…  (``method="cauchy"``, pinned by the tests
    against the closed form and against ``method="zeros"``).
    """
    n = int(n)
    if n < 1:
        raise ValueError("Li coefficients are indexed by n >= 1")
    if method == "zeros":
        return _li_zeros([n], n_zeros, dps, zero_dps)[0]
    return li_coefficients(n, method=method, dps=dps, radius=radius)[-1]


def li_generating_function_defect(n: int, dps: int = DPS_DEFAULT, radius="0.4") -> mpf:
    """λ_n from the generating function minus λ_n from the literal definition.

    The literal definition is differentiated by mpmath's Cauchy-integral
    differentiator (``mp.diff(..., method='quad')``) applied to
    s ↦ s^{n−1} log ξ(s) at s = 1; the generating-function value comes from
    :func:`li_coefficients`.  Identically zero — this is the numerical proof
    that the substitution s = 1/(1−z) reproduces Li's definition and not some
    neighbouring normalisation.

    Cheap only for small n (the literal path needs one quadrature per
    coefficient and loses digits fast).  Measured |defect| for n = 1, 2, 3, 4:

        dps = 20:  1.7e-52,  5.0e-52,  1.0e-51,  1.1e-50
        dps = 30:  7.29e-63, 2.92e-62, 1.75e-61, 7.39e-61

    i.e. zero to the full internal working precision (dps + 30 digits) in both
    cases.  The dps = 20 row is pinned in the fast tier and the dps = 30 row
    (11 s) in the slow tier.
    """
    n = int(n)
    work = dps + 3 * _GUARD
    with mp.workdps(work):
        f = lambda s: mp.power(s, n - 1) * mp.log(xi(s, work))
        literal = mp.diff(
            f, mp.mpf(1), n, method="quad", radius=mp.mpf(radius)
        ) / mp.factorial(n - 1)
        literal = _real_checked(literal, work, 2 * _GUARD, f"literal lambda_{n}")
        value = li_coefficients(n, dps=work, cache=False)[-1] - literal
    return _shrink(value, dps)


def li_asymptotic(n: int) -> float:
    """The RH-predicted growth of λ_n, as a plain float:

        λ_n ≈ (n/2)·(log n − log 2π + γ − 1) + 1.

    **Where the main term comes from** (and it is a derivation, not a memory):
    on RH, λ_n = Σ_{γ>0} 2(1 − cos nφ(γ)) with φ(t) ≈ 1/t, and the smooth zero
    density is (1/2π)log(t/2π) dt.  Substituting u = n/t,

        λ_n ≈ (n/π) ∫_0^∞ (1 − cos u)[log n − log 2π − log u] u^{−2} du,

    and with ∫(1−cos u)u^{−2}du = π/2 and ∫(1−cos u)u^{−2}log u du = (1−γ)π/2
    this is exactly (n/2)(log n − log 2π + γ − 1).

    **Hedge.**  The constant term is quoted as +1 from the literature
    (Bombieri–Lagarias 1999; Voros 2006), and the true remainder is an
    *oscillating* term — the resonance of the individual zeros — of size
    O(√n log n) on RH.  Our own measurement cannot separate a constant from
    that oscillation.  Measured on this machine for the computed λ_n:

    * λ_n − li_asymptotic(n) ∈ [−2.606, +3.601] for 1 ≤ n ≤ 300, with mean
      0.587 and no visible growth of the mean; the *envelope* does grow (it is
      ±1.2 for n ≤ 50 and ±3.6 by n = 300), consistent with an O(√n log n)
      oscillation and inconsistent with the residual being a constant.
    * relative error |λ_n/li_asymptotic(n) − 1| ≤ 2.95e-2 for n ≥ 50 and
      ≤ 1.25e-2 for n ≥ 100.

    So: the leading term is verified, the constant is not (and cannot be, at
    these n).
    """
    n = int(n)
    if n < 1:
        raise ValueError("li_asymptotic is defined for n >= 1")
    gamma_e = 0.5772156649015328606
    return 0.5 * n * (math.log(n) - math.log(2 * math.pi) + gamma_e - 1.0) + 1.0


def li_positivity_scan(
    n_max: int,
    method: str = "cauchy",
    dps: int = DPS_DEFAULT,
    n_zeros: int = 1000,
    radius: Any = "0.5",
) -> list[dict]:
    """Tabulate λ_n for n = 1 … n_max with its distance from the RH boundary.

    Each row is ``{'n', 'lambda_n', 'positive', 'margin', 'margin_digits',
    'asymptotic', 'relative_to_asymptotic'}`` where

    * ``margin`` = float(λ_n) — the signed distance to the boundary λ = 0 that
      Li's criterion cares about;
    * ``margin_digits`` = log₁₀(λ_n) + dps — how many decimal digits separate
      the value from the *absolute* floor 10^{−dps}.  A small or negative
      ``margin_digits`` would mean the computation cannot decide the sign.
      Note the Cauchy path's error is *relative*, ≈|λ_n|·10^{−dps}, so for
      λ_n ≥ 1 the honest sign margin is the smaller number ``dps`` itself;
      ``margin_digits`` exceeds it by log₁₀(λ_n) and is the right diagnostic
      only in the regime λ_n ≲ 1 where a λ_n near zero is the worry.

    **Honest reading.**  An all-``True`` ``positive`` column says *no violation
    of Li's criterion was found in the scanned range*.  It is not evidence for
    RH (``docs/08``): by Littlewood's theorem finite computation cannot be, and
    Li's criterion is an equivalence over *all* n.

    **And on ``method="zeros"`` it says even less than that — it cannot say
    anything else.**  That route is ``head + tail + boundary`` where
    ``head = Σ 2(1 − cos nφ(γ)) ≥ 0`` termwise, ``tail = ∫ f_n·dN/dt ≥ 0``, and
    ``boundary = −f_n(T)·S_T = +f_n(T)/2 ≥ 0`` because the route feeds it
    ``S_T = −1/2`` by construction.  So ``positive`` is **structurally True for
    every n on this route**, whatever the zeros do: the route consumes a list of
    on-line ordinates, and a sum of nonnegative terms cannot report a negative.
    A column that could never read False is a control with no power, which is
    the admission rule ``harness/README.md`` applies to batteries, applied here
    to a scan.  The default ``method="cauchy"`` is the unconditional route and
    is the one whose sign carries information.  (Measured 2026-08-11; the row
    dicts now carry ``can_report_negative`` so the caller is told in data
    rather than only in prose.)
    """
    lam = li_coefficients(
        n_max, method=method, dps=dps, n_zeros=n_zeros, radius=radius
    )
    rows = []
    for i, value in enumerate(lam, start=1):
        with mp.workdps(dps):
            digits = float(mp.log10(abs(value))) + dps if value != 0 else -float(dps)
        asym = li_asymptotic(i)
        rows.append(
            {
                "n": i,
                "lambda_n": value,
                "positive": bool(value > 0),
                # the zeros route sums nonnegative pieces, so its `positive`
                # column cannot read False — see the docstring
                "can_report_negative": method != "zeros",
                "margin": float(value),
                "margin_digits": digits,
                "asymptotic": asym,
                "relative_to_asymptotic": float(value) / asym,
            }
        )
    return rows


# ===========================================================================
# 2.  The Xi Taylor coefficients gamma(n)
# ===========================================================================


def _gamma_integral(n_max: int, dps: int) -> list[mpf]:
    """γ(0) … γ(n_max) from Riemann's Mellin representation of ξ.

    Starting from ``zeta.core.theta_mellin_xi``,
    Λ(s) = 1/(s(s−1)) + ∫_1^∞ (x^{s/2−1} + x^{(1−s)/2−1}) ω(x) dx and
    ξ = ½s(s−1)Λ, put s = 1/2 + z (so s(s−1) = z² − 1/4) and note
    x^{s/2−1} + x^{(1−s)/2−1} = 2x^{−3/4} cosh((z/2) log x):

        ξ(1/2+z) = 1/2 + (z² − 1/4) ∫_1^∞ x^{−3/4} cosh((z/2)log x) ω(x) dx.

    Expanding the cosh and substituting x = e^u,

        I_k = ∫_0^∞ u^{2k} e^{u/4} ω(e^u) du,   J_k = I_k / (4^k (2k)!),
        [z^{2n}] ξ(1/2+z) = J_{n−1} − J_n/4   (J_{−1} := 0, plus 1/2 at n = 0),

    and γ(n) = 8·n!·[z^{2n}]ξ(1/2+z).

    Every I_k is the integral of a *positive* integrand, so there is no
    cancellation anywhere except the mild 1/2 − J_0/4 at n = 0 and the
    J_{n−1} − J_n/4 differences, where J_n/J_{n−1} = O((log n)²/n²) — no
    cancellation at all for n ≳ 3.  Measured against the independent Cauchy
    path (:func:`_gamma_cauchy`): the two return **bit-identical** values —
    n ≤ 20 at dps = 30 and 50, and n ≤ 12 over the whole radius grid
    {4, 10, 30, 100, 300} at dps = 30 and 80, all pinned by the tests.  Against
    a dps = 110 reference of this same path the max relative error over n ≤ 12
    is 9.222e-32 / 1.303e-51 / 1.022e-81 at dps = 30 / 50 / 80 — i.e. the only
    error is the final rounding to ``dps``.

    The shared profile e^{u/4}ω(e^u) is memoised across the n_max+2
    quadratures, which is what makes the whole table cost one quadrature's
    worth of ω evaluations rather than n_max of them.
    """
    work = dps + _GUARD + 5
    with mp.workdps(work):
        profile: dict = {}

        def W(u):
            v = profile.get(u)
            if v is None:
                v = mp.exp(u / 4) * omega(mp.exp(u), work)
                profile[u] = v
            return v

        # ω(e^u) ~ e^{-π e^u}: at u = 7 that is e^{-3446}, far below any
        # working precision this module is used at, and u^{2k} cannot rescue it.
        pts = [0, mp.mpf(1) / 2, 1, 2, 3, 5, 7]
        I = [
            mp.quad(lambda u, k=k: mp.power(u, 2 * k) * W(u), pts)
            for k in range(n_max + 2)
        ]
        J = [I[k] / (mp.power(4, k) * mp.factorial(2 * k)) for k in range(n_max + 2)]
        out = []
        for n in range(n_max + 1):
            b = -J[n] / 4
            if n == 0:
                b += mp.mpf(1) / 2
            else:
                b += J[n - 1]
            out.append(8 * mp.factorial(n) * b)
    return [_shrink(v, dps) for v in out]


#: Ratios ρ/R tried when bounding the aliasing of the γ Cauchy pass.  The bound
#: is minimised over this ladder; the optimum sits near 100 for R ~ 30–300 and
#: near 1000 for small R, so the ladder brackets it on both sides.
_ALIAS_LAMBDAS: tuple = (2, 3, 10, 30, 100, 300, 1000, 3000)


def _gamma_cauchy_nodes(n_max: int, work: int, radius) -> int:
    """How many trapezoid nodes the γ Cauchy pass needs, *derived* not guessed.

    F(w) = 8ξ(1/2+√w) = Σ c_m w^m has **positive** coefficients (ξ(1/2+z) is an
    even function with a positive Maclaurin series in z²), so a single term
    cannot exceed the whole sum: for every ρ > 0,

        c_m ≤ F(ρ)/ρ^m.

    The aliasing error of an N-point equispaced DFT in the n-th coefficient is
    Σ_{k≥1} c_{n+kN} R^{kN}; with the bound above and ρ > R that is at most
    F(ρ)ρ^{−n}(R/ρ)^N/(1−(R/ρ)^N), and measured *relative to c_n* it is worst
    at n = 0 where c_0 = γ(0).  Demanding it stay below 10^{−work} gives

        N ≥ [work + log₁₀(F(ρ)/γ(0))] / log₁₀(ρ/R) ,

    minimised over ρ = λR on :data:`_ALIAS_LAMBDAS`.  (The 1/(1−(R/ρ)^N) is
    dropped: it is 1 + O(10^{−work}).)  Costs nine ξ evaluations at 20 digits
    (~0.03 s), which is nothing next to the pass itself.  The floor
    ``2·n_max + 40`` also covers the hard requirement N > n_max, without which
    the DFT cannot separate the coefficients at all.

    Why this exists: the previous rule was the radius-blind ``2·n_max + 40``,
    and it **silently lost digits**.  Measured against :func:`_gamma_integral`
    at dps = 80, that rule gave 2.36e-57 relative error at n_max = 12, R = 300
    (64 nodes) and 2.92e-35 at n_max = 4, R = 300 (48 nodes) — a function
    asked for 80 digits returning 34.  The derived count asks for 112 and 102
    nodes there and the output becomes bit-identical again.  At the default
    R = 30 the floor still wins throughout dps = 30, and from n_max = 20 up at
    dps = 80, so the settings that already worked are untouched.
    """
    floor = 2 * n_max + 40
    with mp.workdps(20):
        R = mp.mpf(radius)
        g0 = 8 * xi(mp.mpf(1) / 2, 20)
        candidates = []
        for lam in _ALIAS_LAMBDAS:
            F = 8 * xi(mp.mpf(1) / 2 + mp.sqrt(R * lam), 20)
            candidates.append(
                int(mp.ceil((work + mp.log10(F / g0)) / mp.log10(mp.mpf(lam))))
            )
    return max(floor, min(candidates))


def _gamma_cauchy(n_max: int, dps: int, radius: Any = 30) -> list[mpf]:
    """γ(0) … γ(n_max) by Cauchy integration of F(w) = 8·ξ(1/2 + √w).

    F is single-valued because ξ(1/2+z) is even, entire of order 1/2, and
    F(w) = Σ γ(n) w^n/n!.  One equispaced trapezoid pass on |w| = ``radius``
    gives every coefficient.

    This is the *independent* path used to validate :func:`_gamma_integral`;
    it is the more expensive of the two because the n-th coefficient sits
    log₁₀(max|F| / (|c_n| R^n)) digits below the sampled values, so the working
    precision carries 2.6 extra digits per coefficient, and because the node
    count has to grow with both the working precision and the radius
    (:func:`_gamma_cauchy_nodes`).

    Two measurements, and they say different things — the first is the one that
    matters, the second is why the guard digits are what they are.

    * **At the settings this function actually uses**, the radius is irrelevant:
      the output is *bit-identical* to :func:`_gamma_integral` for every radius
      in {4, 10, 30, 100, 300} at dps = 30 and dps = 80, for n_max ∈
      {4, 12, 20, 30} — the whole 40-cell grid, pinned by
      ``test_gamma_cauchy_radius_independence``.  (With the old radius-blind
      node count three of those cells lost up to 45 digits; see
      :func:`_gamma_cauchy_nodes`.)
    * **Starve the working precision and the trade-off appears.**  Re-running
      the inner loop by hand at a fixed ``work = 80`` digits with a fixed node
      count, against a dps = 110 reference, max relative error over n ≤ 20:

      ========  =======  =========
      radius    nodes    max rel err
      ========  =======  =========
      30        80       1.2e-58
      10        30       1.1e-47
      30        30       1.5e-44
      4         30       1.2e-39
      100       30       7.5e-29
      ========  =======  =========

      i.e. both too-small and too-large a radius cost digits (small R shrinks
      R^n against max|F|; large R inflates max|F| = max|8ξ(1/2+√w)| far faster),
      and starving the node count costs ~14 digits on its own.  The default
      R = 30 sits at the flat bottom, and the node count is no longer a fixed
      2n+40: :func:`_gamma_cauchy_nodes` raises it as the radius or the working
      precision grows, which is what removes the radius dependence entirely at
      the settings above.  (Pinned by
      ``test_gamma_cauchy_starved_precision_tradeoff_table``.)

    **Cancellation audit, and the radius ceiling it exposes.**  ``work`` is
    ``dps + 20 + ⌈2.6·n_max⌉``, a rule calibrated at R ≈ 30, and it is *blind to
    the radius* — so for a large enough circle the coefficients drown in the
    round-off of the DFT sum.  Every coefficient is therefore checked against
    the round-off floor max|F|·R^{−n}·10^{−work} before being returned, and the
    function raises rather than quietly handing back garbage.  Measured spare
    digits beyond the requested ``dps`` (independent of ``dps``, since ``work``
    tracks it):

    ==========  =====  =====  =====  =====  =====
    n_max       R=4    R=10   R=30   R=100  R=300
    ==========  =====  =====  =====  =====  =====
    4           25.3   26.8   28.5   30.0   28.4
    12          29.4   34.2   39.7   45.3   49.4
    30          27.9   39.8   53.9   68.9   81.6
    ==========  =====  =====  =====  =====  =====

    At n_max = 4, R = 1000 still has 23.8 spare; R = 10 000 raises.  Without
    the check, R = 100 000 returned γ(0) wrong by a factor of 3e138.
    """
    R = mp.mpf(radius)
    if R <= 0:
        raise ValueError("radius must be positive")
    work = dps + 2 * _GUARD + int(math.ceil(2.6 * n_max))
    n_points = _gamma_cauchy_nodes(n_max, work, radius)
    with mp.workdps(work):
        Rw = mp.mpf(radius)
        w = _roots_of_unity(n_points)
        F = [
            8 * xi(mp.mpf(1) / 2 + mp.sqrt(Rw * wj), work) for wj in w
        ]
        # max|F| on |w| = R is F(R) itself: F has positive coefficients, so
        # |F(w)| <= sum c_m |w|^m = F(R).  Taking the sampled max costs nothing
        # and keeps the bound honest if that ever stops being true.
        biggest = max(abs(v) for v in F)
        out = []
        for n in range(n_max + 1):
            acc = mp.fsum(F[j] * w[(-(j * n)) % n_points] for j in range(n_points))
            inv = mp.power(Rw, -n)
            c_n = acc * inv / n_points
            value = _real_checked(
                c_n, work, 2 * _GUARD, f"gamma({n})", scale=biggest * inv
            )
            # Cancellation audit.  The round-off floor of the DFT sum is
            # max|F|·10^{−work}; dividing by R^n carries it up to
            # max|F|·R^{−n}·10^{−work}.  The coefficient is only good to
            # ``dps`` digits if that floor sits ``dps`` decades below it.  This
            # is the check that ``work = dps + 20 + 2.6·n_max`` — a rule
            # calibrated at R ≈ 30 — is still adequate at the radius asked for.
            floor = biggest * inv * mp.mpf(10) ** (-work)
            if value == 0 or floor > abs(value) * mp.mpf(10) ** (-dps):
                raise ValueError(
                    f"gamma({n}) at radius {radius}: the DFT round-off floor "
                    f"{mp.nstr(floor, 4)} is not {dps} decades below the "
                    f"coefficient {mp.nstr(abs(value), 4)}; max|F| = "
                    f"{mp.nstr(biggest, 4)} on this circle is too large for the "
                    "working precision (use a smaller radius or a larger dps)"
                )
            out.append(mp.factorial(n) * value)
    return [_shrink(v, dps) for v in out]


def xi_taylor_coefficients(
    n_max: int,
    dps: int = DPS_DEFAULT,
    method: str = "integral",
    cache: bool = True,
) -> list[mpf]:
    """The coefficients γ(0) … γ(n_max) of the Jensen-polynomial sequence:

        8·ξ(1/2 + z)  =  Σ_{n≥0} γ(n) z^{2n} / n!.

    This is the Griffin–Ono–Rolen–Zagier normalisation, whose usual statement
    is (−1 + 4z²)·Λ(1/2+z) = Σ γ(n) z^{2n}/n! with Λ = π^{−s/2}Γ(s/2)ζ(s).
    The two agree because ξ = ½s(s−1)Λ and (1/2+z)(z−1/2) = z² − 1/4, so
    (−1+4z²)Λ(1/2+z) = 4(z²−1/4)·2ξ(1/2+z)/(z²−1/4) = 8ξ(1/2+z) — a factor
    the module *derives* rather than quotes.

    All γ(n) are positive (ξ(1/2+z) has a Maclaurin series in z² with positive
    coefficients) and decay like 1/n!:

        γ(0) = 3.9769662255065128793…  = 8·ξ(1/2)
        γ(1) = 0.09188777726058175014…
        γ(2) = 0.001975232289125088110…
        γ(10) = 1.6323380490301419585e-17
        γ(25) = 5.8107957154993911706e-46

    ``method="integral"`` (default) uses Riemann's Mellin representation —
    positive integrands, no radius, no aliasing (see :func:`_gamma_integral`).
    ``method="cauchy"`` is the independent second path (:func:`_gamma_cauchy`),
    Cauchy integration of 8·ξ(1/2+√w) — no Mellin representation, no ω.  The
    two share nothing but ξ itself, and they return **bit-identical** values
    over the whole grid the tests pin: n_max ∈ {4, 12, 20, 30} × dps ∈ {30, 80}
    × radius ∈ {4, 10, 30, 100, 300}, plus n ≤ 20 at dps = 30 and 50 on the
    default circle.  A third, wholly independent route — Riemann's ω′ form of
    the Ξ integral — reproduces γ(0…8) to 9.2e-32 relative and the committed
    n = 128 table to 4.7e-32 (``tests/test_li.py``).

    Cached under ``data/li_gamma_*.json``.
    """
    n_max = int(n_max)
    if n_max < 0:
        raise ValueError("n_max must be >= 0")
    if method not in ("integral", "cauchy"):
        raise ValueError(f"unknown method {method!r} (use 'integral' or 'cauchy')")
    if not cache:
        engine = _gamma_integral if method == "integral" else _gamma_cauchy
        return engine(n_max, dps)
    hit = _load_table("gamma", n_max, dps, method=method)
    if hit is not None:
        return hit[: n_max + 1]
    n_store = _round_up(n_max)
    engine = _gamma_integral if method == "integral" else _gamma_cauchy
    out = engine(n_store, dps)
    try:
        _save_table("gamma", out, n_store, dps, method=method)
    except OSError:  # pragma: no cover - read-only fs
        pass
    return out[: n_max + 1]


# ===========================================================================
# 3.  Jensen polynomials and hyperbolicity
# ===========================================================================


def jensen_polynomial(
    d: int,
    n: int,
    dps: int = DPS_DEFAULT,
    gammas: Sequence | None = None,
    normalise: bool = False,
) -> list[mpf]:
    """Coefficients of the Jensen polynomial

        J^{d,n}(X) = Σ_{j=0}^{d} C(d,j) γ(n+j) X^j,

    returned in **ascending** order: ``out[j]`` multiplies ``X**j``.

    ``normalise=True`` returns instead the coefficients of
    J^{d,n}(sX)/γ(n) with s = γ(n)/γ(n+1), i.e. ``out[0] = 1`` and
    ``out[1] = d``.  Hyperbolicity is invariant under X ↦ sX for s > 0 and
    under an overall positive scaling, so this is the *same* question asked of
    a numerically sane polynomial.  Measured coefficient spans
    log₁₀(max|c|/min|c|):

    ======  ======  ==========  ==========
    d       n       raw         normalised
    ======  ======  ==========  ==========
    8       0       10^13.8     10^2.4
    8       10      10^14.9     10^2.1
    16      0       10^28.5     10^5.9
    16      10      10^30.4     10^5.0
    ======  ======  ==========  ==========

    i.e. ~28–30 orders raw by d = 16 against ~5 normalised.  (The d = 8 and
    d = 16, n = 0 rows are pinned by
    ``tests/test_li.py::test_balance_conditioning_spans_on_real_jensen_polynomials``.)

    ``gammas`` lets a caller supply a precomputed γ table (needs at least
    n + d + 2 entries) so that a scan pays for it once.
    """
    d, n = int(d), int(n)
    if d < 1:
        raise ValueError("d must be >= 1")
    if n < 0:
        raise ValueError("n must be >= 0")
    if gammas is None:
        gammas = xi_taylor_coefficients(n + d + 1, dps=dps)
    if len(gammas) < n + d + 1:
        raise ValueError(
            f"need gamma(0..{n + d}) but only {len(gammas)} coefficients supplied"
        )
    with mp.workdps(dps + _GUARD):
        coeffs = [mp.binomial(d, j) * gammas[n + j] for j in range(d + 1)]
        if normalise:
            s = gammas[n] / gammas[n + 1]
            coeffs = [c * mp.power(s, j) / gammas[n] for j, c in enumerate(coeffs)]
    return [_shrink(c, dps) for c in coeffs]


def _to_rational(x):
    """Exact sympy Rational for an mpf (mpf values *are* dyadic rationals).

    The ``isinstance`` guard is load-bearing, not defensive: ``mp.mpf(x)`` on a
    value that is *already* an mpf **re-rounds it to the ambient precision**.
    Doing that here silently replaced every coefficient by its 15-digit
    rounding before the "exact" Sturm count ran — which turned the near-miss
    control X² − 2X + (1 + 10^{−36}) into the perfect square (X−1)², i.e. into a
    *hyperbolic* verdict.  ``tests/test_li.py`` pins that control.
    """
    import sympy

    v = x if isinstance(x, mpf) else mp.mpf(x)
    p, q = mpmath.libmp.to_rational(v._mpf_)
    return sympy.Rational(p, q)


def _balance(coeffs: Sequence) -> tuple[list, Any]:
    """Rescale X ↦ sX so the extreme coefficients have comparable magnitude.

    s = (|a_0|/|a_d|)^{1/d} is the classical root-magnitude estimate; after the
    substitution the coefficients are normalised by their largest.  A positive
    scaling is a bijection of the real line, so hyperbolicity is untouched —
    but the conditioning of the root finder improves enormously: measured on
    J^{16,0}, the raw coefficients span 10^28.5 and the ones already normalised
    by :func:`jensen_polynomial` span 10^5.9 (for J^{8,0}: 10^13.8 → 10^2.4).
    """
    a0, ad = coeffs[0], coeffs[-1]
    d = len(coeffs) - 1
    if a0 == 0 or ad == 0 or d < 1:
        s = mp.mpf(1)
    else:
        s = mp.power(abs(a0) / abs(ad), mp.mpf(1) / d)
    scaled = [c * mp.power(s, j) for j, c in enumerate(coeffs)]
    biggest = max(abs(c) for c in scaled)
    if biggest > 0:
        scaled = [c / biggest for c in scaled]
    return scaled, s


def is_hyperbolic(
    poly_coeffs: Sequence,
    dps: int = DPS_DEFAULT,
    method: str = "both",
    tol: float | None = None,
) -> dict:
    """Is a real polynomial *hyperbolic* — i.e. are all of its roots real?

    ``poly_coeffs`` is in **ascending** order (``poly_coeffs[j]`` multiplies
    ``X**j``), matching :func:`jensen_polynomial`.

    Returns ``{'hyperbolic', 'max_abs_imag', 'roots', 'degree',
    'max_rel_imag', 'min_gap', 'n_real_exact', 'method', 'agree'}`` where the
    roots are those of the *original* polynomial (the internal balancing is
    undone).

    Two tests, and by default both are run:

    ``"roots"``  — mpmath's Durand–Kerner on the balanced polynomial; hyperbolic
    iff max |Im root| / max |root| < ``tol`` (default 10^{−dps/2}).  This is a
    *tolerance* test, and a tolerance test can be fooled by a complex pair with
    a tiny imaginary part.  ``max_rel_imag`` is reported so the caller can see
    how far from the boundary the verdict was.

    ``"sturm"``  — exact.  An ``mpf`` is a dyadic rational, so the polynomial
    held in memory converts to ℚ[X] *without error*; sympy's Sturm-sequence
    real-root count on its square-free part is then a decision procedure.
    ``n_real_exact`` is that count.  **Caveat, stated plainly**: this certifies
    the rational polynomial actually in memory, whose coefficients differ from
    the true γ(n) by ~10^{−dps}; the conclusion transfers to the true
    polynomial only when the roots are separated by more than that
    perturbation, which ``min_gap`` quantifies — the smallest gap between
    consecutive root real parts *divided by the largest root modulus*, i.e. a
    scale-free (relative) separation, computed in the balanced variable.

    Coefficients must be real: a complex one raises ``ValueError`` rather than
    letting the Sturm branch fail obscurely.

    ``method="both"`` (default) runs both and sets ``agree``; the returned
    ``hyperbolic`` is then the exact (Sturm) verdict.

    Control: ``is_hyperbolic([1, 0, 1])`` — the polynomial X² + 1 — returns
    ``hyperbolic=False``, ``max_abs_imag=1.0``, ``n_real_exact=0``.
    """
    coeffs = list(poly_coeffs)
    if len(coeffs) < 2:
        raise ValueError("need a polynomial of degree at least 1")
    work = dps + 2 * _GUARD
    with mp.workdps(work):
        real_coeffs = []
        for c in coeffs:
            v = mp.mpmathify(c)
            if isinstance(v, mp.mpc):
                if mp.im(v) != 0:
                    raise ValueError(
                        "is_hyperbolic needs a polynomial with real coefficients; "
                        "hyperbolicity is a statement about real polynomials and "
                        "the exact Sturm branch has no meaning otherwise"
                    )
                v = mp.mpf(mp.re(v))
            real_coeffs.append(v)
        coeffs = real_coeffs
        while len(coeffs) > 1 and coeffs[-1] == 0:
            coeffs.pop()
        degree = len(coeffs) - 1
        if degree < 1:
            raise ValueError("need a polynomial of degree at least 1")
        scaled, s = _balance(coeffs)
        roots = mp.polyroots(
            list(reversed(scaled)), maxsteps=500, extraprec=40 * degree + 200,
            cleanup=False,
        )
        roots = sorted(roots, key=lambda r: (mp.re(r), mp.im(r)))
        max_abs = max(abs(r) for r in roots)
        max_im = max(abs(mp.im(r)) for r in roots)
        rel_im = float(max_im / max_abs) if max_abs > 0 else 0.0
        res = sorted(float(mp.re(r)) for r in roots)
        min_gap = (
            min(b - a for a, b in zip(res, res[1:])) / float(max_abs)
            if degree > 1 and max_abs > 0
            else float("inf")
        )
        true_roots = [_shrink(r * s, dps) for r in roots]
        max_abs_imag = float(max(abs(mp.im(r)) for r in true_roots))

    tol_v = 10.0 ** (-dps / 2.0) if tol is None else float(tol)
    verdict_roots = rel_im < tol_v

    n_real = None
    verdict_sturm = None
    if method in ("sturm", "both"):
        import sympy

        X = sympy.Symbol("X")
        # **The input coefficients, not the balanced ones.**  ``_balance``
        # multiplies by ``mp.power(s, j)`` at ``work`` digits, which *rounds*:
        # feeding ``scaled`` to Sturm made the "exact" branch decide a
        # different polynomial from the one the caller passed.  Measured
        # (2026-08-11): X² − 2X + (1 + 10^{−45}), which has no real root,
        # came back ``hyperbolic=True, n_real_exact=1`` at dps 15 and 20 — and
        # ``agree=True``, because the root finder was fooled identically, so
        # the disagreement flag could not fire.  ``_to_rational``'s guard
        # prevented a *second* re-rounding; the first one happened here.
        # X ↦ sX with s > 0 is a bijection of the real line, so the Sturm count
        # needs no balancing at all — only the root finder does.
        with mp.workdps(work):
            rats = [_to_rational(c) for c in coeffs]
        poly = sympy.Poly(sum(r * X ** j for j, r in enumerate(rats)), X)
        sqf = poly.sqf_part()
        n_real = int(sqf.count_roots())
        verdict_sturm = n_real == sqf.degree()
    if method == "roots":
        hyperbolic, agree = verdict_roots, None
    elif method == "sturm":
        hyperbolic, agree = verdict_sturm, None
    elif method == "both":
        hyperbolic = verdict_sturm
        agree = bool(verdict_sturm == verdict_roots)
    else:
        raise ValueError(f"unknown method {method!r} (use 'roots', 'sturm', 'both')")

    return {
        "hyperbolic": bool(hyperbolic),
        "max_abs_imag": max_abs_imag,
        "max_rel_imag": rel_im,
        "roots": true_roots,
        "degree": degree,
        "min_gap": min_gap,
        "n_real_exact": n_real,
        "method": method,
        "agree": agree,
        "tol": tol_v,
    }


def hyperbolicity_scan(
    d_max: int,
    n_max: int,
    dps: int = DPS_DEFAULT,
    method: str = "roots",
    d_min: int = 1,
) -> list[dict]:
    """The (d, n) hyperbolicity table — "the infinite Routh table", made finite.

    For every degree d in ``d_min … d_max`` and every shift n in ``0 … n_max``,
    build J^{d,n} (in the normalised variable, see :func:`jensen_polynomial`)
    and decide hyperbolicity with :func:`is_hyperbolic`.  Rows are
    ``{'d', 'n', 'hyperbolic', 'max_rel_imag', 'min_gap', 'n_real_exact'}``.

    **Pólya's criterion is an equivalence**, so a single ``False`` here would
    *refute* RH.  Correspondingly, an all-``True`` table means only "no
    violation found in this range" — never support for RH (``docs/08``).
    Measured on this machine at ``dps=30``: every (d, n) with 1 ≤ d ≤ 16 and
    0 ≤ n ≤ 25 (416 rows, ~41 s) is hyperbolic, with relative max |Im root| ≤
    3.722e-104 and smallest relative root gap 0.04316 — the roots come out real
    to far beyond the working precision, and well separated, which is what
    "comfortably hyperbolic" looks like.

    ``method="roots"`` (default) is the fast tolerance test; ``"sturm"`` and
    ``"both"`` run the exact Sturm count as well, at roughly 2x the cost.
    """
    d_max, n_max, d_min = int(d_max), int(n_max), int(d_min)
    gammas = xi_taylor_coefficients(n_max + d_max + 1, dps=dps)
    rows = []
    for d in range(max(1, d_min), d_max + 1):
        for n in range(0, n_max + 1):
            coeffs = jensen_polynomial(d, n, dps=dps, gammas=gammas, normalise=True)
            info = is_hyperbolic(coeffs, dps=dps, method=method)
            rows.append(
                {
                    "d": d,
                    "n": n,
                    "hyperbolic": info["hyperbolic"],
                    "max_rel_imag": info["max_rel_imag"],
                    "min_gap": info["min_gap"],
                    "n_real_exact": info["n_real_exact"],
                }
            )
    return rows


def _hermite_roots(d: int, dps: int) -> list[float]:
    """Roots of the (physicists') Hermite polynomial H_d, ascending."""
    import sympy

    X = sympy.Symbol("X")
    poly = sympy.Poly(sympy.hermite(d, X), X)
    return sorted(float(r) for r in poly.nroots(n=max(20, dps)))


def _standardise(values: Sequence[float]) -> list[float]:
    """Affine map to mean 0, sample standard deviation 1 (population form)."""
    m = sum(values) / len(values)
    var = sum((v - m) ** 2 for v in values) / len(values)
    sd = math.sqrt(var)
    if sd == 0:  # pragma: no cover - impossible for distinct roots
        return [0.0] * len(values)
    return [(v - m) / sd for v in values]


def jensen_roots_vs_gue(
    d: int, n: int, dps: int = DPS_DEFAULT, gammas: Sequence | None = None
) -> dict:
    """Compare the roots of J^{d,n} with the roots of the Hermite polynomial H_d.

    Griffin–Ono–Rolen–Zagier (2019) prove that, for fixed d, a suitable affine
    renormalisation of J^{d,n} converges as n → ∞ to H_d — so the Jensen roots
    approach the Hermite roots, whose empirical measure is the semicircle law
    and which are the classical "GUE side" of this picture (the Hermite
    polynomials are the orthogonal polynomials of the Gaussian Unitary
    Ensemble weight e^{−x²}).

    Because the theorem's normalisation is affine, this function compares
    *standardised* root vectors — each shifted to mean 0 and scaled to unit
    standard deviation — which removes the normalisation entirely and leaves
    only the shape.  Returns ``{'d', 'n', 'roots', 'roots_standardised',
    'hermite_roots', 'hermite_standardised', 'max_deviation',
    'rms_deviation'}``.

    Measured max deviation (this is a *slow* convergence, and the numbers say
    so honestly):

    ====  =======  =======  =======  =======
    d     n = 10   n = 20   n = 40   n = 110
    ====  =======  =======  =======  =======
    3     0.0339   0.0329   0.0294   0.0223
    4     0.0350   0.0337   0.0300   0.0226
    6     0.0681   0.0648   0.0574   0.0434
    ====  =======  =======  =======  =======

    d = 2 is exact for every n by symmetry (any two distinct points standardise
    to ∓1, as do the two roots of H₂): measured deviation 0 … 1.6e-15 over
    n ∈ {7, 10, 20, 40, 110}, i.e. double-precision round-off.
    """
    d, n = int(d), int(n)
    if d < 2:
        raise ValueError("the Hermite comparison needs d >= 2")
    coeffs = jensen_polynomial(d, n, dps=dps, gammas=gammas, normalise=True)
    info = is_hyperbolic(coeffs, dps=dps, method="roots")
    roots = sorted(float(mp.re(r)) for r in info["roots"])
    herm = _hermite_roots(d, dps)
    rs, hs = _standardise(roots), _standardise(herm)
    dev = [abs(a - b) for a, b in zip(rs, hs)]
    return {
        "d": d,
        "n": n,
        "hyperbolic": info["hyperbolic"],
        "roots": roots,
        "roots_standardised": rs,
        "hermite_roots": herm,
        "hermite_standardised": hs,
        "max_deviation": max(dev),
        "rms_deviation": math.sqrt(sum(x * x for x in dev) / len(dev)),
    }
