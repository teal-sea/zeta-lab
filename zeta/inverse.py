"""Inverse spectral theory: the Wu–Sprung potential, and what it cannot show.

Hilbert–Pólya as an experiment.  If the zero ordinates γₙ were the spectrum
of a Schrödinger operator −ψ″ + V(x)ψ = Eψ, semiclassical quantization ties
the eigenvalue counting function to the potential by

    N(E) ≈ (1/π) ∫ √(E − V(x))₊ dx + 1/2,

and for a symmetric single-well V this Abel integral equation inverts in
closed form (Wu & Sprung, Phys. Rev. E 48 (1993) 2595):

    x(V) = ∫_{E₀}^{V} N̄′(E) / √(V − E) dE ,

where the Maslov 1/2 drops out under the derivative.  Feeding in the smooth
zero-counting density N̄′(E) = (1/2π)·log(E/2π) produces the smooth
Wu–Sprung well; adding the oscillating part of the staircase (a mollified
sum over actual ordinates) adds the famous fractal wiggles that pull the
eigenvalues from the *average* zero positions toward the *actual* ones.

House discipline applied to a folklore construction:

* The Abel inversion and the finite-difference forward solver are each
  **calibrated on the harmonic oscillator**, where both directions are
  exact (`harmonic_calibration`): V = x² must come back from the counting
  function N̄(E) = E/2 + 1/2, and the forward solve must return
  E_n = 2n + 1.  Nothing about ζ enters the calibration.
* Everything returns measured defects, never booleans.
* **The battery point is the point** (`docs/09` gate #3): the identical
  pipeline run on the Davenport–Heilbronn on-line ordinates, a function
  that *violates* RH, produces an equally serviceable potential
  (`spectrum_report(source="dh")`).  The Abel inversion consumes only a
  list of real ordinates; it cannot see the off-line zeros at all.  So
  "a Hamiltonian with the right spectrum exists" distinguishes nothing:
  the Hilbert–Pólya content, if any, must live in *properties* of the
  operator (a natural derivation, an arithmetic structure in V, a trace
  formula), not in its existence.  This module makes that folklore
  observation a measured fact.

Everything here is *accurate*, not *certified* (float pipeline; see
`zeta/rigor.py` for the reserved word).
"""

from __future__ import annotations

import json
import os
from typing import Any, Callable, Sequence

import numpy as np
from mpmath import mp

from .zeros import first_n_zeros

DATA_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data")

__all__ = [
    "abel_reconstruct",
    "harmonic_calibration",
    "wu_sprung_potential",
    "schrodinger_eigenvalues",
    "spectrum_report",
    "dh_online_ordinates",
]

TWO_PI = 2.0 * np.pi


# ----------------------------------------------------------------------
# The Abel inversion
# ----------------------------------------------------------------------

def abel_reconstruct(
    nbar_prime: Callable[[np.ndarray], np.ndarray],
    V_values: np.ndarray,
    E0: float,
    n_quad: int = 400,
) -> np.ndarray:
    """x(V) = ∫_{E₀}^{V} N̄′(E)/√(V−E) dE for each V in ``V_values``.

    The substitution E = V − w² removes the endpoint singularity:
    x(V) = 2 ∫₀^{√(V−E₀)} N̄′(V − w²) dw, then Gauss–Legendre in w.
    """
    nodes, weights = np.polynomial.legendre.leggauss(n_quad)
    V = np.asarray(V_values, dtype=float)
    x = np.empty_like(V)
    for i, v in enumerate(V):
        if v <= E0:
            x[i] = 0.0
            continue
        wmax = np.sqrt(v - E0)
        w = 0.5 * wmax * (nodes + 1.0)
        x[i] = 2.0 * (0.5 * wmax) * float(np.dot(weights, nbar_prime(v - w * w)))
    return x


def harmonic_calibration(n_eigs: int = 12, grid_n: int = 6000) -> dict[str, Any]:
    """Calibrate both directions on the harmonic oscillator, where truth is exact.

    Inverse: N̄(E) = E/2 + 1/2 (exact for V = x², in units −ψ″ + Vψ = Eψ)
    has N̄′ = 1/2, and the Abel formula must return x(V) = √V, i.e. V = x².
    Forward: the finite-difference eigenvalues of V = x² must be 1, 3, 5, …
    """
    V_grid = np.linspace(0.25, 40.0, 60)
    x = abel_reconstruct(lambda E: np.full_like(E, 0.5), V_grid, E0=0.0)
    inverse_defect = float(np.max(np.abs(x - np.sqrt(V_grid))))

    L = np.sqrt(60.0)  # classical turning point of E≈40, plus margin
    eigs = schrodinger_eigenvalues(lambda xs: xs * xs, L=L + 3.0, n_grid=grid_n, k=n_eigs)
    target = 2.0 * np.arange(n_eigs) + 1.0
    forward_defect = float(np.max(np.abs(eigs - target)))
    return {
        "inverse_max_defect": inverse_defect,
        "forward_max_defect": forward_defect,
        "eigenvalues": eigs.tolist(),
        "passed": inverse_defect < 1e-10 and forward_defect < 5e-4,
    }


# ----------------------------------------------------------------------
# Counting densities: smooth mean parts, and the mollified staircase
# ----------------------------------------------------------------------

def _zeta_nbar_prime(E: np.ndarray) -> np.ndarray:
    """(1/2π)·log(E/2π), the derivative of the Riemann–von Mangoldt mean
    N̄(T) = (T/2π)log(T/2πe) + 7/8; the 1/(48T) tail of ϑ is negligible
    beyond E₀ = 2π and is checked against ``zeta.core.rs_theta`` in tests."""
    return np.log(np.asarray(E, dtype=float) / TWO_PI) / TWO_PI


def _dh_nbar_prime(E: np.ndarray) -> np.ndarray:
    """DH mean density: N̄′(E) = (1/2π)·log(5E/2π).

    Derived, not remembered: finite differences of ``zeta.epstein.dh_theta``
    give ϑ′_dh(8) = 0.9248, ϑ′_dh(30) = 1.5863, ϑ′_dh(100) = 2.1884, and
    (1/2)log(5E/2π) reproduces all three to ≤ 1e-3 (the residue is the
    O(1/E²) phase tail).  A first guess with √5 in place of 5 missed by the
    constant log √5 ≈ 0.4024, the conductor enters the density in full.
    Pinned against dh_theta in tests/test_inverse.py."""
    return np.log(5.0 * np.asarray(E, dtype=float) / TWO_PI) / TWO_PI


def _mollified_osc_prime(
    ordinates: np.ndarray,
    nbar: Callable[[np.ndarray], np.ndarray],
    delta: float,
) -> Callable[[np.ndarray], np.ndarray]:
    """N′_osc as a function: Gaussian-mollified staircase minus the mean.

    N′_δ(E) = Σₙ φ_δ(E − γₙ) − N̄′(E), with φ_δ the unit Gaussian of width
    δ.  Only meaningful for E inside the window covered by ``ordinates``;
    the caller keeps V_max below the last ordinate minus a few δ.
    """
    g = np.asarray(ordinates, dtype=float)
    norm = 1.0 / (delta * np.sqrt(2.0 * np.pi))

    def osc(E: np.ndarray) -> np.ndarray:
        E = np.atleast_1d(np.asarray(E, dtype=float))
        z = (E[:, None] - g[None, :]) / delta
        staircase = norm * np.exp(-0.5 * z * z).sum(axis=1)
        return staircase - nbar(E)

    return osc


# ----------------------------------------------------------------------
# The potentials
# ----------------------------------------------------------------------

def wu_sprung_potential(
    V_max: float = 120.0,
    n_grid: int = 1600,
    ordinates: Sequence[float] | None = None,
    delta: float = 2.5,
    source: str = "zeta",
) -> dict[str, Any]:
    """The (half-)potential as monotone samples x(V), V ∈ [E₀, V_max].

    Without ``ordinates``: the smooth well from the mean counting density.
    With ``ordinates``: the fractal correction is added, the mollified
    oscillating density enters the same Abel integral.  Returns x and V
    arrays (symmetric extension V(−x) = V(x) is the caller's convention),
    plus the reconstruction parameters for provenance.
    """
    if source == "zeta":
        nbar, E0 = _zeta_nbar_prime, TWO_PI
    elif source == "dh":
        nbar, E0 = _dh_nbar_prime, TWO_PI / 5.0
    else:
        raise ValueError("source must be 'zeta' or 'dh'")

    V_grid = np.linspace(E0 + 1e-9, V_max, n_grid)
    x_smooth = abel_reconstruct(nbar, V_grid, E0=E0)
    x = x_smooth.copy()
    if ordinates is not None:
        osc = _mollified_osc_prime(np.asarray(ordinates, float), nbar, delta)
        x = x + abel_reconstruct(osc, V_grid, E0=E0)
        # A large enough wiggle can break monotonicity of x(V); the forward
        # solver only needs V(x) single-valued, so report the defect and
        # enforce monotonicity by isotonic clipping rather than hiding it.
        mono_defect = float(np.max(np.maximum(0.0, -np.diff(x))))
        x = np.maximum.accumulate(x)
    else:
        mono_defect = 0.0
    return {
        "V": V_grid,
        "x": x,
        "x_smooth": x_smooth,
        "E0": float(E0),
        "delta": float(delta) if ordinates is not None else None,
        "n_ordinates": 0 if ordinates is None else len(ordinates),
        "monotonicity_defect": mono_defect,
        "source": source,
    }


def _potential_interpolant(pot: dict[str, Any]) -> Callable[[np.ndarray], np.ndarray]:
    """V(|x|) by monotone interpolation of the (x, V) samples; below the
    first sample the well bottom E₀ is used, beyond the last it extends by
    the smooth well's local slope (only eigenvalues well under V_max are
    trusted, enforced by the caller)."""
    xs, Vs, E0 = pot["x"], pot["V"], pot["E0"]

    slope = (Vs[-1] - Vs[-2]) / max(xs[-1] - xs[-2], 1e-12)

    def V(x: np.ndarray) -> np.ndarray:
        ax = np.abs(np.asarray(x, dtype=float))
        out = np.interp(ax, xs, Vs, left=E0, right=Vs[-1])
        beyond = ax > xs[-1]
        if np.any(beyond):
            out = np.where(beyond, Vs[-1] + slope * (ax - xs[-1]), out)
        return out

    return V


def schrodinger_eigenvalues(
    V: Callable[[np.ndarray], np.ndarray],
    L: float,
    n_grid: int = 8000,
    k: int = 30,
    vectors: bool = False,
):
    """Lowest k eigenpairs of −ψ″ + V(x)ψ on [−L, L], Dirichlet ends.

    Standard second-order central differences on a uniform grid; the
    discretization error is measured against the harmonic oscillator in
    ``harmonic_calibration`` rather than assumed.  With ``vectors=True``
    returns (values, x_interior, eigenfunction columns).
    """
    from scipy.linalg import eigh_tridiagonal

    x = np.linspace(-L, L, n_grid)
    h = x[1] - x[0]
    diag = 2.0 / h**2 + V(x[1:-1])
    off = np.full(n_grid - 3, -1.0 / h**2)
    vals, vecs = eigh_tridiagonal(diag, off, select="i", select_range=(0, k - 1))
    if vectors:
        return vals, x[1:-1], vecs / np.sqrt(h)  # L² normalized on the grid
    return vals


def refine_potential(
    V_seed: Callable[[np.ndarray], np.ndarray],
    targets: np.ndarray,
    L: float,
    n_grid: int = 8000,
    iterations: int = 5,
    damping: float = 0.8,
) -> dict[str, Any]:
    """First-order inverse iteration: bend V until the spectrum hits ``targets``.

    Rayleigh–Schrödinger first order says a perturbation δV shifts E_j by
    ⟨ψ_j|δV|ψ_j⟩.  Expanding δV in the bump basis b_k = ψ_k² and solving the
    small linear system  A c = r,  A_jk = ⟨ψ_j², b_k⟩,  r_j = γ_j − E_j,
    then damping, converges in a few sweeps.  This is deliberately a
    *manufacturing* procedure: it will hit any reasonable target list,
    which is exactly the battery point its results are used to make.

    Basin caveat, measured: convergence needs the seed's eigenvalues within
    roughly one mean gap of the targets (the Wu–Sprung smooth well delivers
    ~0.2 gaps).  Seeding a ladder several gaps away diverges, first-order
    perturbation theory, not magic.

    Returns the refined potential on a grid plus the per-iteration RMS
    residual history (in absolute units).
    """
    x = None
    dV = None
    history: list[float] = []
    k = len(targets)
    for _ in range(iterations):
        def V_cur(xs: np.ndarray) -> np.ndarray:
            out = V_seed(xs)
            if dV is not None:
                out = out + np.interp(np.asarray(xs, float), x, dV, left=0.0, right=0.0)
            return out

        vals, x_int, vecs = schrodinger_eigenvalues(V_cur, L, n_grid, k, vectors=True)
        r = np.asarray(targets, float) - vals
        history.append(float(np.sqrt(np.mean(r**2))))
        h = x_int[1] - x_int[0]
        density = vecs**2  # columns ψ_k², each integrating to 1
        A = density.T @ density * h  # A_jk = ∫ ψ_j² ψ_k² dx
        c = np.linalg.solve(A, r)
        step = damping * (density @ c)
        if dV is None:
            x, dV = x_int, step
        else:
            dV = dV + step
    # final residual after the last update
    def V_fin(xs: np.ndarray) -> np.ndarray:
        return V_seed(xs) + np.interp(np.asarray(xs, float), x, dV, left=0.0, right=0.0)

    vals = schrodinger_eigenvalues(V_fin, L, n_grid, k)
    r = np.asarray(targets, float) - vals
    history.append(float(np.sqrt(np.mean(r**2))))
    return {
        "x": x,
        "dV": dV,
        "eigenvalues": vals.tolist(),
        "rms_history": history,
        "final_rms": history[-1],
    }


# ----------------------------------------------------------------------
# Davenport–Heilbronn on-line ordinates (the battery's fuel)
# ----------------------------------------------------------------------

def dh_online_ordinates(
    t_max: float = 120.0, cache: bool = True, coarse_step: float = 0.05
) -> list[float]:
    """Ordinates of Z_dh sign changes on (1, t_max], bisected to ~1e-12.

    Cached to ``data/dh_zeros_online_T<t_max>.json`` (the hunt costs ~100 s).
    Sign-change hunting can in principle miss a close pair; the count is
    cross-checked against ``zeta.epstein.zeros_on_line`` in the tests.
    Note these are the *on-line* zeros only, the whole battery point is
    that the off-line ones (first at t ≈ 85.7) are invisible here.
    """
    path = os.path.join(DATA_DIR, f"dh_zeros_online_T{int(round(t_max))}.json")
    if cache and os.path.exists(path):
        with open(path) as fh:
            blob = json.load(fh)
        if blob.get("coarse_step", 1.0) <= coarse_step:
            return [float(z) for z in blob["zeros"]]

    from .epstein import Z_dh

    zeros: list[float] = []
    t = mp.mpf(1)
    prev_t, prev_v = t, Z_dh(t)
    while t < t_max:
        t = t + coarse_step
        v = Z_dh(t)
        if (prev_v < 0) != (v < 0):
            a, b, fa = prev_t, t, prev_v
            for _ in range(50):
                m = (a + b) / 2
                fm = Z_dh(m)
                if (fa < 0) != (fm < 0):
                    b = m
                else:
                    a, fa = m, fm
            zeros.append(float((a + b) / 2))
        prev_t, prev_v = t, v
    if cache:
        os.makedirs(DATA_DIR, exist_ok=True)
        tmp = path + ".tmp"
        with open(tmp, "w") as fh:
            json.dump(
                {
                    "t_max": t_max,
                    "coarse_step": coarse_step,
                    "n_zeros": len(zeros),
                    "source": "sign changes of zeta.epstein.Z_dh, 50 bisections",
                    "zeros": zeros,
                },
                fh,
                indent=1,
            )
        os.replace(tmp, path)
    return zeros


# ----------------------------------------------------------------------
# The experiment
# ----------------------------------------------------------------------

def spectrum_report(
    source: str = "zeta",
    n_eigs: int = 25,
    n_ordinates: int = 60,
    delta: float = 2.5,
    V_max: float | None = None,
    n_grid: int = 8000,
) -> dict[str, Any]:
    """Reconstruct the potential (smooth and fractal), forward-solve both,
    and score the eigenvalues against the actual ordinates.

    Returns per-eigenvalue defects and two summary numbers:

    * ``rms_smooth``: RMS of (E_k − γ_k) for the smooth well, in units of
      the local mean gap: how far the *average* well already gets.
    * ``rms_fractal``, same for the wiggled well: what the actual staircase
      buys.  ``improvement`` is their ratio.

    ``source="dh"`` runs the identical pipeline on the Davenport–Heilbronn
    on-line ordinates; comparable scores there are the battery verdict.
    """
    if source == "zeta":
        gams = [float(g) for g in first_n_zeros(n_ordinates, dps=20)]
    elif source == "dh":
        gams = dh_online_ordinates()[:n_ordinates]
        if len(gams) < n_ordinates:
            raise ValueError(
                f"only {len(gams)} DH on-line ordinates cached; extend t_max"
            )
    else:
        raise ValueError("source must be 'zeta' or 'dh'")

    targets = np.array(gams[:n_eigs])
    if V_max is None:
        # keep every scored eigenvalue well inside the ordinate window
        V_max = gams[-1] * 0.85
    if targets[-1] > 0.9 * V_max:
        raise ValueError("n_eigs too large for the ordinate window")

    smooth = wu_sprung_potential(V_max=V_max, source=source)
    fractal = wu_sprung_potential(
        V_max=V_max, source=source, ordinates=gams, delta=delta
    )
    L = float(fractal["x"].max()) + 3.0
    E_smooth = schrodinger_eigenvalues(_potential_interpolant(smooth), L, n_grid, n_eigs)
    E_fractal = schrodinger_eigenvalues(_potential_interpolant(fractal), L, n_grid, n_eigs)

    refined = refine_potential(
        _potential_interpolant(fractal), targets, L=L, n_grid=n_grid
    )
    E_refined = np.array(refined["eigenvalues"])

    gaps = np.gradient(targets)
    d_smooth = (E_smooth - targets) / gaps
    d_fractal = (E_fractal - targets) / gaps
    d_refined = (E_refined - targets) / gaps
    rms_smooth = float(np.sqrt(np.mean(d_smooth**2)))
    rms_fractal = float(np.sqrt(np.mean(d_fractal**2)))
    rms_refined = float(np.sqrt(np.mean(d_refined**2)))
    return {
        "rms_refined": rms_refined,
        "eigs_refined": E_refined.tolist(),
        "refine_rms_history": refined["rms_history"],
        "source": source,
        "n_eigs": n_eigs,
        "n_ordinates": len(gams),
        "delta": delta,
        "V_max": float(V_max),
        "targets": targets.tolist(),
        "eigs_smooth": E_smooth.tolist(),
        "eigs_fractal": E_fractal.tolist(),
        "defect_smooth_gaps": d_smooth.tolist(),
        "defect_fractal_gaps": d_fractal.tolist(),
        "rms_smooth": rms_smooth,
        "rms_fractal": rms_fractal,
        "improvement": rms_smooth / rms_fractal if rms_fractal > 0 else np.inf,
        "monotonicity_defect": fractal["monotonicity_defect"],
        "note": (
            "existence of a serviceable potential for source='dh' is the "
            "battery verdict: the Abel inversion sees only real ordinates "
            "and cannot detect an RH violation (docs/09 gate #3)"
        ),
    }
