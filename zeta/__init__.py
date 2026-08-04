"""zeta-lab — a computational laboratory for the Riemann zeta function.

This package is an *instrument*, not a proof attempt: arbitrary-precision
machinery (mpmath) for ζ, θ, ξ, Ξ and Hardy's Z, zero hunting with
Turing-style counting certificates, the explicit formula rebuilding the
primes from the zeros, GUE spacing statistics, and heat flow on Ξ itself —
the de Bruijn–Newman constant Λ, where RH ⟺ Λ = 0 and Λ ≥ 0 is a theorem
(Rodgers–Tao 2018).

The organising chain, in one breath:

    θ(x) = Σ_{n∈ℤ} e^{−πn²x} is the heat kernel on ℝ/ℤ
      → Poisson summation gives the modular identity θ(1/x) = √x·θ(x)
      → whose Mellin transform is the functional equation ξ(s) = ξ(1−s)
      → whose mirror axis is Re(s) = 1/2 (the critical line)
      → and running the SAME heat equation on Ξ gives the family H_t,
        with Λ = inf{t : H_t has only real zeros} and RH ⟺ Λ = 0.

Modules
-------
:mod:`zeta.core`        ζ, η, Euler–Maclaurin, θ (Jacobi), ξ, Ξ, Z, Mellin.
:mod:`zeta.zeros`       zero finding, Gram points, N(T), verify_rh_up_to.
:mod:`zeta.explicit`    the explicit formula: ψ, π rebuilt from zeros; the
                        prime spectrum recovering zeros from primes.
:mod:`zeta.statistics`  unfolding, spacings vs GUE/Poisson, pair correlation.
:mod:`zeta.moments`     external zero windows, finite moments, gated scorecards.
:mod:`zeta.heatflow`    Φ, H_t, zero tracking, de Bruijn–Newman Λ facts.
:mod:`zeta.weil`        the Riemann–Weil explicit formula, Weil positivity.
:mod:`zeta.epstein`     the Davenport–Heilbronn counterexample battery.
:mod:`zeta.plots`       the twenty figures (imported lazily — matplotlib is
                        only loaded when a ``plot_*`` name is first touched).

Four further modules are **not** imported by ``import zeta`` — they pull in
heavier dependencies (Arb, sympy, bulk numpy) that purely numerical work does
not need.  Import them explicitly:

:mod:`zeta.rigor`       ball arithmetic: enclosures of Z, proven signs,
                        certified N(T), ``verify_rh_certified``.  The only
                        module in the package entitled to the word *certified*.
:mod:`zeta.li`          Li's criterion (λ_n) and Jensen polynomials.
:mod:`zeta.finitefield` curves over F_p — the RH that is a theorem.
:mod:`zeta.criteria`    Mertens, Baez-Duarte, Robin/Lagarias, Speiser.

Naming trap — there are three different "theta"s in this subject:

* :func:`zeta.core.theta`          — Jacobi θ(x) = Σ e^{−πn²x} (the heat kernel);
* :func:`zeta.core.rs_theta`       — the Riemann–Siegel phase ϑ(t) in
                                     Z(t) = e^{iϑ(t)} ζ(½+it);
* :func:`zeta.explicit.theta_cheb` — Chebyshev's prime sum θ(x) = Σ_{p≤x} log p.

All three are re-exported here under those distinct names; nothing in this
package ever means more than one of them by ``theta``.

A fourth collision, in the import system rather than the mathematics:
``zeta.li`` is :func:`zeta.explicit.li`, the *logarithmic integral* — until
something executes ``import zeta.li``, after which Python rebinds the package
attribute to the *module* :mod:`zeta.li` (Li's criterion) and ``zeta.li(x)``
raises ``TypeError``.  Use ``zeta.explicit.li`` for the function and
``from zeta.li import …`` for the module; never rely on ``from zeta import li``.

Quickstart:  ``python scripts/06_tour.py``  (see README.md at the repo root).
"""

from __future__ import annotations

__version__ = "0.1.0"

# Submodules (zeta.plots is intentionally NOT imported here: it pulls in
# matplotlib, which is slow and unnecessary for purely numerical work.
# It is loaded lazily through __getattr__ below.)
from . import core, epstein, explicit, heatflow, moments, statistics, weil, zeros

# --- core: ζ and the completed functions ----------------------------------
from .core import (
    DATA_DIR,
    DPS_DEFAULT,
    Xi,
    Z,
    completed_zeta,
    eta,
    functional_equation_defect,
    omega,
    rs_theta,
    theta,
    theta_heat,
    theta_modular_defect,
    xi,
    zeta,
    zeta_euler_maclaurin,
)

# --- zeros: hunting and counting ------------------------------------------
from .zeros import (
    N_of_T,
    S_of_T,
    first_n_zeros,
    gram_law_violations,
    gram_point,
    gram_points,
    riemann_von_mangoldt,
    verify_rh_up_to,
    zeros_by_sign_change,
    zeros_from_scratch,
)

# --- explicit formula: zeros <-> primes -----------------------------------
from .explicit import (
    Li,
    R,
    first_zeros,
    li,
    mangoldt,
    pi_from_zeros,
    pi_true,
    prime_spectrum,
    psi_from_zeros,
    psi_true,
    spectrum_peaks,
    theta_cheb,
)

# --- statistics: GUE and the Montgomery-Odlyzko law -----------------------
from .statistics import (
    compare_to_random_matrix,
    gue_eigenvalues,
    gue_spacing_exact,
    montgomery_prediction,
    nearest_neighbour_spacings,
    pair_correlation,
    poisson_spacing,
    unfold,
    wigner_surmise_gue,
    zero_ordinates,
)

# --- external high-zero tables for the moments programme -----------------
from .moments import (
    ODLYZKO_TABLES,
    CriticalLineSampleTable,
    ExternalZeroTable,
    MomentError,
    MomentEstimate,
    MomentPolynomial,
    MomentReference,
    MomentScore,
    MomentScorecard,
    OdlyzkoTableSpec,
    ZeroTableError,
    estimate_moment,
    estimate_moment_from_samples,
    leading_moment_mean,
    load_lmfdb_zeros,
    load_critical_line_samples,
    load_odlyzko_zeros,
    moment_polynomial,
    moment_polynomial_mean,
    moment_reference,
    moment_scorecard,
)

# --- heat flow on Ξ: the de Bruijn-Newman constant ------------------------
from .heatflow import (
    H_t,
    Phi,
    Xi_reference,
    lambda_facts,
    polynomial_heat_flow,
    track_zeros,
    zeros_of_H_t,
)

# --- Weil: the Riemann-Weil explicit formula and Weil positivity ----------
from .weil import (
    autocorrelation_pair,
    explicit_formula_sides,
    fejer_pair,
    gaussian_pair,
    near_tightness_report,
    positivity_probe,
    weil_functional,
)

# --- epstein: the Davenport-Heilbronn counterexample battery --------------
from .epstein import (
    KAPPA_REF,
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    L_chi,
    Z_dh,
    battery,
    chi5,
    claim_functional_equation,
    claim_multiplicativity,
    completed_dh,
    count_zeros_box,
    dh_coefficient,
    dh_f,
    dh_functional_equation_defect,
    dh_interface,
    dh_mean_value_defect,
    dh_theta,
    find_offline_zero,
    kappa,
    zeros_on_line,
    zeta_interface,
)

# --- plots (lazy) ---------------------------------------------------------
#: Names served lazily from :mod:`zeta.plots` on first attribute access.
_PLOT_EXPORTS: tuple[str, ...] = (
    "plot_zeta_critical_line",
    "plot_hardy_Z",
    "plot_zeta_domain_coloring",
    "plot_theta_modularity",
    "plot_theta_heat_evolution",
    "plot_explicit_formula",
    "plot_prime_spectrum",
    "plot_spacing_histogram",
    "plot_pair_correlation",
    "plot_zero_counting",
    "plot_heatflow_trajectories",
    "plot_polynomial_root_repulsion",
    "plot_weil_positivity",
    "plot_offline_zero",
    "plot_certified_enclosures",
    "plot_li_coefficients",
    "plot_jensen_roots",
    "plot_finite_field_rh",
    "plot_sato_tate",
    "plot_mertens",
)


def __getattr__(name: str):
    """Lazily resolve ``zeta.plots`` and its figure functions (PEP 562)."""
    if name == "plots" or name in _PLOT_EXPORTS:
        import importlib

        plots = importlib.import_module(".plots", __name__)  # matplotlib, Agg
        globals()["plots"] = plots  # cache: later zeta.plots skips __getattr__
        return plots if name == "plots" else getattr(plots, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


def __dir__() -> list[str]:
    return sorted(set(globals()) | set(_PLOT_EXPORTS) | {"plots"})


__all__ = [
    "__version__",
    # constants
    "DPS_DEFAULT",
    "DATA_DIR",
    # core
    "zeta",
    "eta",
    "zeta_euler_maclaurin",
    "theta",
    "omega",
    "theta_modular_defect",
    "theta_heat",
    "xi",
    "Xi",
    "completed_zeta",
    "functional_equation_defect",
    "rs_theta",
    "Z",
    # zeros
    "first_n_zeros",
    "zeros_by_sign_change",
    "zeros_from_scratch",
    "gram_point",
    "gram_points",
    "gram_law_violations",
    "N_of_T",
    "S_of_T",
    "riemann_von_mangoldt",
    "verify_rh_up_to",
    # explicit formula
    "mangoldt",
    "psi_true",
    "theta_cheb",
    "pi_true",
    "li",
    "Li",
    "R",
    "first_zeros",
    "psi_from_zeros",
    "pi_from_zeros",
    "prime_spectrum",
    "spectrum_peaks",
    # statistics
    "zero_ordinates",
    "unfold",
    "nearest_neighbour_spacings",
    "wigner_surmise_gue",
    "gue_spacing_exact",
    "poisson_spacing",
    "pair_correlation",
    "montgomery_prediction",
    "gue_eigenvalues",
    "compare_to_random_matrix",
    # external high-zero tables and finite moment scorecards
    "ExternalZeroTable",
    "OdlyzkoTableSpec",
    "ZeroTableError",
    "MomentError",
    "MomentEstimate",
    "MomentPolynomial",
    "MomentReference",
    "MomentScore",
    "MomentScorecard",
    "ODLYZKO_TABLES",
    "load_lmfdb_zeros",
    "load_odlyzko_zeros",
    "estimate_moment",
    "leading_moment_mean",
    "moment_polynomial",
    "moment_polynomial_mean",
    "moment_reference",
    "moment_scorecard",
    # heat flow
    "Phi",
    "H_t",
    "Xi_reference",
    "zeros_of_H_t",
    "track_zeros",
    "lambda_facts",
    "polynomial_heat_flow",
    # Weil explicit formula / positivity
    "gaussian_pair",
    "fejer_pair",
    "autocorrelation_pair",
    "explicit_formula_sides",
    "weil_functional",
    "positivity_probe",
    "near_tightness_report",
    # Davenport-Heilbronn counterexample battery
    "KAPPA_REF",
    "OFFLINE_ZERO_RE",
    "OFFLINE_ZERO_IM",
    "chi5",
    "kappa",
    "L_chi",
    "dh_f",
    "dh_coefficient",
    "completed_dh",
    "dh_functional_equation_defect",
    "dh_mean_value_defect",
    "dh_theta",
    "Z_dh",
    "zeros_on_line",
    "count_zeros_box",
    "find_offline_zero",
    "zeta_interface",
    "dh_interface",
    "battery",
    "claim_functional_equation",
    "claim_multiplicativity",
    # plots (lazy)
    *_PLOT_EXPORTS,
]
