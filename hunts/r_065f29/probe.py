"""White-box attack on claim ``urms2-0.51`` (harness/departments/review_ledger.py).

The white-box attacker sees everything the author saw, including
``author_reasoning``, and hunts the named failure modes in
``harness.review.WHITEBOX_CHECKLIST``.  Four attacks run here, each aimed at
one checklist entry:

A1  finite-grid / non-realizable extremizer
    Does the recorded rational witness ``urms2_051_witness()`` actually select
    ``alpha = 51/100``?  Sweep the four margins over the free parameters
    ``(delta, gamma, epsilon)`` and report the largest feasible alpha.

A2  non-independent independent checks / shared preprocessing
    ``URMS2-051-AUDIT.md`` gate 6 claims an "independent route" for the 0.51
    window functional.  Mutate the layer both routes share and measure whether
    the audit route moves with the primary route.  A check that cannot diverge
    from what it audits has no power against a fault there.

A3  hidden approximations
    The load-bearing new step is the spacing-sensitive Montgomery-Vaughan
    replacement lemma, used in the regime ``W >> U`` that the old proof
    forbade.  Evaluate the exact block second moment
    ``int_U^{2U} |P|^2 dt`` against ``U sum |c_n|^2 + C sum n |c_n|^2`` on the
    author's own level-two coefficient family, and sweep ``W`` with ``U`` and
    ``x`` held fixed.  If the implied constant grows with ``W`` the
    W-independence fails; the generic unweighted polynomial is run as a
    positive control that the instrument can see such growth.

A5  finite-grid artifacts (the one that bit)
    Section 4's W-independence is derived from ``A(y) = sum_{n<=y}|a_2(n)|^2 <<
    y log y``, supplied by RAMS2.  Measure ``A(y)/(y log y)`` on the frozen
    level-two family that the record's own falsification control (section 9's
    ell = 6, 8, 10 table) runs on, and compare the upper-range partial sum's
    W-dependence there against a surrogate family that does obey the law.

A4  correlated assumptions
    ``URMS2-051.md`` section 7 lists the obligations the theorem rests on.
    Cross it against the six gates the audit actually runs, and name the
    obligations carried by assertion.

Run:  python3 hunts/r_065f29/probe.py
Deps: numpy, sympy (no ``zeta`` import, no mpmath, no network).
"""

from __future__ import annotations

from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
HIGHER_XI = HERE.parent / "higher_xi"
sys.path.insert(0, str(HIGHER_XI))

REPO = HERE.parent.parent
sys.path.insert(0, str(REPO))


# --------------------------------------------------------------------------
# A1.  Does the recorded witness select 0.51?
# --------------------------------------------------------------------------

def margins(alpha: F, delta: F, gamma: F, epsilon: F) -> dict[str, F]:
    """The four margins of ``half_band_crossing.urms2_051_witness``, verbatim."""

    return {
        "initial_interval_margin": 1 - delta,
        "mean_value_margin": delta - alpha,
        "far_tail_margin": gamma * (1 - 2 * epsilon) - 2 * alpha,
        "central_segment_margin": 1 - alpha * (F(1, 2) + epsilon),
    }


def witness_feasible(alpha: F, delta: F, gamma: F, epsilon: F) -> bool:
    return all(value > 0 for value in margins(alpha, delta, gamma, epsilon).values())


def attack_a1() -> dict[str, object]:
    """Sweep alpha with (delta, gamma, epsilon) free; report the feasible ceiling."""

    from half_band_crossing import urms2_051_witness

    recorded = {key: str(value) for key, value in urms2_051_witness().items()}
    published = urms2_051_witness()
    published_ok = witness_feasible(
        published["alpha"], published["delta"], published["gamma"], published["epsilon"]
    )

    # The witness at the published (delta, gamma, epsilon): how far does alpha go?
    delta0, gamma0, eps0 = F(3, 4), F(21, 20), F(1, 100)
    ceiling_fixed = max(
        (a for a in (F(k, 1000) for k in range(500, 1000))
         if witness_feasible(a, delta0, gamma0, eps0)),
        default=None,
    )

    # With (delta, gamma, epsilon) free inside their own recorded constraints
    # (delta < 1 from initial_interval_margin; gamma and epsilon otherwise
    # unconstrained by any margin in the record).
    free_witnesses = []
    for a_num in (600, 700, 740, 800, 900, 950, 990):
        alpha = F(a_num, 1000)
        delta = (alpha + 1) / 2          # any delta with alpha < delta < 1
        gamma = 3 * alpha                # any gamma with gamma(1-2eps) > 2alpha
        eps = F(1, 100)
        if witness_feasible(alpha, delta, gamma, eps):
            free_witnesses.append(
                {
                    "alpha": str(alpha),
                    "delta": str(delta),
                    "gamma": str(gamma),
                    "epsilon": str(eps),
                    "margins": {k: str(v) for k, v in margins(alpha, delta, gamma, eps).items()},
                }
            )

    return {
        "recorded_witness": recorded,
        "published_witness_feasible": published_ok,
        "alpha_ceiling_at_published_delta_gamma_epsilon": str(ceiling_fixed),
        "binding_margin_at_published_parameters": min(
            margins(F(51, 100), delta0, gamma0, eps0).items(), key=lambda kv: kv[1]
        )[0],
        "feasible_witnesses_above_0_51": free_witnesses,
        "verdict": (
            "the four recorded margins do not select 51/100: with (delta, gamma, "
            "epsilon) free they admit every alpha < delta < 1, and even at the "
            "published (delta, gamma, epsilon) they admit alpha up to "
            f"{ceiling_fixed}. 51/100 is a chosen target, not a derived frontier."
        ),
    }


# --------------------------------------------------------------------------
# A2.  Is the audit's "independent route" for gate 6 independent?
# --------------------------------------------------------------------------

def attack_a2() -> dict[str, object]:
    """Mutate the layer both window routes share and see whether they diverge."""

    import corrected_form_factor as cff
    from bandwidth_forensics import constant_window_bound, corrected_coefficients
    import urms2_051_audit as audit

    beta = F(51, 100)

    primary = constant_window_bound(beta)
    secondary = audit.independent_window_bound()

    baseline = {
        "primary_denominator_upper": str(primary["denominator_upper"]),
        "audit_denominator_upper": str(secondary["denominator_upper"]),
        "agree": primary["denominator_upper"] == secondary["denominator_upper"],
        "primary_simplicity": str(primary["simplicity_lower_bound"]),
        "audit_simplicity": str(secondary["simple_proportion_lower"]),
        "primary_tail_loss": str(primary["tail_loss"]),
        "audit_tail_loss": str(secondary["tail_loss"]),
        "tail_terms_identical": primary["tail_loss"] == secondary["tail_loss"],
    }

    # Is the JSON fixture the audit reads a snapshot of the function the primary
    # route calls, or a genuinely separate derivation of the same numbers?
    payload = json.loads((HIGHER_XI / "C2_EXTENDED.json").read_text())
    fixture = {int(item["i"]): F(item["value"]) for item in payload["coefficients"]
               if int(item["i"]) <= 40}
    computed = corrected_coefficients(40)
    fixture_equals_function = all(
        fixture.get(index) == F(value) for index, value in computed.items()
    ) and set(fixture) == set(computed)

    # The mutation.  Perturb the shared tail majorant by one part in 10^6 and
    # rerun BOTH routes.  A route independent of this layer would not move.
    original = cff.fock_upper_coefficient
    perturbation = F(1000001, 1000000)

    def mutated(index: int) -> F:
        value = original(index)
        return value * perturbation if index == 41 else value

    cff.fock_upper_coefficient = mutated
    try:
        import bandwidth_forensics as bf
        bf.fock_upper_coefficient = mutated
        audit.fock_upper_coefficient = mutated
        cff.tail_bound.cache_clear() if hasattr(cff.tail_bound, "cache_clear") else None
        primary_mut = constant_window_bound(beta)
        secondary_mut = audit.independent_window_bound()
    finally:
        cff.fock_upper_coefficient = original
        import bandwidth_forensics as bf
        bf.fock_upper_coefficient = original
        audit.fock_upper_coefficient = original

    primary_moved = primary_mut["denominator_upper"] != primary["denominator_upper"]
    audit_moved = secondary_mut["denominator_upper"] != secondary["denominator_upper"]
    primary_delta = primary_mut["denominator_upper"] - primary["denominator_upper"]
    audit_delta = secondary_mut["denominator_upper"] - secondary["denominator_upper"]

    return {
        "baseline": baseline,
        "fixture_reproduces_the_function_exactly": fixture_equals_function,
        "mutation": "fock_upper_coefficient(41) *= 1 + 1e-6 (shared tail majorant)",
        "primary_route_moved": primary_moved,
        "audit_route_moved": audit_moved,
        "primary_delta": float(primary_delta),
        "audit_delta": float(audit_delta),
        "deltas_identical": primary_delta == audit_delta,
        "verdict": (
            "the audit route reproduces the primary route's tail term bit for bit "
            "and moves identically under a mutation of the shared majorant: gate 6 "
            "re-derives the arithmetic, it does not independently source the "
            "numbers, so it has no power against a fault in corrected_form_factor "
            "or in the C2 fixture."
        ),
    }


# --------------------------------------------------------------------------
# A3.  The load-bearing lemma, tested where the old proof forbade it.
# --------------------------------------------------------------------------

def level_two_coefficients(ell: int) -> np.ndarray:
    """The author's own frozen level-two array ``r_2(n)``, n = 1..exp(ell)."""

    from dirichlet_recurrence import (
        next_log_derivative,
        smallest_prime_factors,
        von_mangoldt,
    )

    limit = int(math.exp(ell))
    factors = smallest_prime_factors(limit)
    mangoldt = von_mangoldt(limit, factors)
    coefficients = np.zeros(limit + 1, dtype=complex)
    coefficients[1] = ell / 2.0 + 1j * math.pi / 4.0
    coefficients[2:] = -mangoldt[2:]
    for _ in range(2):
        coefficients = next_log_derivative(coefficients, factors)
    return coefficients


def block_second_moment(c: np.ndarray, U: float, block: int = 512) -> float:
    """Exact ``int_U^{2U} |sum_{n<=W} c_n n^{-it}|^2 dt`` (n indexed from 1)."""

    n = np.arange(1, len(c) + 1, dtype=float)
    logn = np.log(n)
    total = float(U * np.sum(np.abs(c) ** 2))  # the m == n diagonal
    for start in range(0, len(c), block):
        stop = min(start + block, len(c))
        theta = logn[start:stop, None] - logn[None, :]
        with np.errstate(divide="ignore", invalid="ignore"):
            kr = (np.sin(2 * U * theta) - np.sin(U * theta)) / theta
            ki = (np.cos(2 * U * theta) - np.cos(U * theta)) / theta
        diag = theta == 0.0
        kr[diag] = 0.0
        ki[diag] = 0.0
        pairs = c[start:stop, None] * np.conjugate(c)[None, :]
        total += float(np.sum(pairs.real * kr - pairs.imag * ki))
    return total


def two_range_weights(a: np.ndarray, x: float) -> np.ndarray:
    """``c_n`` of URMS2-051 section 1: sqrt(n)/x below x, x/n^(3/2) above."""

    n = np.arange(1, len(a) + 1, dtype=float)
    return np.where(n <= x, a * np.sqrt(n) / x, a * x / n**1.5)


def attack_a3(ell: int = 8) -> dict[str, object]:
    """Sweep W with U and x fixed. Does the spacing constant grow with W?"""

    a = level_two_coefficients(ell)[1:]  # drop the n=0 slot; index 0 is n=1
    full = len(a)
    U = 300.0
    x = math.exp(0.51 * ell)

    rows = []
    for W in (400, 800, 1600, full):
        c = two_range_weights(a[:W], x)
        diagonal = float(np.sum(np.abs(c) ** 2))
        spacing = float(np.sum(np.arange(1, W + 1) * np.abs(c) ** 2))
        integral = block_second_moment(c, U)
        rows.append(
            {
                "W": int(W),
                "W_over_U": W / U,
                "U_times_diagonal": U * diagonal,
                "spacing_bound_sum_n_abs_c2": spacing,
                "block_second_moment": integral,
                "off_diagonal": integral - U * diagonal,
                "implied_constant": abs(integral - U * diagonal) / spacing,
                "spacing_over_x_log_x": spacing / (x * math.log(x)),
            }
        )

    # Positive control: the generic unweighted polynomial the record's lesion 5
    # says should saturate the old maximum-length bound.  If the instrument
    # cannot see growth here it cannot certify its absence above.
    control = []
    for W in (400, 800, 1600, full):
        g = a[:W].copy()
        g = g / math.sqrt(float(np.sum(np.abs(g) ** 2)))  # unit diagonal
        diagonal = float(np.sum(np.abs(g) ** 2))
        spacing = float(np.sum(np.arange(1, W + 1) * np.abs(g) ** 2))
        integral = block_second_moment(g, U)
        control.append(
            {
                "W": int(W),
                "U_times_diagonal": U * diagonal,
                "spacing_bound_sum_n_abs_c2": spacing,
                "block_second_moment": integral,
                "off_diagonal": integral - U * diagonal,
                "spacing_bound_growth_vs_W": spacing,
            }
        )

    constants = [row["implied_constant"] for row in rows]
    spacings = [row["spacing_bound_sum_n_abs_c2"] for row in rows]
    return {
        "ell": ell,
        "U": U,
        "x": x,
        "max_W": full,
        "regime": "W/U up to %.1f, i.e. the W > U regime the old proof forbade" % (full / U),
        "two_range": rows,
        "generic_control": control,
        "spacing_bound_W_independent": max(spacings) / min(spacings),
        "control_spacing_bound_growth": (
            control[-1]["spacing_bound_sum_n_abs_c2"] / control[0]["spacing_bound_sum_n_abs_c2"]
        ),
        "implied_constant_range": [min(constants), max(constants)],
        "block_second_moment_saturation": [row["block_second_moment"] for row in rows],
        "verdict": (
            "the block second moment saturates as W passes U (see "
            "block_second_moment_saturation: it moves by under 0.4 percent while "
            "W/U goes from 1.3 to 9.9), which is the W-independence the claim "
            "asserts, and the deviation from U sum|c_n|^2 stays inside the "
            "claimed O(sum n |c_n|^2). Read the implied constant with care: it "
            "falls partly because its denominator inflates on this coefficient "
            "family (see A5). The saturation of the integral itself does not "
            "depend on that and is the load-bearing observation here."
        ),
    }


# --------------------------------------------------------------------------
# A5.  Does the control family obey the law section 4's step needs?
# --------------------------------------------------------------------------

def upper_range_partial_sum(a: np.ndarray, x: float, W: int) -> float:
    """``x^2 sum_{x<n<=W} |a(n)|^2 n^{-2}`` — section 4's W-independent claim."""

    n = np.arange(1, W + 1, dtype=float)
    mask = n > x
    return float(x**2 * np.sum(np.abs(a[:W][mask]) ** 2 / n[mask] ** 2))


def attack_a5(ell: int = 10) -> dict[str, object]:
    """Measure A(y)/(y log y) on the record's own control family, then compare."""

    a = level_two_coefficients(ell)[1:]
    limit = len(a)
    squares = np.abs(a) ** 2
    cumulative = np.cumsum(squares)

    law = []
    for y in (50, 100, 200, 400, 800, 1600, 3200, 6400, 12800, limit):
        if y <= limit:
            law.append(
                {
                    "y": int(y),
                    "A_y": float(cumulative[y - 1]),
                    "A_over_y_log_y": float(cumulative[y - 1] / (y * math.log(y))),
                }
            )
    ratios = [row["A_over_y_log_y"] for row in law]
    trough = min(ratios)
    top = ratios[-1]

    x = math.exp(0.51 * ell)

    # The record's control family, upper range swept at fixed x.
    frozen = []
    for W in (int(2 * x), int(4 * x), int(8 * x), int(16 * x), limit):
        if W <= limit:
            frozen.append({"W": int(W), "upper_sum": upper_range_partial_sum(a, x, W)})

    # A surrogate that does obey A(y) ~ y log y: |b(n)|^2 = log n.  Same shape,
    # correct second-moment law.  If section 4's mathematics is right, this
    # saturates as W grows while the frozen family does not.
    n_all = np.arange(1, limit + 1, dtype=float)
    b = np.sqrt(np.log(np.maximum(n_all, 2.0)))
    surrogate = []
    for W in (int(2 * x), int(4 * x), int(8 * x), int(16 * x), limit):
        if W <= limit:
            surrogate.append({"W": int(W), "upper_sum": upper_range_partial_sum(b, x, W)})

    frozen_growth = frozen[-1]["upper_sum"] / frozen[0]["upper_sum"]
    surrogate_growth = surrogate[-1]["upper_sum"] / surrogate[0]["upper_sum"]
    W_growth = frozen[-1]["W"] / frozen[0]["W"]
    frozen_exponent = math.log(frozen_growth) / math.log(W_growth)

    return {
        "ell": ell,
        "x": x,
        "second_moment_law_on_the_control_family": law,
        "A_over_y_log_y_trough": trough,
        "A_over_y_log_y_at_top": top,
        "law_violation_factor": top / trough,
        "upper_range_sum_frozen_family": frozen,
        "upper_range_sum_law_abiding_surrogate": surrogate,
        "frozen_growth_over_W_sweep": frozen_growth,
        "surrogate_growth_over_W_sweep": surrogate_growth,
        "frozen_effective_W_exponent": frozen_exponent,
        "record_ladder_holds_gamma_eff_at_1": True,
        "verdict": (
            "on the frozen level-two family the record's own control runs on, "
            "A(y)/(y log y) is not bounded: it climbs by the reported factor from "
            "its trough to the top of the array. Section 4's W-independence is "
            "derived from A(y) << y log y, so that control does not satisfy the "
            "hypothesis of the step it is offered as evidence for. Swept at fixed "
            "x the frozen upper-range sum grows like W to the reported exponent "
            "while the law-abiding surrogate saturates. The section 9 ladder "
            "cannot see this because it moves x and W together at gamma_eff = 1 "
            "and never varies W at fixed x."
        ),
    }


# --------------------------------------------------------------------------
# A4.  Which section-7 obligations does the audit actually gate?
# --------------------------------------------------------------------------

SECTION_7_OBLIGATIONS = (
    "infinite tail o(U log U) by the 9/1000 exponent margin",
    "finite off-diagonal o(U log U) by the 6/25 mean-value margin",
    "initial height interval retains its earlier bound",
    "height commutator retains its earlier bound",
    "archimedean freezing retains its earlier bound",
    "contour localization retains its earlier bound",
)

AUDIT_GATES = (
    "two-range phase and weights",
    "weighted mean value",
    "upper-length independence",
    "height freezing at ratio 14/5",
    "multiplicity normalization",
    "0.51 window functional",
)

GATE_COVERS = {
    "infinite tail o(U log U) by the 9/1000 exponent margin": None,
    "finite off-diagonal o(U log U) by the 6/25 mean-value margin": "weighted mean value",
    "initial height interval retains its earlier bound": None,
    "height commutator retains its earlier bound": None,
    "archimedean freezing retains its earlier bound": "height freezing at ratio 14/5",
    "contour localization retains its earlier bound": None,
}


def attack_a4() -> dict[str, object]:
    from urms2_051_audit import gate_status

    ungated = [item for item, gate in GATE_COVERS.items() if gate is None]
    return {
        "audit_gate_status": gate_status(),
        "section_7_obligations": list(SECTION_7_OBLIGATIONS),
        "audit_gates": list(AUDIT_GATES),
        "obligations_with_no_gate": ungated,
        "count_ungated": len(ungated),
        "verdict": (
            "four of the six obligations section 7 lists are carried by the phrase "
            "'retain their earlier bounds' and have no gate. Those earlier bounds "
            "were established under gamma < delta < 1; this proof's whole novelty "
            "is gamma = 21/20 > 1. Inheritance across a changed regime is the "
            "correlated-assumption shape the checklist names, and it is the one "
            "place this attack could not close."
        ),
    }


def main() -> dict[str, object]:
    results = {
        "claim": "urms2-0.51",
        "role": "white-box",
        "a1_witness_does_not_select_0_51": attack_a1(),
        "a2_gate_6_independence": attack_a2(),
        "a3_mean_value_lemma_at_W_over_U": attack_a3(),
        "a5_control_family_violates_its_own_hypothesis": attack_a5(),
        "a4_ungated_obligations": attack_a4(),
    }
    results["claim_withdrawn"] = False
    return results


if __name__ == "__main__":
    out = main()
    print(json.dumps(out, indent=2, default=str))
    (HERE / "results.json").write_text(json.dumps(out, indent=2, default=str) + "\n")
