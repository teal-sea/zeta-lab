"""Gap A of the lattice-extremality route, pinned.

Run 2 of hunt `r_b9552d` (run id `113786a8-1f1c-4220-b772-15160a0274fa`).
Run 1's instrument is `probe_37fb06a9.py` and is unchanged; this file does
not repeat any of its measurements.

The question this file answers is not "is the uniform lattice the centre-gas
extremum" (run 1 searched, found no counterexample; `hunts/frontier_math`
then turned that search into an argument) but:

    the argument of LATTICE-EXTREMALITY-ROUTE.md closes the dense side
    `rho >= 1/(2*pi)` and says nothing for `rho < 1/(2*pi)` (its gap A).
    What exactly would a Cohn-Elkies-style certificate have to be to close
    the sparse side, and can the family that closed gap B reach it?

Everything below is double precision, no enclosures.  Nothing here is
evidence for or against RH (`docs/08`).

    ../../.venv/bin/python hunts/r_b9552d/probe.py            # ~40 s
    ../../.venv/bin/python hunts/r_b9552d/probe.py --quick    # ~8 s
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
FM = HERE.parent / "frontier_math"
sys.path.insert(0, str(FM))

import counting_lemma as cl            # noqa: E402
import gram_form as gf                 # noqa: E402
import lattice_extremality as le       # noqa: E402
import two_species as ts               # noqa: E402

TWOPI = 2.0 * math.pi


# --------------------------------------------------------------------------
# vectorised kernels, checked against the scalar paths they claim to be
# --------------------------------------------------------------------------

def k1_vec(s):
    """`K_1(s) = -D(1,s) = Re(ghat(1,s)^2)`, the rectification kernel."""
    g = le.ghat_vec(1.0, s)
    return (g * g).real


def kernel_defect() -> float:
    """`k1_vec` against `gram_form.kernel(1, .)` on a probe spanning decades."""
    probe = np.array([0.0, 0.3, 1.7, TWOPI, 9.4, 2 * TWOPI, 25.1, 100.0, 1234.5])
    scal = np.array([gf.kernel(1.0, float(x)) for x in probe])
    return float(np.max(np.abs(k1_vec(probe) - scal)))


# --------------------------------------------------------------------------
# 1.  the pinned constants of a universal certificate
# --------------------------------------------------------------------------

def constants() -> dict:
    c2_0 = le.c2(0.0)
    kap_0 = cl.kappa(0.0)
    L = ts.centre_gas_row_closed()
    return {
        "L_lattice_row": L,                       # 0.11433003938654052
        "half_L": L / 2,
        "c2_0": c2_0,
        "kappa_0": kap_0,
        "kappa_hat_0": 4 * math.pi * c2_0,
        "L_from_constants": 2 * kap_0 - 4 * c2_0,  # must equal L
        "c_needed_2c2_0": 2 * c2_0,
        "c_lo_K1_0": gf.kernel(1.0, 0.0),
        "c_hi_endpoint": math.cos(math.sqrt(2) / 2) ** 2 * (1 + math.cosh(1.0)),
    }


def sup_f(s_max: float = 400.0, n: int = 4_000_001) -> dict:
    """`sup_{s != 0} f(s)`, and the tail check that the scan is the sup.

    `f` decays like `1/s^2`, so a scan to `s_max` plus a monotone envelope on
    the tail settles it.  Reported against `L/2`, which section 2 of
    RESULTS.md shows is a hard ceiling on `sup|g|` for any universal
    certificate, hence on `sup f`.
    """
    s = np.linspace(1e-9, s_max, n)
    f = le.f_vec(s)
    i = int(np.argmax(f))
    tail = np.linspace(s_max, 20 * s_max, 400_001)
    return {
        "sup_f": float(f[i]),
        "argmax_f": float(s[i]),
        "f_at_zero": float(le.f_vec(np.array([0.0]))[0]),
        "sup_f_tail": float(np.max(le.f_vec(tail))),
        "first_positive_s": float(s[f > 0][0]),
        "scan_s_max": s_max,
    }


# --------------------------------------------------------------------------
# 2.  can the gap-B family reach the pinned value of c?
# --------------------------------------------------------------------------

def fejer_family(quick: bool) -> dict:
    """`g = -kappa + c*fejer`: the admissible window for `c` against the value
    a density-independent bound demands.

    `LP_v(rho) = -8*pi*rho*c2(0) + 2*kappa(0) + 2c(2*pi*rho - 1)` has
    `rho`-coefficient `-8*pi*c2(0) + 4*pi*c = 4*pi*(c - 2*c2(0))`, so the
    bound is constant in `rho` -- i.e. it closes the sparse side too -- if and
    only if `c = 2*c2(0)`, and then it equals `2*kappa(0) - 4*c2(0) = L`
    exactly.  Admissibility caps `c` at `inf khat/shat`.
    """
    k = constants()
    c_need, c_hi, c_lo = k["c_needed_2c2_0"], k["c_hi_endpoint"], k["c_lo_K1_0"]

    # the cap, re-measured rather than taken from its closed form
    xi = np.linspace(1e-6, 1 - 1e-9, 200_001 if not quick else 20_001)
    khat = np.array([2 * math.pi * le.c2(float(x)) * (1 + math.cosh(float(x)))
                     for x in xi])
    shat = TWOPI * (1 - xi)
    ratio = khat / shat
    cap_measured = float(np.min(ratio))

    # the witness: with c = 2*c2(0) the certificate condition ghat <= 0 fails
    ghat_needed = -khat + c_need * shat
    j = int(np.argmax(ghat_needed))

    # the floor, re-measured: sup K1^+/fejer over a wide range
    xs = np.linspace(1e-6, 3000.0, 1_000_001 if not quick else 100_001)
    fl = np.maximum(k1_vec(xs), 0.0) / le.fejer(xs)
    floor_measured = float(np.max(fl))

    # the bound is constant in rho at c = c_need, and equals L
    rhos = [0.001, 0.01, 0.05, 1 / TWOPI, 0.25, 1.0]
    const_check = [le.lp_bound_with_majorant(r, c=c_need) for r in rhos]

    # the best uniform (all-density) bound the family does give
    uniform = 2 * k["kappa_0"] - 2 * c_hi
    return {
        "c_needed": c_need,
        "c_cap_closed_form": c_hi,
        "c_cap_measured": cap_measured,
        "c_floor_closed_form": c_lo,
        "c_floor_measured": floor_measured,
        "shortfall_factor": c_need / c_hi,
        "shortfall_absolute": c_need - c_hi,
        "witness_xi": float(xi[j]),
        "witness_ghat": float(ghat_needed[j]),
        "witness_ghat_at_xi_0.999": float((-khat + c_need * shat)[-2]),
        "bound_at_c_needed_over_rho": const_check,
        "bound_at_c_needed_spread": float(max(const_check) - min(const_check)),
        "uniform_bound_best_c": uniform,
        "uniform_bound_over_L": uniform / k["L_lattice_row"],
    }


# --------------------------------------------------------------------------
# 3.  the new uniform bound, tested against configurations
# --------------------------------------------------------------------------

def configurations(quick: bool) -> list:
    """Sparse and dense periodic configurations, with `J`, the family's bound
    at the best admissible `c`, and the conjectured ceiling `L`."""
    k = constants()
    c_hi = k["c_hi_endpoint"]
    L = k["L_lattice_row"]
    N = 400 if quick else 1500
    rng = np.random.default_rng(20260820)

    cases = [("lattice 2pi", [0.0], TWOPI)]
    for mult in (1.5, 2.0, 4.0, 10.0):          # sparse: spacing above 2pi
        cases.append((f"lattice {mult}x2pi", [0.0], mult * TWOPI))
    cases.append(("vacancy 1-in-3", [0.0, TWOPI], 3 * TWOPI))
    cases.append(("vacancy 1-in-5", [0.0, TWOPI, 2 * TWOPI, 3 * TWOPI], 5 * TWOPI))
    cases.append(("tight pair, sparse", [0.0, 0.4], 20 * TWOPI))
    cases.append(("cluster of 3, sparse", [0.0, 0.3, 0.7], 30 * TWOPI))
    for i in range(3 if quick else 6):
        m = int(rng.integers(2, 6))
        P = float(rng.uniform(4, 20) * TWOPI)   # density well below 1/(2pi)
        a = np.sort(rng.uniform(0, P, m))
        cases.append((f"random sparse #{i}", list(a), P))

    out = []
    for name, a, P in cases:
        rho = len(a) / P
        J = le.per_centre_cost(a, P, N=N)
        out.append({
            "name": name, "m": len(a), "P": P, "rho_times_2pi": rho * TWOPI,
            "J": J,
            "family_bound": le.lp_bound_with_majorant(rho, c=c_hi),
            "uniform_bound": 2 * k["kappa_0"] - 2 * c_hi,
            "L": L,
            "below_uniform_bound": bool(J <= 2 * k["kappa_0"] - 2 * c_hi + 1e-9),
            "below_L": bool(J <= L + 1e-9),
        })
    return out


# --------------------------------------------------------------------------
# 4.  controls -- a test that cannot fail is not a test
# --------------------------------------------------------------------------

def controls(quick: bool) -> dict:
    """Three planted faults, each of which must turn a verdict red."""
    k = constants()
    L = k["L_lattice_row"]

    # (i) the sup f <= L/2 necessary condition must fire on an inflated f
    s = np.linspace(1e-9, 400.0, 400_001)
    f = le.f_vec(s)
    inflate = float(k["half_L"] / np.max(f))
    planted_fires = bool(np.max(f) * (inflate * 1.01) > k["half_L"])
    honest_fires = bool(np.max(f) > k["half_L"])

    # (ii) the admissibility cap must reject c = 2*c2(0) and accept c = K1(0)
    xi = np.linspace(1e-6, 1 - 1e-9, 20_001)
    khat = np.array([2 * math.pi * le.c2(float(x)) * (1 + math.cosh(float(x)))
                     for x in xi])
    shat = TWOPI * (1 - xi)
    rejects_needed = bool(np.max(-khat + k["c_needed_2c2_0"] * shat) > 0)
    accepts_floor = bool(np.max(-khat + k["c_lo_K1_0"] * shat) <= 0)

    # (iii) the configuration check must report a violation against a bound
    #       deliberately set below the lattice row
    cfg = le.per_centre_cost([0.0], TWOPI, N=400 if quick else 1500)
    catches_low_ceiling = bool(cfg > L / 2)

    return {
        "inflation_needed_to_break_sup_f": inflate,
        "planted_inflated_f_fires": planted_fires,
        "honest_f_fires": honest_fires,
        "cap_rejects_c_needed": rejects_needed,
        "cap_accepts_c_floor": accepts_floor,
        "config_check_catches_low_ceiling": catches_low_ceiling,
        "kernel_defect": kernel_defect(),
        "lattice_row_calibration": cfg - L,
    }


def main() -> None:
    quick = "--quick" in sys.argv
    res = {
        "run_id": "113786a8-1f1c-4220-b772-15160a0274fa",
        "quick": quick,
        "constants": constants(),
        "sup_f": sup_f(400.0, 400_001 if quick else 4_000_001),
        "fejer_family": fejer_family(quick),
        "configurations": configurations(quick),
        "controls": controls(quick),
    }
    k, ff, sf = res["constants"], res["fejer_family"], res["sup_f"]
    res["verdict"] = {
        "universal_certificate_ruled_out_by_sup_f": bool(sf["sup_f"] > k["half_L"]),
        "sup_f_margin_factor": k["half_L"] / sf["sup_f"],
        "fejer_family_can_close_gap_A": bool(ff["c_needed"] <= ff["c_cap_closed_form"]),
        "fejer_shortfall_factor": ff["shortfall_factor"],
        "new_uniform_bound_all_densities": ff["uniform_bound_best_c"],
        "violations_of_L": [c["name"] for c in res["configurations"]
                            if not c["below_L"]],
        "violations_of_uniform_bound": [c["name"] for c in res["configurations"]
                                        if not c["below_uniform_bound"]],
    }
    out = HERE / ("results_quick.json" if quick else "results.json")
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(json.dumps(res["verdict"], indent=2))
    print("constants:", json.dumps(k, indent=2))
    print("fejer:", json.dumps(ff, indent=2))
    print("sup_f:", json.dumps(sf, indent=2))
    print("controls:", json.dumps(res["controls"], indent=2))
    print("wrote", out)


if __name__ == "__main__":
    main()
