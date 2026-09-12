"""Hunt r_f7cd45, which structural properties of zeta actually discriminate.

Runs six claimed structural properties of zeta through gate #3 of
``docs/09-new-ontologies.md``, as executed by ``zeta.epstein.battery``: each
property is evaluated on zeta and on three functions that share zeta's
analytic structure and violate RH (Davenport-Heilbronn, and the Epstein zetas
of the two discriminant -23 forms (2,1,3) and (1,1,6)).  A property every
rival also satisfies distinguishes nothing.

Nothing here is evidence for or against RH (``docs/08-why-it-is-hard.md``).
The subject is discrimination between functions, not the location of zeros.

Two stages, because they cost three orders of magnitude apart:

    .venv/bin/python hunts/r_f7cd45/probe.py            # both stages
    .venv/bin/python hunts/r_f7cd45/probe.py --stage 1  # the five cheap claims
    .venv/bin/python hunts/r_f7cd45/probe.py --stage 2  # the box counts

Stage 2's box parameters are preregistered in ``MISSION.md`` and were
committed before the first box was counted.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from math import gcd
from pathlib import Path

from mpmath import mp

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from zeta import epstein  # noqa: E402
from zeta.epstein import claim_functional_equation, claim_multiplicativity  # noqa: E402

HERE = Path(__file__).resolve().parent

# --- parameters, all fixed here rather than inline at the call site ---------

DPS_CLAIMS = 25          # working precision for the five cheap claims
DPS_BOX = 15             # preregistered: dropped from 20, per issue #21
FORMS = ((2, 1, 3), (1, 1, 6))

# Precision audit (stage 2a).  The preregistered DPS_BOX was chosen on cost.
# Before spending it, check that each completed function has actually
# *converged* at that precision at the box height: run the same point up a
# ladder of dps and see where the value stops moving.  A box count computed
# below the convergence floor is a winding number over noise, and the
# integrality check inside count_zeros_box does not catch that -- noise winds
# to an integer just as happily as signal does.
DPS_LADDER = (15, 20, 30, 40, 60, 80, 100)
AUDIT_POINT = (0.75, 85.5)     # inside box B2, off the critical line
AUDIT_AGREE_RELTOL = "1e-6"    # two rungs agree to this => converged

# Preregistered in MISSION.md, committed before any box was counted.
BOXES = {
    "B1": {"re": (0.6, 0.9), "im": (80.0, 81.0),
           "why": "first unit slice of issue #21's window; no rival zero known "
                  "to this laboratory inside it"},
    "B2": {"re": (0.6, 0.9), "im": (85.0, 86.0),
           "why": "the unit slice holding the pinned Davenport-Heilbronn "
                  "off-line zero 0.8085171824... + 85.6993484853...i"},
}
BOX_WALL_CLOCK_CAP_S = 600.0

Z_REAL_SAMPLES = [1.0, 5.0, 14.0, 21.0, 30.5]
Z_REAL_TOL = "1e-12"
LINE_WINDOW = (10.0, 40.0)

# Coprime pairs, both members >= 2.  m = 1 is excluded deliberately: the
# Epstein coefficient is a representation count with r(1) != 1, so a pair
# (1, n) would fail on normalisation rather than on multiplicative structure.
# Excluding it gives every rival its best shot; they fail anyway.
COPRIME_PAIRS = [(2, 3), (2, 7), (3, 7), (2, 9), (3, 4), (4, 9), (5, 6), (3, 8)]
# Non-coprime pairs, for the strictly stronger complete-multiplicativity claim.
ANY_PAIRS = COPRIME_PAIRS + [(2, 2), (2, 4), (3, 3), (2, 6), (3, 6), (5, 5)]
COEFF_TOL = "1e-12"


# --- the six claims ---------------------------------------------------------
# Each takes the zeta-like interface dict of zeta.epstein and returns a bool.

def claim_hardy_Z_real(iface: dict) -> bool:
    """Claim: "there is a Hardy-style Z, real-valued for real t"."""
    tol = mp.mpf(Z_REAL_TOL)
    values = [iface["Z"](mp.mpf(t)) for t in Z_REAL_SAMPLES]
    if all(abs(mp.mpf(mp.re(v))) < tol for v in values):
        return False  # a Z identically zero would satisfy this vacuously
    return all(abs(mp.mpf(mp.im(v))) < tol for v in values)


def claim_zeros_on_critical_line(iface: dict) -> bool:
    """Claim: "the function has zeros on the critical line"."""
    return iface["zeros_on_line"](LINE_WINDOW[0], LINE_WINDOW[1]) > 0


def claim_complete_multiplicativity(iface: dict) -> bool:
    """Claim: "the Dirichlet coefficients are completely multiplicative:
    a_{mn} = a_m a_n for *all* m, n", strictly stronger than
    :func:`zeta.epstein.claim_multiplicativity`, which only quantifies over
    coprime pairs."""
    tol = mp.mpf(COEFF_TOL)
    a = iface["coefficient"]
    return all(abs(a(m * n) - a(m) * a(n)) < tol for (m, n) in ANY_PAIRS)


def claim_multiplicativity_coprime(iface: dict) -> bool:
    """Claim: "a_{mn} = a_m a_n for coprime m, n" over a wider pair set than
    :func:`zeta.epstein.claim_multiplicativity` uses, with m, n >= 2."""
    tol = mp.mpf(COEFF_TOL)
    a = iface["coefficient"]
    return all(
        abs(a(m * n) - a(m) * a(n)) < tol
        for (m, n) in COPRIME_PAIRS
        if gcd(m, n) == 1
    )


CLAIMS = [
    ("functional_equation",
     "the completed function satisfies F(s) = F(1-s)",
     claim_functional_equation),
    ("hardy_Z_real",
     "there is a Hardy-style Z real-valued for real t",
     claim_hardy_Z_real),
    ("zeros_on_critical_line",
     "the function has zeros on the critical line",
     claim_zeros_on_critical_line),
    ("multiplicative_coefficients",
     "the Dirichlet coefficients are multiplicative (coprime m, n)",
     claim_multiplicativity_coprime),
    ("completely_multiplicative_coefficients",
     "the Dirichlet coefficients are completely multiplicative (all m, n)",
     claim_complete_multiplicativity),
]


# --- stage 1 ----------------------------------------------------------------

def run_stage1() -> dict:
    out = []
    for key, prose, fn in CLAIMS:
        t0 = time.time()
        verdict = epstein.battery(fn, dps=DPS_CLAIMS, forms=FORMS)
        elapsed = time.time() - t0
        rivals = [n for n in ("davenport_heilbronn",
                              "epstein_2_1_3", "epstein_1_1_6")]
        surviving = [n for n in rivals if verdict[n]]
        out.append({
            "key": key,
            "claim": prose,
            "riemann_zeta": bool(verdict["riemann_zeta"]),
            "per_function": {n: bool(verdict[n]) for n in rivals},
            "rivals_surviving": len(surviving),
            "rivals_total": len(rivals),
            "shared_with": list(verdict["shared_with"]),
            "distinguishes": bool(verdict["distinguishes"]),
            "gate3_verdict": "DISTINGUISHES" if verdict["distinguishes"] else "VACUOUS",
            "seconds": round(elapsed, 2),
        })
        print(f"  {key:42s} zeta={verdict['riemann_zeta']!s:5s} "
              f"rivals_surviving={len(surviving)}/3  "
              f"{'DISTINGUISHES' if verdict['distinguishes'] else 'VACUOUS':13s} "
              f"({elapsed:.1f}s)", flush=True)
    return {"claims": out}


# --- stage 2, the sixth property -------------------------------------------

def run_precision_audit() -> dict:
    """Stage 2a. Where does each completed function stop moving with dps, at
    the height of the preregistered boxes?

    This is an instrument check, not a result about zeta, and it is run before
    any winding number so that it cannot be a post-hoc excuse for one.
    """
    from zeta.core import xi
    from zeta.epstein import completed_dh, epstein_completed

    s = complex(*AUDIT_POINT)
    fns = {
        "riemann_zeta": lambda d: xi(s, dps=d),
        "davenport_heilbronn": lambda d: completed_dh(s, dps=d),
        "epstein_2_1_3": lambda d: epstein_completed(s, (2, 1, 3), dps=d),
        "epstein_1_1_6": lambda d: epstein_completed(s, (1, 1, 6), dps=d),
    }
    reltol = mp.mpf(AUDIT_AGREE_RELTOL)
    audit = {}
    for name, f in fns.items():
        ladder, floor, values = [], None, []
        for d in DPS_LADDER:
            t0 = time.time()
            v = f(d)
            values.append(v)
            ladder.append({"dps": d, "value": mp.nstr(v, 12),
                           "abs": mp.nstr(abs(v), 8),
                           "seconds": round(time.time() - t0, 2)})
        # floor = lowest dps whose value already agrees with the top rung
        top = values[-1]
        for d, v in zip(DPS_LADDER, values):
            if abs(top) != 0 and abs(v - top) <= reltol * abs(top):
                floor = d
                break
        audit[name] = {
            "ladder": ladder,
            "converged_value": mp.nstr(top, 12),
            "converged_abs": mp.nstr(abs(top), 8),
            "convergence_floor_dps": floor,
            "preregistered_dps_is_adequate": (
                floor is not None and floor <= DPS_BOX
            ),
        }
        print(f"  {name:22s} |F| = {mp.nstr(abs(top), 6):12s} "
              f"floor dps = {floor}  "
              f"(preregistered {DPS_BOX} "
              f"{'OK' if floor is not None and floor <= DPS_BOX else 'INADEQUATE'})",
              flush=True)
    return {"precision_audit": {
        "point": list(AUDIT_POINT),
        "ladder_dps": list(DPS_LADDER),
        "agreement_reltol": AUDIT_AGREE_RELTOL,
        "per_function": audit,
        "note": (
            "A box count below the convergence floor is a winding number over "
            "noise. count_zeros_box's integrality check does not catch that: "
            "noise winds to an integer too."
        ),
    }}


def run_stage2(audit: dict | None = None) -> dict:
    """Count zeros of each completed function in the two preregistered boxes.

    Not routed through ``battery``: a box count can raise (a zero on the
    contour makes the winding ill-posed), can exceed its wall-clock cap, or
    can be inadmissible on precision, and all three must be recorded as
    themselves rather than collapsed to a bool.  The gate #3 verdict is then
    assembled with battery's own rule -- zeta satisfies it and no rival does.

    A function whose stage-2a convergence floor exceeds ``DPS_BOX`` is
    **skipped, not run at DPS_BOX**: running it would produce a number that
    looks like a zero count and is not one.
    """
    ifaces = [epstein.zeta_interface(DPS_BOX), epstein.dh_interface(DPS_BOX)]
    ifaces += [epstein.epstein_interface(f, DPS_BOX) for f in FORMS]
    per_fn_audit = (audit or {}).get("precision_audit", {}).get("per_function", {})

    boxes = {}
    for box_name, box in BOXES.items():
        s0 = complex(box["re"][0], box["im"][0])
        s1 = complex(box["re"][1], box["im"][1])
        per_function = {}
        for iface in ifaces:
            name = iface["name"]
            fn_audit = per_fn_audit.get(name, {})
            if fn_audit and not fn_audit.get("preregistered_dps_is_adequate", True):
                rec = {"zero_count": None, "status": "inadmissible_precision",
                       "convergence_floor_dps": fn_audit.get("convergence_floor_dps"),
                       "seconds": 0.0,
                       "why": (
                           f"convergence floor dps="
                           f"{fn_audit.get('convergence_floor_dps')} exceeds the "
                           f"preregistered dps={DPS_BOX}; a count here would be a "
                           f"winding number over noise"
                       )}
                per_function[name] = rec
                print(f"  {box_name} {name:22s} SKIPPED [{rec['status']}]",
                      flush=True)
                continue
            t0 = time.time()
            try:
                n = iface["count_zeros_box"](s0, s1)
                rec = {"zero_count": int(n), "status": "ok"}
            except Exception as exc:  # ill-posed winding, non-finite sample
                rec = {"zero_count": None, "status": "error",
                       "error": f"{type(exc).__name__}: {exc}"}
            rec["seconds"] = round(time.time() - t0, 2)
            if rec["seconds"] > BOX_WALL_CLOCK_CAP_S and rec["status"] == "ok":
                rec["status"] = "ok_over_cap"
            per_function[iface["name"]] = rec
            print(f"  {box_name} {iface['name']:22s} "
                  f"count={rec['zero_count']} [{rec['status']}] "
                  f"({rec['seconds']:.1f}s)", flush=True)

        # The property is "no zeros in this box".  Satisfied iff count == 0.
        def holds(name):
            r = per_function[name]
            return None if r["zero_count"] is None else (r["zero_count"] == 0)

        rivals = ["davenport_heilbronn", "epstein_2_1_3", "epstein_1_1_6"]
        rival_holds = {n: holds(n) for n in rivals}
        zeta_holds = holds("riemann_zeta")
        surviving = [n for n, v in rival_holds.items() if v]
        undecided = [n for n, v in rival_holds.items() if v is None]

        # Gate #3's asymmetry: a single surviving rival forces VACUOUS, so an
        # undecided cell cannot overturn it.  DISTINGUISHES needs every rival
        # decided and every one of them failing, so an undecided cell does
        # block that.
        if surviving:
            verdict, forced_by = "VACUOUS", sorted(surviving)
        elif undecided or zeta_holds is None:
            verdict, forced_by = "UNDECIDED", None
        elif zeta_holds:
            verdict, forced_by = "DISTINGUISHES", None
        else:
            verdict, forced_by = "UNDECIDED", None

        boxes[box_name] = {
            "re": list(box["re"]),
            "im": list(box["im"]),
            "why_preregistered": box["why"],
            "dps": DPS_BOX,
            "per_function": per_function,
            "property_holds": {"riemann_zeta": zeta_holds, **rival_holds},
            "rivals_surviving": len(surviving),
            "rivals_undecided": sorted(undecided),
            "rivals_total": len(rivals),
            "shared_with": sorted(surviving),
            "distinguishes": True if verdict == "DISTINGUISHES" else (
                False if verdict == "VACUOUS" else None),
            "gate3_verdict": verdict,
            "verdict_forced_by": forced_by,
        }
    return {"boxes": boxes}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--stage", type=int, choices=(1, 2), default=None,
                    help="run only one stage (default: both)")
    ap.add_argument("--out", default=str(HERE / "results.json"))
    args = ap.parse_args()

    results = {
        "hunt": "r_f7cd45",
        "run_id": "5c3b062c-9fe6-431b-9bd3-25083ca3426d",
        "source_issue": "https://github.com/teal-sea/zeta-lab/issues/21",
        "gate": "docs/09-new-ontologies.md gate #3",
        "rivals": ["davenport_heilbronn", "epstein_2_1_3", "epstein_1_1_6"],
        "scope": (
            "Nothing here is evidence for or against RH (docs/08). Gate #3 is "
            "eliminative, never probative: prime-blind implies not an "
            "explanation, but prime-sensitive does not imply proof."
        ),
        "parameters": {
            "dps_claims": DPS_CLAIMS,
            "dps_box": DPS_BOX,
            "forms": [list(f) for f in FORMS],
            "Z_real_samples": Z_REAL_SAMPLES,
            "Z_real_tol": Z_REAL_TOL,
            "line_window": list(LINE_WINDOW),
            "coprime_pairs": [list(p) for p in COPRIME_PAIRS],
            "any_pairs": [list(p) for p in ANY_PAIRS],
            "coefficient_tol": COEFF_TOL,
            "box_wall_clock_cap_s": BOX_WALL_CLOCK_CAP_S,
        },
    }

    out_path = Path(args.out)
    if out_path.exists():
        results.update(json.loads(out_path.read_text()))

    if args.stage in (None, 1):
        print("stage 1, the five properties of issue #21")
        results.update(run_stage1())
    if args.stage in (None, 2):
        print("stage 2a, precision audit at the box height (instrument check)")
        results.update(run_precision_audit())
        print("stage 2b, the sixth property, preregistered boxes")
        results.update(run_stage2(results))

    out_path.write_text(json.dumps(results, indent=2) + "\n")
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
