"""Hunt R-E2EE73 probe: Scope caveat: compiler verdicts rest on a hand-written model, not LLVM semantics (Alive2 absent).

This probe measures and documents the exact boundaries of the compiler department's
verdicts:
1. Backend availability census (clang.exhaustive_i8, pymodel.refinement_i8, alive2.refinement).
2. Two-backend cross-check over all 10 fixtures (655,360 total points evaluated).
3. Power and blind spot measurement across all 4 planted lesions.
4. Rivals, surrogates, and decoys verification.
5. Unsupported IR taxonomy and rejection safety audit (confirming ModelUnsupported is raised).
6. Verification path independence measurement comparing the concrete and model backends.
"""

from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from compiler import catalog, semantics
from harness.departments import compiler_department as dept
from harness.independence import VerificationPath, agreement_bounds, compare
from harness.protocol import run_ablation, run_battery, run_nulls, run_power


def run_probe() -> dict:
    start_time = time.time()

    # 1. Backend Census
    status = semantics.backend_status()
    backends = semantics.available_backends()
    backend_census = {
        "available_backends": backends,
        "status_details": status,
        "clang_available": "clang.exhaustive_i8" in backends,
        "pymodel_available": "pymodel.refinement_i8" in backends,
        "alive2_available": "alive2.refinement" in backends,
        "primary_backend": semantics.BACKEND,
        "primary_backend_reason": semantics.BACKEND_REASON,
    }

    # 2. Exhaustive Cross-Check of All Fixtures (Model vs Clang)
    fixture_paths = sorted(catalog.FIXTURES.glob("*.ll"))
    fixture_cross_checks = []
    total_comparable = 0
    total_mismatches = 0

    for p in fixture_paths:
        fixture_name = p.stem
        ir_text = catalog.load_ir(fixture_name)
        check = semantics.model_matches_clang(ir_text)
        comparable = check["comparable"]
        mismatches = check["mismatches"]
        agrees = check["agrees"]
        total_comparable += comparable
        total_mismatches += mismatches
        fixture_cross_checks.append(
            {
                "fixture": fixture_name,
                "file": str(p.relative_to(REPO_ROOT)),
                "comparable_points": comparable,
                "mismatches": mismatches,
                "agrees": agrees,
            }
        )

    # 3. Lesion Power and Blind Spot Audit
    lesion_results = []
    for spec in catalog.LESIONS:
        lesioned = spec.apply(catalog.LESION_HOST)
        concrete_report = semantics.agreement(lesioned.source, lesioned.target)
        model_report = semantics.refinement(lesioned.source, lesioned.target)

        lesion_results.append(
            {
                "name": spec.name,
                "declared_magnitude": spec.magnitude,
                "visible_concretely": spec.visible_concretely,
                "concrete_agreement": {
                    "agrees": concrete_report.agrees,
                    "disagreements": concrete_report.disagreements,
                    "fraction": concrete_report.fraction,
                    "measured_defect": 1.0 - concrete_report.fraction,
                },
                "model_refinement": {
                    "refines": model_report.refines,
                    "violations": model_report.violations,
                    "value_violations": model_report.value_violations,
                    "poison_violations": model_report.poison_violations,
                    "ub_violations": model_report.ub_violations,
                    "fraction": model_report.fraction,
                    "measured_defect": 1.0 - model_report.fraction,
                },
            }
        )

    # 4. Harness Battery, Rivals, Surrogates, Decoys
    rival_results = []
    for rival in catalog.RIVALS:
        concrete_report = semantics.agreement(rival.source, rival.target)
        model_report = semantics.refinement(rival.source, rival.target)
        rival_results.append(
            {
                "name": rival.name,
                "instructions_removed": rival.instructions_removed(),
                "concrete_disagreements": concrete_report.disagreements,
                "model_violations": model_report.violations,
                "model_value_violations": model_report.value_violations,
                "model_poison_violations": model_report.poison_violations,
                "model_ub_violations": model_report.ub_violations,
                "both_backends_agree_on_count": (
                    concrete_report.disagreements == model_report.violations
                ),
            }
        )

    power_concrete = run_power(
        dept.BATTERY, dept.concrete_detector, payload=catalog.LESION_HOST, name="exhaustive_i8_run"
    )
    power_model = run_power(
        dept.BATTERY, dept.model_detector, payload=catalog.LESION_HOST, name="model_refinement_i8"
    )

    ablation_res = run_ablation(
        dept.BATTERY,
        dept.agreement_over(catalog.RIVALS[0]),
        tolerance=0.01,
        payload=list(dept.FULL_DOMAIN),
        name=f"agreement_of_{catalog.RIVALS[0].name}",
    )

    nulls_res = run_nulls(
        dept.BATTERY,
        dept.unguided_agreement,
        tolerance=0.01,
        name="exhaustive_agreement_fraction",
    )

    # 5. Unsupported IR Taxonomy & Rejection Safety
    unsupported_cases = [
        (
            "floating_point",
            "define i8 @f(i8 %x, i8 %y) {\nentry:\n  %r = fadd i8 %x, %y\n  ret i8 %r\n}\n",
        ),
        (
            "memory_load",
            "define i8 @f(i8 %x, i8 %y) {\nentry:\n  %p = alloca i8\n  store i8 %x, i8* %p\n  %r = load i8, i8* %p\n  ret i8 %r\n}\n",
        ),
        (
            "multi_block_cfg",
            "define i8 @f(i8 %x, i8 %y) {\nentry:\n  br label %next\nnext:\n  ret i8 %x\n}\n",
        ),
        (
            "i32_types",
            "define i32 @f(i32 %x, i32 %y) {\nentry:\n  %r = add i32 %x, %y\n  ret i32 %r\n}\n",
        ),
        (
            "phi_node",
            "define i8 @f(i8 %x, i8 %y) {\nentry:\n  %c = icmp eq i8 %x, 0\n  br i1 %c, label %t, label %f\nt:\n  br label %m\nf:\n  br label %m\nm:\n  %r = phi i8 [ %x, %t ], [ %y, %f ]\n  ret i8 %r\n}\n",
        ),
        (
            "freeze_instruction",
            "define i8 @f(i8 %x, i8 %y) {\nentry:\n  %r = freeze i8 %x\n  ret i8 %r\n}\n",
        ),
    ]

    rejection_audit = []
    for label, ir in unsupported_cases:
        caught = False
        exc_type = ""
        exc_msg = ""
        try:
            semantics.model_output_table(ir)
        except semantics.ModelUnsupported as e:
            caught = True
            exc_type = "ModelUnsupported"
            exc_msg = str(e)
        except Exception as e:
            caught = True
            exc_type = type(e).__name__
            exc_msg = str(e)

        rejection_audit.append(
            {
                "case": label,
                "caught": caught,
                "exception_type": exc_type,
                "exception_message": exc_msg,
                "is_ir_rejected_subclass": (
                    exc_type == "ModelUnsupported"
                    or issubclass(getattr(semantics, exc_type, object), semantics.IRRejected)
                ),
            }
        )

    # 6. Verification Path Independence Formalization
    clang_path = VerificationPath(
        name="concrete backend: clang -O0/-O2 binary",
        layers=(
            "LLVM IR text",
            "clang frontend parser/lowering",
            "code generation/compilation to native binary",
            "driver harness execution over 65536 inputs",
            "stdout byte capture",
            "exhaustive byte table comparison",
        ),
    )
    pymodel_path = VerificationPath(
        name="model backend: pure-Python poison-aware interpreter",
        layers=(
            "LLVM IR text",
            "regex IR parser (_parse)",
            "Python AST evaluation (_eval_program)",
            "poison and immediate UB propagation",
            "exhaustive tuple generation (65536 points)",
            "refinement relation check (value/poison/UB)",
        ),
    )
    indep_report = compare(clang_path, pymodel_path)
    indep_bounds = agreement_bounds(indep_report)

    independence_data = {
        "path_a": clang_path.name,
        "path_b": pymodel_path.name,
        "radius": indep_report.radius,
        "shared_layers": list(indep_report.shared),
        "reconvergent_layers": list(indep_report.reconvergent),
        "distinct_a": list(indep_report.distinct_a),
        "distinct_b": list(indep_report.distinct_b),
        "agreement_bounds": list(indep_bounds),
    }

    elapsed = time.time() - start_time

    results = {
        "meta": {
            "hunt": "r_e2ee73",
            "task": "Scope caveat: compiler verdicts rest on a hand-written model, not LLVM semantics (Alive2 absent)",
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "elapsed_seconds": round(elapsed, 3),
        },
        "backend_census": backend_census,
        "cross_check": {
            "fixtures_count": len(fixture_paths),
            "total_comparable_points": total_comparable,
            "total_mismatches": total_mismatches,
            "overall_agreement_fraction": (
                (total_comparable - total_mismatches) / total_comparable
                if total_comparable
                else 0.0
            ),
            "fixtures": fixture_cross_checks,
        },
        "lesion_power": {
            "concrete_has_power": power_concrete.has_power,
            "concrete_blind_to": list(power_concrete.blind_to),
            "model_has_power": power_model.has_power,
            "model_blind_to": list(power_model.blind_to),
            "lesions": lesion_results,
        },
        "rivals_and_nulls": {
            "rivals": rival_results,
            "ablation": {
                "baseline": ablation_res.baseline,
                "decoys": ablation_res.decoys,
                "survives": ablation_res.survives,
            },
            "nulls": {
                "observed": nulls_res.observed,
                "surrogates": nulls_res.surrogates,
                "survives": nulls_res.survives,
            },
        },
        "rejection_safety": rejection_audit,
        "independence": independence_data,
    }

    return results


def main() -> int:
    results = run_probe()
    out_path = Path(__file__).parent / "results.json"
    out_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"Wrote results to {out_path}")
    print(
        f"Census: backends={results['backend_census']['available_backends']}; "
        f"Cross-check: {results['cross_check']['total_comparable_points']} points, "
        f"{results['cross_check']['total_mismatches']} mismatches; "
        f"Alive2 absent: {not results['backend_census']['alive2_available']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
