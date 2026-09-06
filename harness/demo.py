"""``python -m harness.demo``, the whole architecture, in one run.

Six departments, number theory at arbitrary precision, curves over finite
fields, compiler rewrites, cron schedules, statistical model evaluation,
and the verification machinery itself, pass through the same referee, and
then the referee is turned on its own kind: a hollow battery is shown
producing a green verdict, and the audit is shown catching it, alongside a
statement of what the audit admits it cannot catch.

Nothing printed here is a stored number. Every verdict re-derives when this
runs, which is why the demo takes tens of seconds rather than none.

Usage::

    .venv/bin/python -m harness.demo                # everything
    .venv/bin/python -m harness.demo --department stateval
    .venv/bin/python -m harness.demo --json out.json   # machine-readable too

This module is an application, not part of the domain-agnostic seam: it
imports the departments, and may say their names.
"""

from __future__ import annotations

import argparse
import json
import sys
import time

from harness import departments as _departments
from harness.integrity import (
    AUDIT_BLIND_SPOTS,
    CALIBRATED,
    audit_department,
    report_claim,
)
from harness.protocol import get_department, run_battery, run_detector, run_null_band

_RULE = "=" * 72
_THIN = "-" * 72


def _section(title: str) -> None:
    print(f"\n{_RULE}\n{title}\n{_RULE}")


def _department_block(name: str, collect: list[dict]) -> None:
    department = get_department(name)
    started = time.monotonic()
    print(f"\nDEPARTMENT: {name}")
    print(f"  {department.summary}")
    print(f"  scope of a pass: {department.scope}")

    for reference in department.reference_claims:
        report = report_claim(department, reference.claim, name=reference.name)
        collect.append(report.to_dict())
        marker = "!!" if report.dangerous else "  "
        print(f"{marker}  claim {reference.name!r}: {report.verdict.summary()}")

    for detector in department.detectors:
        verdict = run_detector(department.battery, detector)
        print(f"    detector {detector.name}: {verdict.summary()}")

    audit = audit_department(department)
    print(f"    battery integrity: {audit.grade}"
          f" ({sum(1 for c in audit.checks if c.status == 'pass')}"
          f"/{len(audit.checks)} checks pass)")
    if audit.unseen_lesions:
        print(f"    measured power limit: no detector sees {', '.join(audit.unseen_lesions)}")
    for reason in audit.dependence:
        print(f"    dependence: {reason.split(':')[0]}")
    print(f"    [{time.monotonic() - started:.1f}s, all re-derived]")


def _the_turn(collect: list[dict]) -> None:
    """The moment the machinery turns on itself."""
    from harness.departments.referee_department import (
        BATTERY,
        DEPARTMENT,
        SPECIMEN,
        build_sham_431cc74,
        integrity_pass_count,
    )

    _section("THE TURN: a hollow battery, caught producing a green verdict")
    sham = build_sham_431cc74()
    print(
        "\nThe sham battery commit 431cc74 replaced, reconstructed: placeholder\n"
        "instruments, and rival payloads carrying a virtual_a_p field a claim\n"
        "can read as a label. It passes structural admission. Its own\n"
        "'distinguishing' claim, run through its own battery:"
    )
    report = report_claim(sham, lambda p: "virtual_a_p" not in p, name="no-virtual-trace")
    collect.append(report.to_dict())
    print(f"\n  {report.headline()}")
    symmetry = report.integrity.check("payload-symmetry")
    print(f"  caught by: {symmetry.name}, {symmetry.evidence.split(';')[0]}")
    print(
        "  and note what PASSES on this sham: calibration re-derives, its\n"
        "  co-designed detector has mechanical power. Structural completeness\n"
        "  is not verification; only the audit separates them."
    )

    _section("THE REFEREE, REFEREED: is the audit itself worth anything?")
    print(
        "\nThe referee department's battery: batteries are the subjects, sham\n"
        "modes are the planted violations, the audit is the detector."
    )
    for reference in DEPARTMENT.reference_claims:
        verdict = run_battery(BATTERY, reference.claim, name=reference.name)
        print(f"  claim {reference.name!r}: {verdict.summary()}")
    detector = DEPARTMENT.detectors[0]
    verdict = run_detector(BATTERY, detector)
    print(f"  the audit as detector: {verdict.summary()}")
    band = run_null_band(
        BATTERY, integrity_pass_count, draws=1, observed=integrity_pass_count(SPECIMEN),
        name="audit-pass-count",
    )
    print(f"  against unguided bundles: {band.summary()}")
    print("\n  and what the audit admits it cannot catch (printed on every report):")
    for mode in AUDIT_BLIND_SPOTS:
        print(f"    blind spot: {mode.name}")
        print(f"      countermeasure: {mode.countermeasure}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--department", help="run one department only")
    parser.add_argument("--json", dest="json_path", help="write machine-readable reports here")
    parser.add_argument("--skip-slow", action="store_true",
                        help="skip the departments with expensive payloads (zeta, compiler)")
    args = parser.parse_args(argv)

    _section("ZETA LAB, six departments, one referee, and the referee refereed")
    print(
        "\nEvery claim below is paired with the integrity of the battery that\n"
        "judged it. A green claim from a hollow battery renders as dangerous,\n"
        "because it is."
    )

    names = list(_departments.KNOWN_DEPARTMENTS)
    if args.department:
        names = [args.department]
    if args.skip_slow:
        names = [n for n in names if n not in ("zeta", "compiler")]
    for name in names:
        _departments.load(name)

    collect: list[dict] = []
    _section("THE DEPARTMENTS")
    for name in names:
        _department_block(name, collect)

    if args.department is None:
        _the_turn(collect)

    _section("READING THIS HONESTLY")
    print(
        "\nA claim that 'distinguishes' has survived this battery, nothing\n"
        "more. Scope lines say exactly what that licenses. CALIBRATED means\n"
        "the battery survives the named sham classes; two classes defeat it\n"
        "by construction and are declared above, with their countermeasure.\n"
        "Per docs/08: nothing here is evidence for or against RH."
    )

    if args.json_path:
        with open(args.json_path, "w", encoding="utf-8") as fh:
            json.dump(collect, fh, indent=2)
        print(f"\nmachine-readable reports: {args.json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
