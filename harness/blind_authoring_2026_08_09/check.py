"""Sealed audit runner for the blind-authoring experiment.

Usage:  python3 check.py /abs/path/to/your/department.py

Your module must expose a module-level name ``DEPARTMENT`` bound to a
``harness.protocol.Department``.

This prints the integrity grade and the pass/fail/unknown status of each
named check.  It deliberately does NOT print the check evidence strings, the
audit's declared blind-spot catalog, or any other internal of the audit.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

REPO = Path("/Users/thomas/Zeta")
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from harness.integrity import audit_department  # noqa: E402
from harness.protocol import department_reasons  # noqa: E402


def _load(path: str):
    spec = importlib.util.spec_from_file_location("blind_candidate", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: python3 check.py /abs/path/to/department.py")
        return 2
    module = _load(sys.argv[1])
    department = getattr(module, "DEPARTMENT", None)
    if department is None:
        print("FAIL: module exposes no DEPARTMENT")
        return 1

    reasons = department_reasons(department)
    if reasons:
        print("NOT ADMISSIBLE:")
        for reason in reasons:
            print("  -", reason)
        return 1

    report = audit_department(department)
    print(f"grade: {report.grade}")
    for result in report.checks:
        print(f"  [{result.status:>7}] {result.name}")
    return 0 if report.grade == "CALIBRATED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
