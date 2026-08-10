"""Score the ten blind-authored batteries under the pre-change audit and the new one.

Frozen decision rule (docs/23 §7): no blind-authored battery is edited, for any
reason. This script only reads them.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

BLIND = Path(__file__).resolve().parent
REPO = BLIND.parents[1]
# ``integrity_before`` is the audit as of e7d52b6, the pre-registration commit.
# Produce it with:  git show e7d52b6:harness/integrity.py > /tmp/integrity_before.py
for path in (str(REPO), "/tmp"):
    if path not in sys.path:
        sys.path.insert(0, path)

import integrity_before as BEFORE  # noqa: E402  the audit as of e7d52b6
from harness import integrity as AFTER  # noqa: E402
from harness.protocol import department_reasons, run_battery  # noqa: E402

HOLLOW = [f"party0{i}" for i in range(1, 7)]
HONEST = ["party07", "party08", "party09", "party10"]

_NEW_CHECKS = ("rival-separator-abundance", "detector-claim-agreement")


def load(party: str):
    path = BLIND / party / "department.py"
    if not path.exists():
        return None
    spec = importlib.util.spec_from_file_location(f"blind_{party}", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    try:
        spec.loader.exec_module(module)
    except Exception as exc:  # noqa: BLE001
        return {"party": party, "load_error": f"{type(exc).__name__}: {exc}"}
    return module


def score(party: str, kind: str) -> dict:
    module = load(party)
    if module is None:
        return {"party": party, "kind": kind, "status": "missing"}
    if isinstance(module, dict):
        return {**module, "kind": kind, "status": "load-error"}
    department = getattr(module, "DEPARTMENT", None)
    if department is None:
        return {"party": party, "kind": kind, "status": "no-DEPARTMENT"}

    row: dict = {"party": party, "kind": kind, "status": "ok"}
    row["admissible"] = not department_reasons(department)

    try:
        before = BEFORE.audit_department(department)
        row["before_grade"] = before.grade
        row["before_failures"] = [c.name for c in before.checks if c.status == "fail"]
        row["before_unknowns"] = [c.name for c in before.checks if c.status == "unknown"]
    except Exception as exc:  # noqa: BLE001
        row["before_grade"] = f"RAISED {type(exc).__name__}"

    try:
        after = AFTER.audit_department(department)
        row["after_grade"] = after.grade
        row["after_failures"] = [c.name for c in after.checks if c.status == "fail"]
        row["undecided"] = list(after.undecided)
        row["new_checks"] = {
            c.name: c.status for c in after.checks if c.name in _NEW_CHECKS
        }
        row["new_evidence"] = {
            c.name: c.evidence[:260] for c in after.checks
            if c.name in _NEW_CHECKS and c.status != "pass"
        }
    except Exception as exc:  # noqa: BLE001
        row["after_grade"] = f"RAISED {type(exc).__name__}: {exc}"

    absurd = getattr(module, "ABSURD_CLAIM", None)
    row["absurd_text"] = getattr(module, "ABSURD_CLAIM_TEXT", "")
    if callable(absurd):
        try:
            verdict = run_battery(department.battery, absurd, name="absurd")
            row["absurd_distinguishes"] = bool(verdict.distinguishes)
            row["absurd_summary"] = verdict.summary()
        except Exception as exc:  # noqa: BLE001
            row["absurd_distinguishes"] = f"RAISED {type(exc).__name__}"
    else:
        row["absurd_distinguishes"] = None
    return row


def main() -> None:
    rows = [score(p, "hollow") for p in HOLLOW] + [score(p, "honest") for p in HONEST]
    print(json.dumps(rows, indent=1, default=str))

    print("\n\n===================== SUMMARY =====================")
    hdr = f"{'party':9s} {'kind':7s} {'before':21s} {'after':21s} {'absurd?':9s} caught-by"
    print(hdr)
    print("-" * len(hdr))
    for row in rows:
        if row.get("status") != "ok":
            print(f"{row['party']:9s} {row['kind']:7s} {row.get('status')}")
            continue
        caught = [n for n, s in row.get("new_checks", {}).items() if s == "fail"]
        if row.get("undecided"):
            caught.append(f"undecided:{','.join(row['undecided'])}")
        print(
            f"{row['party']:9s} {row['kind']:7s} {str(row.get('before_grade')):21s} "
            f"{str(row.get('after_grade')):21s} {str(row.get('absurd_distinguishes')):9s} "
            f"{', '.join(caught) or '-'}"
        )

    ok = [r for r in rows if r.get("status") == "ok"]
    hollow_ok = [r for r in ok if r["kind"] == "hollow"]
    honest_ok = [r for r in ok if r["kind"] == "honest"]

    succeeded = [
        r for r in hollow_ok
        if r.get("before_grade") == "CALIBRATED" and r.get("absurd_distinguishes") is True
    ]
    print(f"\nhollowing succeeded under the OLD audit: {len(succeeded)}/{len(hollow_ok)}")
    caught_now = [r for r in succeeded if r.get("after_grade") != "CALIBRATED"]
    print(f"  of those, caught by the NEW audit:      {len(caught_now)}/{len(succeeded)}")
    for r in succeeded:
        verdict = "CAUGHT" if r.get("after_grade") != "CALIBRATED" else "SURVIVES"
        print(f"    {r['party']}: {verdict} ({r.get('after_grade')})")

    honest_clean = [r for r in honest_ok if r.get("before_grade") == "CALIBRATED"]
    newly_rejected = [r for r in honest_clean if r.get("after_grade") != "CALIBRATED"]
    print(f"\nhonest CALIBRATED under the OLD audit:    {len(honest_clean)}/{len(honest_ok)}")
    print(f"  newly rejected by the NEW audit:       {len(newly_rejected)}")
    for r in newly_rejected:
        print(f"    {r['party']}: {r.get('after_grade')} — {r.get('after_failures')} {r.get('undecided')}")


if __name__ == "__main__":
    main()
