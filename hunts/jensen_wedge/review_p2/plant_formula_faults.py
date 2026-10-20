"""Formula plants against phase 2's own test suite (review item P, `REVIEW_PHASE2.md`).

Run from the repository root (about 5 minutes, one core):

    .venv/bin/python hunts/jensen_wedge/review_p2/plant_formula_faults.py

Copies `hunts/jensen_wedge/*.py` and `*.json` into a temporary directory, applies one
formula fault at a time to the copy of `effective.py`, and runs the copy of
`test_effective.py` there in a subprocess. Nothing in the tree is edited and nothing
is imported from `effective.py`. Each fault makes a bound unsoundly optimistic; a
suite that covers the step should go red.

Writes `plants_review_p2.json` next to this file.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
HUNT = HERE.parent
ROOT = HUNT.parents[1]

PLANTS = {
    "none (control)": None,
    "Lemma L: cubic Taylor constant 8/3 -> 8/15 (C_rho 5x too small)":
        ("r3 = (1 + a1) * (ab(8) / 3) * m3", "r3 = (1 + a1) * (ab(8) / 15) * m3"),
    "Lemma L: cubic Taylor constant 8/3 -> 8/30 (C_rho 10x too small)":
        ("r3 = (1 + a1) * (ab(8) / 3) * m3", "r3 = (1 + a1) * (ab(8) / 30) * m3"),
    "Lemma D(ii): Cauchy radius n/4 where only n/8 is available (2^k too small)":
        ("(2 * ab(RHO - RHO_D) ** k * sub.n_lo", "(2 * ab(Fraction(1, 4)) ** k * sub.n_lo"),
    "Lemma B: Sturm constants 2.47, 6.07 -> 0.247, 0.607 (r 3.2x too small)":
        ("s247 = (ab(Fraction(247, 100)) + ab(Fraction(607, 100)) / ab(d_min)).sqrt()",
         "s247 = (ab(Fraction(247, 1000)) + ab(Fraction(607, 1000)) / ab(d_min)).sqrt()"),
}


def run_one(label: str, plant) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        dest = Path(tmp) / "hunts" / "jensen_wedge"
        dest.mkdir(parents=True)
        for f in list(HUNT.glob("*.py")) + list(HUNT.glob("*.json")):
            shutil.copy(f, dest / f.name)
        (Path(tmp) / "zeta").symlink_to(ROOT / "zeta")
        if plant is not None:
            src = (dest / "effective.py").read_text()
            old, new = plant
            assert src.count(old) == 1, f"plant site not found once: {old!r}"
            (dest / "effective.py").write_text(src.replace(old, new))
        proc = subprocess.run(
            [sys.executable, "-m", "pytest", "-q", "-n0", "-p", "no:cacheprovider",
             "hunts/jensen_wedge/test_effective.py"],
            cwd=tmp, capture_output=True, text=True, timeout=1800,
        )
        tail = proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else proc.stderr[-300:]
        passed = int(m.group(1)) if (m := re.search(r"(\d+) passed", tail)) else 0
        failed = int(m.group(1)) if (m := re.search(r"(\d+) failed", tail)) else 0
        failed_names = re.findall(r"FAILED \S+::(\S+)", proc.stdout)
        return {"plant": label, "passed": passed, "failed": failed, "failed_tests": failed_names,
                "suite_red": failed > 0 or proc.returncode != 0, "summary": tail}


def main() -> None:
    out = [run_one(label, plant) for label, plant in PLANTS.items()]
    for r in out:
        print(f"{'RED  ' if r['suite_red'] else 'green'}  {r['plant']}: {r['summary']}", flush=True)
    (HERE / "plants_review_p2.json").write_text(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
