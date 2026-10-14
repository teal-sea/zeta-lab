#!/usr/bin/env python3
"""Require exactly the twenty advertised reports, with the three standard axioms.

The fail-closed log audit of hunt #132 (`hunts/hardy_first_zero/lean/check_axioms.py`),
with this hunt's names. Run only after build.sh succeeds; this does not itself run a
proof kernel.
"""
import re
import sys
from pathlib import Path

TAGS = ("2102", "2501", "3042", "3293", "3758", "4091", "4332", "4800", "4977")
expected = {
    "HardyTenZeros.ten_zeros_on_line_below_fifty",
    "HardyFirstZero.first_zero_on_line",
    *(f"HardyTenZeros.zero_in_{tag}" for tag in TAGS),
    "HardyTenZeros.le_phi_tail",
    "HardyTenZeros.gammaR_re_pos_tail",
    "HardyTenZeros.gammaR_re_pos_short",
    "HardyTenZeros.window_132_fails_at_4977",
    "HardyTenZeros.emN_bound",
    "HardyTenZeros.cBox_contains",
    "HardyTenZeros.zeta_mem_mainBox",
    "HardyTenZeros.contains_cpow_mul_coarsen",
    "HardyTenZeros.zero_of_tables",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
text = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
names = [name for name, _ in reports]
if set(names) != expected or len(names) != len(expected):
    raise SystemExit(f"Expected exactly {sorted(expected)}, received {names}")
for name, axioms in reports:
    actual = [a.strip() for a in axioms.split(",")]
    if set(actual) != allowed or len(actual) != len(allowed):
        raise SystemExit(f"{name}: expected the three standard axioms, received {actual}")
if re.search(r"\bsorryAx\b|\berror:", text):
    raise SystemExit("Lean reported a placeholder or error")
print(f"Accepted all {len(expected)} reports: propext, Classical.choice, Quot.sound only.")
