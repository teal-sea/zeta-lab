#!/usr/bin/env python3
"""Require exactly the nine advertised reports, with the three standard axioms.

Uses the fail-closed log audit pattern from lean/qrh/scripts/check-axioms.py.
Run only after build.sh succeeds; this does not itself run a proof kernel.
"""
import re
import sys
from pathlib import Path

expected = {
    "HardyFirstZero.first_zero_on_line",
    "HardyFirstZero.zeta_product_re_neg",
    "HardyFirstZero.exists_zero_of_sign_data",
    "HardyFirstZero.gammaR_re_pos",
    "HardyFirstZero.gammaR_re_pos_first",
    "HardyFirstZero.first_zero_on_line_of_zeta_product",
    "HardyFirstZero.corrected_trapezoid",
    "HardyFirstZero.zeta_em4_error",
    "HardyFirstZero.em30_bound",
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
print("Accepted all nine reports: propext, Classical.choice, Quot.sound only.")
