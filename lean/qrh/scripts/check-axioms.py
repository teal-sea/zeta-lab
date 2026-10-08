#!/usr/bin/env python3
"""Fail closed on missing, duplicate or nonstandard Lean axiom reports."""
import re
import sys
from pathlib import Path

expected = {
    "QRH125.dirichlet_nonvanishing",
    "QRH125.logDeriv_eq_hadamardB_add_zero_sum",
    "QRH125.lorentzian_domination",
    "QRH125.lorentzian_domination_seven_eighths",
    "QRH125.kernel_endpoint_constants",
    "QRH125.small_moduli_cover",
    "ZetaLean.ComplexBall.contains_dirichletTermBallB",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
text = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
empty = re.findall(r"'([^']+)' does not depend on any axioms", text)
reports += [(name, "") for name in empty]
names = [name for name, _ in reports]
if set(names) != expected or len(names) != len(expected):
    raise SystemExit(f"Expected exactly {sorted(expected)}, received {names}")
for name, axioms in reports:
    unexpected = {a.strip() for a in axioms.split(",") if a.strip()} - allowed
    if unexpected:
        raise SystemExit(f"{name}: forbidden axioms {sorted(unexpected)}")
if re.search(r"\bsorryAx\b|\berror:", text):
    raise SystemExit("Lean reported a placeholder or error")
print(f"Accepted {len(reports)} axiom reports. These are partial lemmas, not Theorem 1(a).")
