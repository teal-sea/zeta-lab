"""Plant failures in the CI axiom log so a missing check cannot pass silently."""
import subprocess
import sys
from pathlib import Path

import pytest

AUDIT = Path(__file__).parent / "lean" / "check_axioms.py"
NAMES = (
    "first_zero_on_line", "zeta_product_re_neg", "exists_zero_of_sign_data",
    "gammaR_re_pos", "gammaR_re_pos_first", "first_zero_on_line_of_zeta_product",
    "corrected_trapezoid", "zeta_em4_error", "em30_bound",
)
CLEAN = "\n".join(
    f"'HardyFirstZero.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
    for name in NAMES
)


@pytest.mark.parametrize("log, passes", [
    (CLEAN, True),
    (CLEAN.replace("axioms: [", "axioms:\n [").replace(", ", ",\n "), True),
    ("", False),
    ("\n".join(CLEAN.splitlines()[1:]), False),
    (CLEAN + "\n" + CLEAN.splitlines()[0], False),
    (CLEAN.replace("Quot.sound", "sorryAx", 1), False),
    (CLEAN.replace("Quot.sound", "Lean.ofReduceBool", 1), False),
    (CLEAN.replace("Quot.sound", "unreviewedAssumption", 1), False),
    (CLEAN.replace("first_zero_on_line'", "other_result'", 1), False),
    (CLEAN.replace("Quot.sound]", "Quot.sound", 1), False),
    (CLEAN + "\nerror: failed to compile", False),
    (CLEAN + "\nwarning: declaration uses sorryAx", False),
])
def test_axiom_audit(tmp_path, log, passes):
    path = tmp_path / "build.log"
    path.write_text(log)
    result = subprocess.run(
        [sys.executable, str(AUDIT), str(path)], capture_output=True, text=True, timeout=10,
    )
    assert (result.returncode == 0) is passes, result.stdout + result.stderr
