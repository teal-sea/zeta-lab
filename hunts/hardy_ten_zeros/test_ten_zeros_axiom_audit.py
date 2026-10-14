"""Plant failures in the CI axiom log so a missing check cannot pass silently."""
import subprocess
import sys
from pathlib import Path

import pytest

AUDIT = Path(__file__).parent / "lean" / "check_axioms.py"
TAGS = ("2102", "2501", "3042", "3293", "3758", "4091", "4332", "4800", "4977")
NAMES = (
    "HardyTenZeros.ten_zeros_on_line_below_fifty", "HardyFirstZero.first_zero_on_line",
    *(f"HardyTenZeros.zero_in_{tag}" for tag in TAGS),
    "HardyTenZeros.le_phi_tail", "HardyTenZeros.gammaR_re_pos_tail",
    "HardyTenZeros.gammaR_re_pos_short", "HardyTenZeros.window_132_fails_at_4977",
    "HardyTenZeros.emN_bound",
    "HardyTenZeros.cBox_contains", "HardyTenZeros.zeta_mem_mainBox",
    "HardyTenZeros.contains_cpow_mul_coarsen", "HardyTenZeros.zero_of_tables",
)
CLEAN = "\n".join(
    f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in NAMES
)


def test_twenty_reports():
    assert len(NAMES) == 20 == len(set(NAMES))


@pytest.mark.parametrize("log, passes", [
    (CLEAN, True),
    (CLEAN.replace("axioms: [", "axioms:\n [").replace(", ", ",\n "), True),
    ("", False),
    ("\n".join(CLEAN.splitlines()[1:]), False),
    ("\n".join(CLEAN.splitlines()[:-1]), False),
    (CLEAN + "\n" + CLEAN.splitlines()[0], False),
    (CLEAN.replace("Quot.sound", "sorryAx", 1), False),
    (CLEAN.replace("Quot.sound", "Lean.ofReduceBool", 1), False),
    (CLEAN.replace("Quot.sound", "unreviewedAssumption", 1), False),
    (CLEAN.replace("zero_in_4977'", "zero_in_4978'", 1), False),
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
