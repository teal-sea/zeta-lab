"""The fail-closed axiom audit of hunt #137's build log, with planted failures.

`lean/check_axioms.py` is what turns a `build.sh` log into an accepted or refused build. Its
expected sets are written out by hand, so two things can drift: the names it expects and the
names the check files actually print. These tests take the names from the `#print axioms`
lines of the check files that each `build.sh` mode runs, build a clean log from them, require
the audit to accept it, and require it to refuse each planted fault.
"""
import re
import subprocess
import sys
from pathlib import Path

import pytest

LEAN = Path(__file__).parent / "lean"
AUDIT = LEAN / "check_axioms.py"
BUILD = LEAN / "build.sh"
MODES = {
    "": ["CheckAxioms.lean"],
    "--assembly": ["CheckAxioms.lean", "CheckAssembly.lean"],
    "--full": [
        "CheckAxioms.lean",
        "CheckAssembly.lean",
        "RHHeight/CheckGammaIncrement.lean",
        "RHHeight/CheckHorizontalLegs.lean",
        "RHHeight/CheckExactArgument.lean",
        "RHHeight/CheckLowHeight.lean",
        "CheckMain.lean",
    ],
    "--full100": [
        "CheckAxioms.lean", "CheckAssembly.lean",
        "RHHeight/CheckGammaIncrement.lean", "RHHeight/CheckHorizontalLegs.lean",
        "RHHeight/CheckExactArgument.lean", "RHHeight/CheckLowHeight.lean",
        "CheckMain.lean", "CheckMain100.lean",
    ],
}
COUNTS = {"": 11, "--assembly": 14, "--full": 72, "--full100": 100}
STANDARD = "[propext, Classical.choice, Quot.sound]"


def printed_names(mode: str) -> list[str]:
    names = []
    for rel in MODES[mode]:
        for line in (LEAN / rel).read_text(encoding="utf-8").splitlines():
            m = re.match(r"#print axioms\s+(\S+)\s*$", line)
            if m:
                names.append(m.group(1))
    return names


def clean_log(mode: str) -> str:
    lines = ["== Zeta23.Defs 00:00:00"]
    lines += [f"'{name}' depends on axioms: {STANDARD}" for name in printed_names(mode)]
    lines.append("== done 00:00:01")
    return "\n".join(lines)


def audit(tmp_path: Path, log: str, mode: str) -> subprocess.CompletedProcess:
    path = tmp_path / "build.log"
    path.write_text(log, encoding="utf-8")
    args = [sys.executable, str(AUDIT), str(path)] + ([mode] if mode else [])
    return subprocess.run(args, capture_output=True, text=True, timeout=30)


@pytest.mark.parametrize("mode", list(MODES))
def test_the_check_files_print_the_advertised_number_of_distinct_reports(mode):
    names = printed_names(mode)
    assert len(names) == COUNTS[mode] == len(set(names))


def test_the_final_theorem_is_among_the_audited_reports():
    assert "RHHeight.rh_height_fifty" in printed_names("--full")
    assert "RHHeight.rh_height_fifty" not in printed_names("--assembly")
    assert "RHHeight100.rh_height_hundred" in printed_names("--full100")
    assert "RHHeight100.zero_count_hundred" in printed_names("--full100")
    assert "RHHeight100.rh_height_hundred" not in printed_names("--full")


def test_build_sh_runs_every_check_file_of_the_full_mode():
    text = BUILD.read_text(encoding="utf-8")
    for rel in MODES["--full100"]:
        assert rel in text, f"build.sh does not run {rel}"
    for tag in ("5297", "5644", "5934", "6083", "6511", "67075", "6954",
                "7206", "7570", "7714", "7933", "8291", "8473", "8742",
                "8880", "9249", "9465", "95865", "9883"):
        assert tag in text
    assert "TwentyNineZeros Main100" in text


@pytest.mark.parametrize("mode", list(MODES))
def test_a_clean_log_is_accepted(tmp_path, mode):
    result = audit(tmp_path, clean_log(mode), mode)
    assert result.returncode == 0, result.stdout + result.stderr
    assert f"Accepted all {COUNTS[mode]} reports" in result.stdout


def _planted(log: str) -> list[tuple[str, str]]:
    lines = log.splitlines()
    reports = [i for i, line in enumerate(lines) if "depends on axioms" in line]
    first, last = reports[0], reports[-1]
    drop = lambda i: "\n".join(lines[:i] + lines[i + 1:])
    return [
        ("empty log", ""),
        ("first report missing", drop(first)),
        ("last report missing", drop(last)),
        ("a report duplicated", log + "\n" + lines[first]),
        ("sorryAx in a report", log.replace("Quot.sound]", "Quot.sound, sorryAx]", 1)),
        ("ofReduceBool in place of Quot.sound", log.replace("Quot.sound", "Lean.ofReduceBool", 1)),
        ("an axiom missing from a report", log.replace(", Quot.sound]", "]", 1)),
        ("a renamed report", log.replace("'RHHeight.", "'RHHeight.x", 1)),
        ("a sorry warning, backticks", log + "\nwarning: declaration uses `sorry`"),
        ("a sorry warning, straight quotes", log + "\nwarning: declaration uses 'sorry'"),
        ("a Lean error", log + "\nerror: unknown identifier"),
        ("a coded Lean error", log + "\nMain100.lean:4:2: error(lean.unknownIdentifier): unknown identifier"),
        ("a plain Lean warning", log + "\nwarning: unused simp argument"),
        ("a coded Lean warning", log + "\nMain100.lean:4:2: warning(lean.unusedVariables): unused"),
        ("a truncated report", log + "\n'RHHeight.extra' depends on axioms: [propext,"),
        ("a diagnostic before completion", log.replace("== done 00:00:01", "warning: unused variable\n== done 00:00:01")),
        ("trailing garbage", log + "\nextra data"),
        ("the build stopped early", log.replace("== done 00:00:01", "")),
    ]


@pytest.mark.parametrize("mode", list(MODES))
def test_planted_faults_are_refused(tmp_path, mode):
    for label, log in _planted(clean_log(mode)):
        result = audit(tmp_path, log, mode)
        assert result.returncode != 0, f"{mode or 'skeleton'}: accepted with {label}"


def test_pinned_upstream_warning_only_is_allowed(tmp_path):
    import json
    baseline = json.loads((LEAN / "legacy_warnings.json").read_text())
    key, record = next(iter(baseline.items()))
    line = record["warnings"][0]
    log = clean_log("--full100").replace("== done 00:00:01", line + "\n== done 00:00:01")
    assert audit(tmp_path, log, "--full100").returncode == 0
    assert audit(tmp_path, log.replace(line, line + " changed"), "--full100").returncode != 0
    assert audit(tmp_path, log.replace(line, line + "\n" + line), "--full100").returncode != 0
    assert key.startswith("Zeta23/") or key.startswith("ZetaLean/")


def test_a_log_is_refused_in_the_wrong_mode(tmp_path):
    assert audit(tmp_path, clean_log("--full"), "").returncode != 0
    assert audit(tmp_path, clean_log("--full"), "--assembly").returncode != 0
    assert audit(tmp_path, clean_log("--assembly"), "--full").returncode != 0
    assert audit(tmp_path, clean_log(""), "--full").returncode != 0
