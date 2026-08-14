"""`hunts/` is the probe area, and this file is what keeps it one.

The spine's admission rule is **no department without a battery**
(`harness/README.md`). Hunts are deliberately exempt from that rule — they are
where an idea gets chased before anything has tried to kill it — so the
exemption is paid for here instead:

1. **The classification is on disk.** A hunt directory without `hunts/README.md`
   declaring probes non-results would let a probe pass for a department.
2. **The reserved vocabulary holds.** `docs/17` §1.4 and `CLAUDE.md` make
   "certified" the property of `zeta/rigor.py` alone. A hunt may measure and
   observe; it may not certify.
3. **The load-bearing confound is measured, not remembered.** This is the one
   that matters, and it is the reason Hunt #2's headline was withdrawn.

On (3): `zeta/detector.py` computes ``residue(c) = [arithmetic side] − [sum
over ON-LINE zeros]``, and its own docstring names the caveat — *a missing
on-line zero produces a residue indistinguishable from an off-line zero*.
That sentence is easy to read past. The test below makes it a number: ζ, whose
Euler product is exact (factorization defect ~1e-32), is given a zero list with
one on-line zero removed, and produces an O(1) residue anyway. Any hunt reading
an O(1) residue as evidence of off-line zeros must therefore first establish
that its on-line list is complete.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest
from mpmath import mp

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

_HUNTS = _REPO_ROOT / "hunts"

#: ζ's first two ordinates, the only ones below the t_max the hunt scanned.
GAMMA_1 = 14.134725141734694
GAMMA_2 = 21.022039638771555


# ---------------------------------------------------------------------------
# 1. The classification exists and says what it must
# ---------------------------------------------------------------------------


def test_the_hunts_area_declares_itself_a_probe_area() -> None:
    readme = _HUNTS / "README.md"
    assert readme.is_file(), "hunts/ exists with no README classifying it"
    text = readme.read_text(encoding="utf-8").lower()
    assert "not a result" in text or "nothing in `hunts/` is a result" in text.lower(), (
        "hunts/README.md must state that a hunt is a probe, not a result"
    )
    assert "no department without a battery" in text, (
        "hunts/README.md must cite the admission rule it is the exception to"
    )


def test_every_hunt_directory_is_covered_by_the_case_log() -> None:
    """A hunt that appears on disk without a case-log entry is unclassified."""
    if not _HUNTS.is_dir():  # pragma: no cover - hunts/ is optional
        pytest.skip("no hunts/ directory")
    log = (_HUNTS / "README.md").read_text(encoding="utf-8")
    for child in sorted(_HUNTS.iterdir()):
        if not child.is_dir() or child.name.startswith((".", "_")):
            continue
        assert child.name in log, (
            f"hunt {child.name!r} has no entry in hunts/README.md's case log, so "
            "nothing on disk says whether its claims survived anything"
        )


def test_no_hunt_claims_the_reserved_word() -> None:
    """'Certified' belongs to zeta/rigor.py. A probe may never claim it."""
    if not _HUNTS.is_dir():  # pragma: no cover
        pytest.skip("no hunts/ directory")
    offenders = []
    for path in _HUNTS.rglob("*"):
        if path.suffix.lower() not in {".py", ".md", ".json"}:
            continue
        if ".lake" in path.parts:
            # Lean build trees are *downloaded dependencies*, not probe files:
            # `hunts/frontier_math/zeta23ext/.lake/` holds Mathlib, whose own
            # `CITATION.md` contains the word.  Scanning it made this gate fail
            # for any session that had actually built the Lean arm — which is
            # to say, it only fired at the one moment it should have stayed
            # quiet.  `test_zeta23ext_imports._lean_files` already skips
            # `.lake` for the same reason.
            continue
        if path.name == "README.md" and path.parent == _HUNTS:
            continue  # the case log may quote the rule it enforces
        text = path.read_text(encoding="utf-8", errors="ignore").lower()
        if "certified" in text:
            offenders.append(str(path.relative_to(_REPO_ROOT)))
    assert not offenders, f"reserved word 'certified' used in probe files: {offenders}"


# ---------------------------------------------------------------------------
# 2. The confound, measured rather than remembered
# ---------------------------------------------------------------------------


def _zeta_arch_bracket(r):
    return mp.re(mp.digamma(mp.mpf(1) / 4 + mp.mpc(0, 1) * r / 2)) - mp.log(mp.pi)


def _zeta_residue_scan(online_zeros):
    from hunts.factorization_vs_position.detector import generalized_residue_scan
    from zeta.factorization import log_derivative_coefficients

    coefficients = [0.0] + [1.0] * 2000
    return generalized_residue_scan(
        c_values=np.linspace(10.0, 20.0, 11),
        b=log_derivative_coefficients(coefficients, 2000),
        archimedean_bracket_fn=_zeta_arch_bracket,
        online_zeros=online_zeros,
        has_pole=True,
        a=0.25,
        n_max=2000,
    )


def test_zeta_with_a_complete_on_line_list_is_silent() -> None:
    """The control: ζ's on-line zeros account for the whole explicit formula."""
    scan = _zeta_residue_scan([GAMMA_1, GAMMA_2])
    assert scan["max_abs_residue"] < 0.01, (
        f"ζ should be near-silent with a complete list; got {scan['max_abs_residue']}"
    )


@pytest.mark.slow
def test_a_missing_on_line_zero_forges_the_off_line_signal() -> None:
    """**The load-bearing test.** Perfect Euler product, O(1) position residue.

    ζ has factorization defect ~1e-32 and every zero on the line. Remove one
    zero from the *supplied list* and the residue jumps by more than two orders
    of magnitude — reproducing, at zero factorization defect, exactly the
    signal Hunt #2 read as "zeros off the critical line".

    The consequence is the rule in ``hunts/README.md``: a residue is evidence
    of off-line zeros only when paired with an independent completeness check
    of the on-line list (``zeta.detector.online_list_is_complete``).
    """
    from zeta.factorization import factorization_defect

    defect = float(factorization_defect([0.0] + [1.0] * 2000, 2000))
    assert defect < 1e-20, "ζ must factor exactly for this test to mean anything"

    complete = _zeta_residue_scan([GAMMA_1, GAMMA_2])["max_abs_residue"]
    lesioned = _zeta_residue_scan([GAMMA_2])["max_abs_residue"]

    assert lesioned > 1.0, (
        f"the lesion should forge an O(1) residue; got {lesioned}"
    )
    assert lesioned > 100 * complete, (
        "a single missing on-line zero must be shown to dominate the complete-list "
        f"residue: complete={complete}, lesioned={lesioned}"
    )


@pytest.mark.slow
def test_the_hunt_does_not_call_the_completeness_gate() -> None:
    """Pins the defect itself, so removing it is a deliberate act.

    If a future hunt starts calling ``online_list_is_complete``, this test
    fails and the corresponding paragraph in ``hunts/README.md`` should be
    updated — the finding would then be on a different footing.
    """
    sources = "\n".join(
        p.read_text(encoding="utf-8", errors="ignore")
        for p in _HUNTS.rglob("*.py")
    )
    assert "online_list_is_complete" not in sources, (
        "a hunt now calls the completeness gate — revisit hunts/README.md's "
        "Hunt #2 disposition, which is written on the assumption that it does not"
    )
