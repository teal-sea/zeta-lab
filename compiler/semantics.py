"""``compiler.semantics`` — what can actually be established about a rewrite here.

This module is the candidate department's *detector*, and the whole point of
keeping it in one file is that its limits are written down in one place.

The ladder, and where this repository currently stands on it
------------------------------------------------------------
1. **Exhaustive concrete agreement** (implemented). Compile both programs and
   run them on every point of a deliberately tiny finite domain — all 65536
   ``(i8, i8)`` pairs — at more than one optimisation level, and compare the
   output tables byte for byte. What this establishes is exactly its name:
   *the two programs produced equal results on every input in the stated
   domain, under this compiler, at these flags*.
2. **Restricted symbolic semantics** (not implemented). An SMT model of a small
   IR subset would cover poison and ``undef``, which rung 1 cannot.
3. **LLVM-native refinement** (not implemented). Alive2 decides *refinement*,
   which is the property an LLVM transformation actually owes.

What rung 1 does **not** establish
----------------------------------
It is not a proof, not a certificate, not equivalence, and not refinement.

* **Poison and ``undef`` are invisible to it.** A transformation that adds an
  ``nsw`` flag makes the result poison on overflow, but a compiled binary still
  hands back the wrapped value, so the tables agree. The transformation is
  nonetheless invalid. ``compiler.catalog`` plants exactly this lesion so that
  the blindness is measured rather than assumed.
* **The two optimisation levels are not independent checks.** Both go through
  the same clang. Agreement across ``-O0`` and ``-O2`` catches a transformation
  whose validity the optimiser disagrees with; it cannot catch anything both
  levels get wrong for the same reason.
* **The domain is i8.** A defect that first appears at i32 is out of range by
  construction, and choosing a domain small enough to enumerate is itself a way
  to miss things.

Vocabulary
----------
`zeta/rigor.py` owns the word *certified* in this repository and nothing here
may borrow it. The strongest phrase this module is entitled to is the one
:data:`EVIDENCE_EXHAUSTIVE_I8` spells out, and every public function returns
that string alongside its verdict so a caller cannot report the verdict
without the caveat.
"""

from __future__ import annotations

import hashlib
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

__all__ = [
    "BACKEND",
    "BACKEND_REASON",
    "EVIDENCE_EXHAUSTIVE_I8",
    "OPT_LEVELS",
    "DOMAIN_SIZE",
    "SemanticsUnavailable",
    "IRRejected",
    "AgreementReport",
    "available_backends",
    "backend_status",
    "output_table",
    "agreement",
    "agreement_fraction",
    "index_of",
    "i8",
]

#: Every optimisation level both programs are compiled at. Disagreement
#: *between* levels for the same program is a signal in its own right: it means
#: the optimiser and the unoptimised lowering do not agree about the program,
#: which for a well-defined program should not happen.
OPT_LEVELS: tuple[str, ...] = ("-O0", "-O2")

#: 256 * 256 — every ``(i8, i8)`` pair.
DOMAIN_SIZE: int = 65536

#: The exact claim rung 1 supports. Quote it verbatim; do not paraphrase it
#: upward.
EVIDENCE_EXHAUSTIVE_I8: str = (
    "exhaustive agreement over all 65536 (i8, i8) inputs, compiled by this "
    "clang at -O0 and -O2; not equivalence, not refinement, and blind to "
    "poison/undef because a compiled binary observes neither"
)


class SemanticsUnavailable(RuntimeError):
    """No semantic backend is installed, so nothing here can be measured.

    Raised rather than returning a neutral verdict: a missing detector must not
    be able to produce a result that reads like a passing one.
    """


class IRRejected(ValueError):
    """The compiler refused the IR. Never treated as agreement or as failure."""


# ---------------------------------------------------------------------------
# Backend discovery — the rigor.py pattern, minus the entitlement to "certified"
# ---------------------------------------------------------------------------

_DRIVER = r"""
#include <stdio.h>
signed char f(signed char, signed char);
int main(void) {
    for (int x = -128; x < 128; x++)
        for (int y = -128; y < 128; y++)
            putchar((int)(unsigned char)f((signed char)x, (signed char)y));
    return 0;
}
"""

_PROBE_IR = """
define i8 @f(i8 %x, i8 %y) {
entry:
  %r = add i8 %x, %y
  ret i8 %r
}
"""


def _clang() -> str | None:
    return shutil.which("clang")


@lru_cache(maxsize=1)
def _clang_consumes_ir() -> tuple[bool, str]:
    """Does the clang on PATH accept a ``.ll`` file as input?

    Apple clang does, which is what makes rung 1 available with no install at
    all. A clang that does not is reported as an absent backend rather than
    worked around.
    """
    exe = _clang()
    if exe is None:
        return False, "no clang on PATH"
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "probe.ll"
        path.write_text(_PROBE_IR, encoding="utf-8")
        proc = subprocess.run(
            [exe, "-x", "ir", "-c", str(path), "-o", str(Path(tmp) / "probe.o")],
            capture_output=True,
            text=True,
        )
    if proc.returncode != 0:
        return False, f"clang at {exe} rejected LLVM IR input: {proc.stderr.strip()[:200]}"
    return True, f"clang at {exe} accepts LLVM IR input"


@lru_cache(maxsize=1)
def _alive2() -> tuple[bool, str]:
    exe = shutil.which("alive-tv")
    if exe is None:
        return False, "alive-tv not on PATH (rung 3 unavailable: no refinement checking)"
    return True, f"alive-tv at {exe}"


def available_backends() -> list[str]:
    """Every semantic backend that is actually usable right now."""
    found: list[str] = []
    if _clang_consumes_ir()[0]:
        found.append("clang.exhaustive_i8")
    if _alive2()[0]:
        found.append("alive2.refinement")
    return sorted(found)


def backend_status() -> dict[str, str]:
    """One line per candidate backend, present or absent, for diagnostics.

    Absence is reported, never hidden: this dict is what a report prints so
    that "no defect found" can never be read without "and here is what was not
    looked for".
    """
    ok_clang, why_clang = _clang_consumes_ir()
    ok_alive, why_alive = _alive2()
    return {
        "clang.exhaustive_i8": ("available: " if ok_clang else "ABSENT: ") + why_clang,
        "alive2.refinement": ("available: " if ok_alive else "ABSENT: ") + why_alive,
    }


#: The backend chosen for the exhaustive path, or the empty string if none is.
BACKEND: str = "clang.exhaustive_i8" if _clang_consumes_ir()[0] else ""

#: Why :data:`BACKEND` is what it is — quote this verbatim when reporting.
BACKEND_REASON: str = _clang_consumes_ir()[1]


# ---------------------------------------------------------------------------
# Running a program over the whole domain
# ---------------------------------------------------------------------------


def i8(value: int) -> int:
    """Wrap ``value`` into the signed 8-bit range."""
    return ((int(value) + 128) % 256) - 128


def index_of(x: int, y: int) -> int:
    """Position of the pair ``(x, y)`` in an output table."""
    return (i8(x) + 128) * 256 + (i8(y) + 128)


@lru_cache(maxsize=256)
def _run(ir_text: str, opt: str) -> bytes:
    exe = _clang()
    if exe is None or not _clang_consumes_ir()[0]:
        raise SemanticsUnavailable(
            "no semantic backend: " + backend_status()["clang.exhaustive_i8"]
        )
    with tempfile.TemporaryDirectory(prefix="zeta-lab-compiler-") as tmp:
        root = Path(tmp)
        (root / "m.ll").write_text(ir_text, encoding="utf-8")
        (root / "drv.c").write_text(_DRIVER, encoding="utf-8")
        build = subprocess.run(
            [exe, opt, "-w", "-x", "ir", str(root / "m.ll"), "-x", "c", str(root / "drv.c"),
             "-o", str(root / "a.out")],
            capture_output=True,
            text=True,
        )
        if build.returncode != 0:
            raise IRRejected(build.stderr.strip()[:400])
        run = subprocess.run([str(root / "a.out")], capture_output=True, timeout=120)
        if run.returncode != 0:
            raise IRRejected(f"the compiled program exited {run.returncode}")
    table = run.stdout
    if len(table) != DOMAIN_SIZE:
        raise IRRejected(f"expected {DOMAIN_SIZE} output bytes, got {len(table)}")
    return table


def output_table(ir_text: str, opt: str = "-O0") -> bytes:
    """Every value ``@f`` returns, indexed by :func:`index_of`."""
    return _run(ir_text, opt)


@dataclass(frozen=True)
class AgreementReport:
    """What was measured, over what, and what it is not.

    ``agrees`` is deliberately not called ``equivalent``: it is true when the
    two programs returned the same byte at every point of the domain that was
    actually enumerated, and nothing more. ``evidence`` carries the caveat so
    that a caller cannot print the verdict without it.
    """

    agrees: bool
    disagreements: int
    domain_size: int
    first_witness: tuple[int, int, int, int] | None
    level_disagreement: tuple[str, ...]
    evidence: str

    @property
    def fraction(self) -> float:
        """Share of the enumerated domain on which the two programs agreed."""
        return 1.0 - self.disagreements / self.domain_size if self.domain_size else 0.0

    def summary(self) -> str:
        if self.level_disagreement:
            return (
                f"inconclusive: {', '.join(self.level_disagreement)} disagree with "
                "themselves across optimisation levels, which means undefined behaviour"
            )
        if self.agrees:
            return f"agrees on all {self.domain_size} inputs ({self.evidence})"
        x, y, a, b = self.first_witness  # type: ignore[misc]
        return (
            f"disagrees on {self.disagreements}/{self.domain_size} inputs; "
            f"first witness f({x}, {y}) = {a} vs {b}"
        )


def agreement(source_ir: str, target_ir: str, *, opt_levels: tuple[str, ...] = OPT_LEVELS) -> AgreementReport:
    """Compare two programs on every point of the i8 x i8 domain.

    Each program is also compared against *itself* across optimisation levels.
    A program that disagrees with itself is exercising undefined behaviour, and
    the report says so rather than declaring a winner: comparing two programs
    when one of them has no single meaning is not a measurement.
    """
    unstable: list[str] = []
    tables: dict[str, dict[str, bytes]] = {}
    for label, text in (("source", source_ir), ("target", target_ir)):
        tables[label] = {opt: output_table(text, opt) for opt in opt_levels}
        if len({bytes(t) for t in tables[label].values()}) > 1:
            unstable.append(label)

    if unstable:
        return AgreementReport(
            agrees=False,
            disagreements=DOMAIN_SIZE,
            domain_size=DOMAIN_SIZE,
            first_witness=None,
            level_disagreement=tuple(unstable),
            evidence=EVIDENCE_EXHAUSTIVE_I8,
        )

    src = tables["source"][opt_levels[0]]
    tgt = tables["target"][opt_levels[0]]
    bad = [i for i in range(DOMAIN_SIZE) if src[i] != tgt[i]]
    witness = None
    if bad:
        i = bad[0]
        witness = (i // 256 - 128, i % 256 - 128, i8(src[i]), i8(tgt[i]))
    return AgreementReport(
        agrees=not bad,
        disagreements=len(bad),
        domain_size=DOMAIN_SIZE,
        first_witness=witness,
        level_disagreement=(),
        evidence=EVIDENCE_EXHAUSTIVE_I8,
    )


def agreement_fraction(source_ir: str, target_ir: str, values: list[int]) -> float:
    """Share of the pairs drawn from ``values`` on which the two programs agree.

    This is the measurement the decoys ablate. It takes the *input set* as an
    argument on purpose: the substantive input to a test-based verdict is which
    inputs were tested, and a measurement that does not move when that set is
    replaced by a degenerate one of the same size was never reading it.
    """
    src = output_table(source_ir, OPT_LEVELS[0])
    tgt = output_table(target_ir, OPT_LEVELS[0])
    pairs = [(x, y) for x in values for y in values]
    if not pairs:
        return 1.0
    hits = sum(1 for x, y in pairs if src[index_of(x, y)] == tgt[index_of(x, y)])
    return hits / len(pairs)
