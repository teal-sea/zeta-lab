"""``compiler.semantics``, what can actually be established about a rewrite here.

This module is the candidate department's *detector*, and the whole point of
keeping it in one file is that its limits are written down in one place.

The ladder, and where this repository currently stands on it
------------------------------------------------------------
1. **Exhaustive concrete agreement** (implemented). Compile both programs and
   run them on every point of a deliberately tiny finite domain, all 65536
   ``(i8, i8)`` pairs, at more than one optimisation level, and compare the
   output tables byte for byte. What this establishes is exactly its name:
   *the two programs produced equal results on every input in the stated
   domain, under this compiler, at these flags*.
2. **Exhaustive refinement under a poison-aware model** (implemented). A pure
   Python interpreter of the supported straight-line IR subset that represents
   poison as a first-class state and immediate UB as a per-input outcome, run
   over the same 65536 points. Over a domain this small, exhaustive
   enumeration decides what an SMT query would decide, with no solver
   installed. What it establishes is refinement **with respect to the model**:
   every claim it makes is about this file's reading of the LangRef, not about
   clang, and the two backends cross-check each other on every value the model
   says is defined (:func:`model_matches_clang`, the same two-backend habit
   as ``zeta/rigor.py``, without borrowing that module's vocabulary).
3. **LLVM-native refinement** (not implemented). Alive2 decides refinement
   under LLVM's own semantics, which is the property an LLVM transformation
   actually owes. Rung 2 is a model of that property, not the property.

What rung 1 does **not** establish
----------------------------------
It is not a proof, not a certificate, not equivalence, and not refinement.

* **Poison and ``undef`` are invisible to it.** A transformation that adds an
  ``nsw`` flag makes the result poison on overflow, but a compiled binary still
  hands back the wrapped value, so the tables agree. The transformation is
  nonetheless invalid. ``compiler.catalog`` plants exactly this lesion so that
  the blindness is measured rather than assumed, and rung 2 exists because of
  it: :func:`refinement` sees that lesion as 32768 poison violations.
* **The two optimisation levels are not independent checks.** Both go through
  the same clang. Agreement across ``-O0`` and ``-O2`` catches a transformation
  whose validity the optimiser disagrees with; it cannot catch anything both
  levels get wrong for the same reason.
* **The domain is i8.** A defect that first appears at i32 is out of range by
  construction, and choosing a domain small enough to enumerate is itself a way
  to miss things.

What rung 2 does **not** establish
----------------------------------
* **The model is hand-written, not LLVM.** Where the model and LLVM's real
  semantics disagree, the model is wrong and its verdicts are about nothing.
  The exposure is bounded three ways: the subset is small enough to check
  against the LangRef by eye, the model is cross-checked against compiled
  output at every defined point of every fixture, and any instruction the
  parser does not recognise raises :class:`ModelUnsupported` rather than
  guessing.
* **``undef`` is out of scope.** The subset has no ``undef`` values, no
  ``freeze``, and single-block control flow only. The refinement rules below
  cover poison and immediate UB, which is what the planted lesions need.

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
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Final

__all__ = [
    "BACKEND",
    "BACKEND_REASON",
    "EVIDENCE_EXHAUSTIVE_I8",
    "EVIDENCE_MODEL_I8",
    "OPT_LEVELS",
    "DOMAIN_SIZE",
    "POISON",
    "UB",
    "SemanticsUnavailable",
    "IRRejected",
    "ModelUnsupported",
    "AgreementReport",
    "RefinementReport",
    "available_backends",
    "backend_status",
    "output_table",
    "agreement",
    "agreement_fraction",
    "model_output_table",
    "refinement",
    "model_matches_clang",
    "index_of",
    "i8",
]

#: Every optimisation level both programs are compiled at. Disagreement
#: *between* levels for the same program is a signal in its own right: it means
#: the optimiser and the unoptimised lowering do not agree about the program,
#: which for a well-defined program should not happen.
OPT_LEVELS: tuple[str, ...] = ("-O0", "-O2")

#: 256 * 256, every ``(i8, i8)`` pair.
DOMAIN_SIZE: int = 65536

#: The exact claim rung 1 supports. Quote it verbatim; do not paraphrase it
#: upward.
EVIDENCE_EXHAUSTIVE_I8: str = (
    "exhaustive agreement over all 65536 (i8, i8) inputs, compiled by this "
    "clang at -O0 and -O2; not equivalence, not refinement, and blind to "
    "poison/undef because a compiled binary observes neither"
)

#: The exact claim rung 2 supports. The load-bearing phrase is "with respect
#: to the model": every verdict is about this file's poison-aware reading of
#: the supported subset, cross-checked against clang where values are defined,
#: and about nothing beyond that.
EVIDENCE_MODEL_I8: str = (
    "exhaustive refinement check over all 65536 (i8, i8) inputs, with respect "
    "to a hand-written poison-aware model of the supported IR subset; a claim "
    "about the model, not about clang or LLVM's full semantics, and undef is "
    "out of scope"
)


class SemanticsUnavailable(RuntimeError):
    """No semantic backend is installed, so nothing here can be measured.

    Raised rather than returning a neutral verdict: a missing detector must not
    be able to produce a result that reads like a passing one.
    """


class IRRejected(ValueError):
    """A backend refused the IR. Never treated as agreement or as failure."""


class ModelUnsupported(IRRejected):
    """The model does not implement this instruction, so it must not answer.

    A subclass of :class:`IRRejected` on purpose: a caller treating "the
    backend refused" uniformly stays correct, and a caller that wants to know
    *which* backend refused can still tell.
    """


# ---------------------------------------------------------------------------
# Backend discovery, the rigor.py pattern, minus the entitlement to "certified"
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
    """Every semantic backend that is actually usable right now.

    ``pymodel.refinement_i8`` is always present because it is this file: pure
    Python, no PATH, no install. That is a feature and a caveat in one, the
    model cannot be switched off by the environment, and it is only as right
    as its author's reading of the LangRef, which is why
    :func:`model_matches_clang` exists.
    """
    found: list[str] = ["pymodel.refinement_i8"]
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
        "pymodel.refinement_i8": (
            "available: pure-Python poison-aware model of the supported subset "
            "(this file; needs nothing installed)"
        ),
        "alive2.refinement": ("available: " if ok_alive else "ABSENT: ") + why_alive,
    }


#: The backend chosen for the exhaustive path, or the empty string if none is.
BACKEND: str = "clang.exhaustive_i8" if _clang_consumes_ir()[0] else ""

#: Why :data:`BACKEND` is what it is, quote this verbatim when reporting.
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


# ---------------------------------------------------------------------------
# Rung 2: the poison-aware model
# ---------------------------------------------------------------------------


class _Poison:
    """The poison state, as a singleton that can never be confused with an i8."""

    __slots__ = ()

    def __repr__(self) -> str:  # pragma: no cover - repr only
        return "POISON"


class _UBState:
    """The immediate-UB state for one input, same discipline as :class:`_Poison`."""

    __slots__ = ()

    def __repr__(self) -> str:  # pragma: no cover - repr only
        return "UB"


#: The two non-value outcomes a model run can produce for one input. Table
#: entries are ``int`` (0..255, the unsigned reading of the i8), ``POISON``,
#: or ``UB``, nothing else, so a caller can pattern-match exhaustively.
POISON = _Poison()
UB = _UBState()


class _ImmediateUB(Exception):
    """Internal: raised mid-evaluation, caught per input, recorded as ``UB``."""


_BINOPS: Final = frozenset(
    {"add", "sub", "mul", "shl", "lshr", "ashr", "sdiv", "udiv", "srem", "urem", "and", "or", "xor"}
)
_PREDICATES: Final = frozenset({"eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge"})
_FLAGS: Final = frozenset({"nsw", "nuw", "exact"})


def _signed(value: int, width: int) -> int:
    half = 1 << (width - 1)
    return value - (1 << width) if value >= half else value


def _unsigned(value: int, width: int) -> int:
    return value & ((1 << width) - 1)


@dataclass(frozen=True)
class _Instr:
    dest: str | None
    op: str
    width: int
    args: tuple[str, ...]
    pred: str = ""
    flags: frozenset = frozenset()


_LINE_BINOP = re.compile(
    r"^%(?P<dest>[\w.]+)\s*=\s*(?P<op>\w+)(?P<flags>(?:\s+(?:nsw|nuw|exact))*)\s+"
    r"i(?P<width>\d+)\s+(?P<a>[%\w.-]+),\s*(?P<b>[%\w.-]+)$"
)
_LINE_ICMP = re.compile(
    r"^%(?P<dest>[\w.]+)\s*=\s*icmp\s+(?P<pred>\w+)\s+i(?P<width>\d+)\s+"
    r"(?P<a>[%\w.-]+),\s*(?P<b>[%\w.-]+)$"
)
_LINE_ZEXT = re.compile(
    r"^%(?P<dest>[\w.]+)\s*=\s*zext\s+i(?P<from>\d+)\s+(?P<a>[%\w.-]+)\s+to\s+i(?P<to>\d+)$"
)
_LINE_SELECT = re.compile(
    r"^%(?P<dest>[\w.]+)\s*=\s*select\s+i1\s+(?P<c>[%\w.-]+),\s*"
    r"i(?P<width>\d+)\s+(?P<a>[%\w.-]+),\s*i\d+\s+(?P<b>[%\w.-]+)$"
)
_LINE_RET = re.compile(r"^ret\s+i(?P<width>\d+)\s+(?P<a>[%\w.-]+)$")


@lru_cache(maxsize=256)
def _parse(ir_text: str) -> tuple[_Instr, ...]:
    """The supported subset: one block, the binops above, icmp, zext, select, ret.

    Anything else raises :class:`ModelUnsupported`, the model must refuse
    rather than guess, for the same reason an absent backend raises rather
    than answering.
    """
    instrs: list[_Instr] = []
    in_body = False
    for raw in ir_text.splitlines():
        line = raw.split(";")[0].strip()
        if not line:
            continue
        if line.startswith("define"):
            in_body = True
            continue
        if not in_body or line in {"{", "}"} or line.endswith(":"):
            continue
        if match := _LINE_BINOP.match(line):
            op = match["op"]
            if op not in _BINOPS:
                raise ModelUnsupported(f"the model does not implement {op!r}: {line}")
            flags = frozenset(match["flags"].split())
            instrs.append(
                _Instr(
                    dest=f"%{match['dest']}",
                    op=op,
                    width=int(match["width"]),
                    args=(match["a"], match["b"]),
                    flags=flags,
                )
            )
        elif match := _LINE_ICMP.match(line):
            if match["pred"] not in _PREDICATES:
                raise ModelUnsupported(f"unknown icmp predicate: {line}")
            instrs.append(
                _Instr(
                    dest=f"%{match['dest']}",
                    op="icmp",
                    width=int(match["width"]),
                    args=(match["a"], match["b"]),
                    pred=match["pred"],
                )
            )
        elif match := _LINE_ZEXT.match(line):
            instrs.append(
                _Instr(
                    dest=f"%{match['dest']}",
                    op="zext",
                    width=int(match["to"]),
                    args=(match["a"],),
                )
            )
        elif match := _LINE_SELECT.match(line):
            instrs.append(
                _Instr(
                    dest=f"%{match['dest']}",
                    op="select",
                    width=int(match["width"]),
                    args=(match["c"], match["a"], match["b"]),
                )
            )
        elif match := _LINE_RET.match(line):
            instrs.append(_Instr(dest=None, op="ret", width=int(match["width"]), args=(match["a"],)))
        else:
            raise ModelUnsupported(f"the model does not recognise this line: {line!r}")
    if not instrs or instrs[-1].op != "ret":
        raise ModelUnsupported("the model needs a single block ending in ret")
    return tuple(instrs)


def _operand(token: str, env: dict):
    if token.startswith("%"):
        try:
            return env[token]
        except KeyError:
            raise ModelUnsupported(f"use of undefined register {token}") from None
    return int(token)


def _eval_binop(instr: _Instr, a, b):
    """One binop under the model's reading of the LangRef, poison in, poison out."""
    if a is POISON or b is POISON:
        # Division by a poison divisor is immediate UB; everything else folds
        # poison operands to a poison result.
        if instr.op in {"sdiv", "udiv", "srem", "urem"} and b is POISON:
            raise _ImmediateUB
        return POISON
    width = instr.width
    mask = (1 << width) - 1
    ua, ub_ = _unsigned(a, width), _unsigned(b, width)
    sa, sb = _signed(ua, width), _signed(ub_, width)
    op = instr.op

    if op in {"add", "sub", "mul"}:
        exact = {"add": sa + sb, "sub": sa - sb, "mul": sa * sb}[op]
        uexact = {"add": ua + ub_, "sub": ua - ub_, "mul": ua * ub_}[op]
        result = uexact & mask
        if "nsw" in instr.flags and not (-(1 << (width - 1)) <= exact <= (1 << (width - 1)) - 1):
            return POISON
        if "nuw" in instr.flags and not (0 <= uexact <= mask):
            return POISON
        return result
    if op in {"shl", "lshr", "ashr"}:
        if ub_ >= width:
            return POISON
        if op == "shl":
            result = (ua << ub_) & mask
            if "nsw" in instr.flags and _signed(result, width) != sa * (1 << ub_):
                return POISON
            if "nuw" in instr.flags and (ua << ub_) != result:
                return POISON
            return result
        if op == "lshr":
            result = ua >> ub_
        else:
            result = _unsigned(sa >> ub_, width)
        if "exact" in instr.flags and _unsigned(result << ub_, width) != (
            ua if op == "lshr" else ua
        ):
            return POISON
        return result
    if op in {"sdiv", "udiv", "srem", "urem"}:
        if ub_ == 0:
            raise _ImmediateUB
        if op == "udiv":
            quotient = ua // ub_
            if "exact" in instr.flags and ua != quotient * ub_:
                return POISON
            return quotient
        if op == "urem":
            return ua % ub_
        if sa == -(1 << (width - 1)) and sb == -1:
            raise _ImmediateUB
        quotient = abs(sa) // abs(sb)
        if (sa < 0) != (sb < 0):
            quotient = -quotient
        if op == "sdiv":
            if "exact" in instr.flags and sa != quotient * sb:
                return POISON
            return _unsigned(quotient, width)
        return _unsigned(sa - quotient * sb, width)
    if op == "and":
        return ua & ub_
    if op == "or":
        return ua | ub_
    if op == "xor":
        return ua ^ ub_
    raise ModelUnsupported(f"unreachable binop {op!r}")  # pragma: no cover


def _eval_program(instrs: tuple[_Instr, ...], x: int, y: int):
    env: dict = {"%x": _unsigned(x, 8), "%y": _unsigned(y, 8)}
    for instr in instrs:
        if instr.op == "ret":
            return _operand(instr.args[0], env)
        if instr.op == "icmp":
            a, b = (_operand(t, env) for t in instr.args)
            if a is POISON or b is POISON:
                env[instr.dest] = POISON
                continue
            width = instr.width
            ua, ub_ = _unsigned(a, width), _unsigned(b, width)
            sa, sb = _signed(ua, width), _signed(ub_, width)
            env[instr.dest] = int(
                {
                    "eq": ua == ub_,
                    "ne": ua != ub_,
                    "ult": ua < ub_,
                    "ule": ua <= ub_,
                    "ugt": ua > ub_,
                    "uge": ua >= ub_,
                    "slt": sa < sb,
                    "sle": sa <= sb,
                    "sgt": sa > sb,
                    "sge": sa >= sb,
                }[instr.pred]
            )
        elif instr.op == "zext":
            value = _operand(instr.args[0], env)
            env[instr.dest] = POISON if value is POISON else value
        elif instr.op == "select":
            condition = _operand(instr.args[0], env)
            if condition is POISON:
                env[instr.dest] = POISON
            else:
                env[instr.dest] = _operand(instr.args[1] if condition else instr.args[2], env)
        else:
            a, b = (_operand(t, env) for t in instr.args)
            env[instr.dest] = _eval_binop(instr, a, b)
    raise ModelUnsupported("fell off the end of the block without a ret")


@lru_cache(maxsize=64)
def model_output_table(ir_text: str) -> tuple:
    """What ``@f`` evaluates to at every input, under the model.

    One entry per :func:`index_of` position: an ``int`` in 0..255 (the
    unsigned reading of the returned i8), :data:`POISON`, or :data:`UB`.
    """
    instrs = _parse(ir_text)
    table = []
    for x in range(-128, 128):
        for y in range(-128, 128):
            try:
                table.append(_eval_program(instrs, x, y))
            except _ImmediateUB:
                table.append(UB)
    return tuple(table)


@dataclass(frozen=True)
class RefinementReport:
    """Whether the candidate refines the source, under the model, and where not.

    The three violation counters are disjoint and sum to ``violations``:

    * ``value_violations``: source defined, candidate defined, values differ.
    * ``poison_violations``: source defined, candidate poison. This is the
      class rung 1 cannot see at all.
    * ``ub_violations``: candidate is immediate UB where the source is not.

    ``refines`` uses the standard direction: where the source is UB anything
    is allowed; where the source is poison the candidate may be poison or any
    value but not UB; where the source is a value the candidate must be that
    value. ``evidence`` carries the model caveat and must travel with the
    verdict.
    """

    refines: bool
    violations: int
    value_violations: int
    poison_violations: int
    ub_violations: int
    domain_size: int
    first_witness: tuple[int, int, str] | None
    evidence: str

    @property
    def fraction(self) -> float:
        """Share of the domain on which the candidate is a valid stand-in."""
        return 1.0 - self.violations / self.domain_size if self.domain_size else 0.0

    def summary(self) -> str:
        if self.refines:
            return f"refines its source at all {self.domain_size} inputs ({self.evidence})"
        x, y, kind = self.first_witness  # type: ignore[misc]
        return (
            f"fails refinement on {self.violations}/{self.domain_size} inputs "
            f"({self.value_violations} value, {self.poison_violations} poison, "
            f"{self.ub_violations} UB); first witness f({x}, {y}): {kind}"
        )


def refinement(source_ir: str, target_ir: str) -> RefinementReport:
    """Exhaustive refinement of ``target_ir`` against ``source_ir`` under the model."""
    src = model_output_table(source_ir)
    tgt = model_output_table(target_ir)
    value_bad = poison_bad = ub_bad = 0
    witness = None

    for i in range(DOMAIN_SIZE):
        s, t = src[i], tgt[i]
        if s is UB:
            continue
        kind = ""
        if t is UB:
            ub_bad += 1
            kind = "candidate is immediate UB where the source is defined"
        elif s is POISON:
            continue
        elif t is POISON:
            poison_bad += 1
            kind = "candidate is poison where the source has a value"
        elif s != t:
            value_bad += 1
            kind = f"source returns {_signed(s, 8)}, candidate returns {_signed(t, 8)}"
        if kind and witness is None:
            witness = (i // 256 - 128, i % 256 - 128, kind)

    bad = value_bad + poison_bad + ub_bad
    return RefinementReport(
        refines=bad == 0,
        violations=bad,
        value_violations=value_bad,
        poison_violations=poison_bad,
        ub_violations=ub_bad,
        domain_size=DOMAIN_SIZE,
        first_witness=witness,
        evidence=EVIDENCE_MODEL_I8,
    )


def model_matches_clang(ir_text: str, *, opt_levels: tuple[str, ...] = OPT_LEVELS) -> dict:
    """The two-backend cross-check: model values against compiled output.

    At every input where the model produces a defined value, the compiled
    program must produce the same byte at every optimisation level, a
    defined value constrains the compiler completely. Where the model says
    poison or UB the compiled byte is unconstrained and is not compared.

    Returns a dict with ``comparable`` (how many inputs constrained the
    check), ``mismatches``, and ``agrees``. A mismatch means one of the two
    backends is wrong about this program, and nothing built on either may be
    quoted until it is known which.
    """
    model = model_output_table(ir_text)
    compiled = {opt: output_table(ir_text, opt) for opt in opt_levels}
    comparable = mismatches = 0
    first = None
    for i, value in enumerate(model):
        if value is POISON or value is UB:
            continue
        comparable += 1
        for opt, table in compiled.items():
            if table[i] != value:
                mismatches += 1
                if first is None:
                    first = (i // 256 - 128, i % 256 - 128, opt, value, table[i])
                break
    return {
        "comparable": comparable,
        "mismatches": mismatches,
        "agrees": mismatches == 0,
        "first_mismatch": first,
        "evidence": EVIDENCE_MODEL_I8,
    }
