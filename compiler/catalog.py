"""``compiler.catalog`` — the tiny, human-inspectable rewrites under study.

Every program here is eight lines of LLVM IR with the same signature,
``i8 @f(i8 %x, i8 %y)``, so that the whole input space is 65536 points and can
be enumerated. The fixtures live as ``.ll`` files next to this module because a
reader should be able to check each one by eye; nothing in this package reads a
benchmark corpus.

The three known-invalid rewrites are not strawmen. Each is a transformation a
competent person has written on purpose:

* ``sdiv2_to_ashr`` — dividing by two with a shift. Wrong for negative odd
  values, because ``sdiv`` truncates toward zero and ``ashr`` floors.
* ``udiv4_to_ashr`` — the same mistake with the signedness confused as well.
* ``slt_to_sign_of_difference`` — testing ``x < y`` by the sign bit of
  ``x - y``. Wrong exactly when the subtraction overflows, which is why real
  code writes the comparison out.

All three reduce or match the instruction count of their source, which is what
makes the negative reference claim in ``harness.departments.compiler_department``
worth stating: they are the reason "shorter" is not evidence.
"""

from __future__ import annotations

import random
import re
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

from compiler import semantics

FIXTURES = Path(__file__).resolve().parent / "fixtures"

__all__ = [
    "FIXTURES",
    "Transformation",
    "LesionSpec",
    "load_ir",
    "instruction_count",
    "claim_no_more_instructions",
    "agreement_fraction_of",
    "claim_exhaustive_agreement",
    "claim_model_refinement",
    "random_mutant",
    "TARGET",
    "RIVALS",
    "LESION_HOST",
    "LESIONS",
]


@lru_cache(maxsize=64)
def load_ir(name: str) -> str:
    """Read one fixture by filename stem."""
    path = FIXTURES / f"{name}.ll"
    if not path.is_file():
        raise FileNotFoundError(f"no IR fixture {name!r} in {FIXTURES}")
    return path.read_text(encoding="utf-8")


_BODY = re.compile(r"\{(.*)\}", re.S)


def instruction_count(ir_text: str) -> int:
    """Instructions in the body of ``@f``, ignoring labels, braces and comments."""
    match = _BODY.search(ir_text)
    if match is None:
        raise ValueError("no function body found")
    total = 0
    for raw in match.group(1).splitlines():
        line = raw.split(";")[0].strip()
        if not line or line.endswith(":"):
            continue
        total += 1
    return total


@dataclass(frozen=True)
class Transformation:
    """A proposed rewrite: one source program, one candidate replacement.

    This is the department's fundamental object and the thing every instrument
    consumes. It carries no verdict of its own — deciding whether it deserves
    belief is exactly what the battery is for.
    """

    name: str
    source: str
    target: str
    note: str = ""

    @classmethod
    def from_fixtures(cls, name: str, source: str, target: str, note: str = "") -> Transformation:
        return cls(name=name, source=load_ir(source), target=load_ir(target), note=note)

    def describe(self) -> str:
        return self.note or self.name

    def instructions_removed(self) -> int:
        return instruction_count(self.source) - instruction_count(self.target)

    def with_target(self, target: str) -> Transformation:
        return Transformation(name=self.name, source=self.source, target=target, note=self.note)


# ---------------------------------------------------------------------------
# Claims — predicates over a Transformation
# ---------------------------------------------------------------------------


def claim_no_more_instructions(transformation: Transformation) -> bool:
    """The candidate is no longer than the source.

    A real, cheap, entirely true property of the target — and of every rival,
    which is the point. It is the compiler domain's version of a symmetry
    everything in the room happens to have.
    """
    return transformation.instructions_removed() >= 0


def agreement_fraction_of(transformation: Transformation, values: list[int]) -> float:
    """Share of the pairs drawn from ``values`` on which the rewrite holds up."""
    return semantics.agreement_fraction(transformation.source, transformation.target, values)


def claim_exhaustive_agreement(transformation: Transformation) -> bool:
    """Source and candidate returned the same value on all 65536 i8 pairs.

    Read :data:`compiler.semantics.EVIDENCE_EXHAUSTIVE_I8` before quoting this
    anywhere: it is agreement over an enumerated finite domain, not equivalence
    and not refinement.
    """
    return semantics.agreement(transformation.source, transformation.target).agrees


def claim_model_refinement(transformation: Transformation) -> bool:
    """The candidate refines its source under the poison-aware model.

    Read :data:`compiler.semantics.EVIDENCE_MODEL_I8` before quoting this
    anywhere: refinement is decided by exhaustive enumeration against a
    hand-written model of the supported subset, not against LLVM's own
    semantics. It is the claim that can see the ``nsw`` lesion rung 1 cannot.
    """
    return semantics.refinement(transformation.source, transformation.target).refines


# ---------------------------------------------------------------------------
# The target and its rivals
# ---------------------------------------------------------------------------

TARGET = Transformation.from_fixtures(
    "mul2_to_shl",
    "mul2_add_src",
    "mul2_add_tgt",
    "strength-reduce a multiply by two to a left shift; both wrap, so the two "
    "agree at every i8 input",
)

RIVALS: tuple[Transformation, ...] = (
    Transformation.from_fixtures(
        "sdiv2_to_ashr",
        "sdiv2_add_src",
        "sdiv2_add_tgt",
        "divide by two with a shift: same shape and same instruction count as the "
        "target, but sdiv truncates toward zero and ashr floors",
    ),
    Transformation.from_fixtures(
        "udiv4_to_ashr",
        "udiv4_add_src",
        "udiv4_add_tgt",
        "unsigned divide by four with an arithmetic shift: sign-extends where the "
        "source zero-extends",
    ),
    Transformation.from_fixtures(
        "slt_to_sign_of_difference",
        "slt_src",
        "slt_sub_tgt",
        "signed comparison by the sign bit of the difference: correct until the "
        "subtraction overflows",
    ),
)


# ---------------------------------------------------------------------------
# Lesions — planted corruptions of a rewrite that is known to agree
# ---------------------------------------------------------------------------

#: The host every lesion is planted in: a rewrite of the signed comparison into
#: the mirrored predicate, which agrees everywhere. Lesions damage the *target*
#: side, so a detector is being asked to notice a candidate that no longer does
#: what the source does.
LESION_HOST = Transformation.from_fixtures(
    "mirrored_predicate_and_shift",
    "host_src",
    "host_tgt",
    "mirror the predicate ('x slt y' is 'y sgt x') and strength-reduce the "
    "multiply -- two genuine identities, and the clean program every planted "
    "violation below is a corruption of",
)


@dataclass(frozen=True)
class LesionSpec:
    """A planted violation, expressed as a textual edit of the candidate.

    ``magnitude`` is the share of the 65536-point domain on which the lesioned
    candidate stops being a valid stand-in for the source. That is a property of
    the *violation*, and it is deliberately not the same number as the share on
    which a concrete run notices. For every lesion here but one the two
    coincide; for ``nsw_flag_on_a_wrapping_shift`` the violation covers half the
    domain and the concrete disagreement is exactly zero, because poison is not
    a value a compiled binary can hand back. Keeping the units on the violation
    rather than on the detector is what lets this department report a blind spot
    as a number instead of a footnote — see ``visible_concretely``.

    Both quantities are pinned by ``tests/test_compiler_lesions.py`` rather than
    trusted from this declaration.

    ``apply`` raises when its pattern is absent. A lesion that silently plants
    nothing would report a detector as blind when in fact it was shown nothing,
    which is the most flattering possible failure and so is made impossible.
    """

    name: str
    magnitude: float
    find: str
    replace: str
    visible_concretely: bool
    note: str = ""

    def describe(self) -> str:
        seen = "" if self.visible_concretely else " (invisible to a concrete run: poison)"
        return f"{self.note}{seen}"

    def apply(self, transformation: Transformation) -> Transformation:
        if self.find not in transformation.target:
            raise ValueError(
                f"lesion {self.name!r} found no {self.find!r} to damage in "
                f"{transformation.name!r}; it would have planted nothing"
            )
        return transformation.with_target(
            transformation.target.replace(self.find, self.replace, 1)
        )


LESIONS: tuple[LesionSpec, ...] = (
    LesionSpec(
        name="signed_to_unsigned_predicate",
        magnitude=0.5,
        find="icmp sgt i8 %y, %x",
        replace="icmp ugt i8 %y, %x",
        visible_concretely=True,
        note="signedness corruption: the comparison becomes unsigned, so it is "
        "wrong on every pair whose operands differ in sign bit",
    ),
    LesionSpec(
        name="strict_to_nonstrict_predicate",
        magnitude=1.0 / 256.0,
        find="icmp sgt i8 %y, %x",
        replace="icmp sge i8 %y, %x",
        visible_concretely=True,
        note="boundary corruption: > becomes >=, so the candidate is wrong on "
        "exactly the diagonal x == y",
    ),
    LesionSpec(
        name="single_point_special_case",
        magnitude=1.0 / 65536.0,
        find="  ret i8 %r",
        replace=(
            "  %p = icmp eq i8 %x, -128\n"
            "  %q = icmp eq i8 %y, -128\n"
            "  %b = and i1 %p, %q\n"
            "  %w = select i1 %b, i8 42, i8 %r\n"
            "  ret i8 %w"
        ),
        visible_concretely=True,
        note="one wrong answer in the whole domain, at the INT_MIN corner -- the "
        "shape of a real transformation bug that survives every test suite that "
        "did not think of the edge",
    ),
    LesionSpec(
        name="nsw_flag_on_a_wrapping_shift",
        magnitude=0.5,
        find="%m = shl i8 %x, 1",
        replace="%m = shl nsw i8 %x, 1",
        visible_concretely=False,
        note="the source multiplies by two and wraps; the candidate promises it "
        "never overflows, so the candidate is poison for every |x| >= 64 -- half "
        "the domain -- while a compiled binary still hands back the wrapped value",
    ),
)


# ---------------------------------------------------------------------------
# Surrogates — candidates from a generator with no idea what it is doing
# ---------------------------------------------------------------------------

#: Opcode families a mutation may swap within. Staying inside a family keeps
#: the mutant *compilable*, which is what makes it a fair null: a surrogate that
#: mostly failed to build would flatter the detector by never reaching it.
_SWAPS: dict[str, tuple[str, ...]] = {
    "add": ("sub", "xor", "and", "or", "mul"),
    "sub": ("add", "xor", "and", "or"),
    "mul": ("add", "sub", "and", "or"),
    "shl": ("lshr", "ashr"),
    "lshr": ("shl", "ashr"),
    "ashr": ("shl", "lshr"),
    "sdiv": ("udiv", "srem", "urem"),
    "udiv": ("sdiv", "urem", "srem"),
    "slt": ("sgt", "ult", "ugt", "sle", "eq"),
    "sgt": ("slt", "ugt", "ult", "sge", "ne"),
}

_TOKEN = re.compile(r"\b(" + "|".join(_SWAPS) + r")\b")


def random_mutant(source_ir: str, seed: int) -> Transformation:
    """A candidate produced by mutating the source with no guidance at all.

    This is the null model: a transformation drawn from the same *kind* of
    generator a search would use, with the part that is supposed to know what
    it is doing removed. If the statistic under audit is reproduced by these,
    it is a property of the generator and not of the candidate.
    """
    rng = random.Random(seed)
    sites = list(_TOKEN.finditer(source_ir))
    if not sites:
        raise ValueError("nothing to mutate in this program")
    site = rng.choice(sites)
    token = site.group(1)
    swapped = rng.choice(_SWAPS[token])
    mutated = source_ir[: site.start()] + swapped + source_ir[site.end() :]
    return Transformation(
        name=f"mutant_{seed}",
        source=source_ir,
        target=mutated,
        note=f"unguided mutation: {token} -> {swapped}",
    )
