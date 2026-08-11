"""Audit the public bandwidth-one ceiling artifact accompanying Claude's paper.

The paper's Remark 1.1 states a 0.68185 ceiling for certificates that use the
bandwidth-one pair-correlation data configuration by configuration.  The public
Lean companion later exposed the finite law behind that statement in
``Zeta23/PairCeiling/LawN256.lean``.  It does not include the exact-rational
law artifact from which the displayed enclosures were generated.

This module checks, with exact rational arithmetic, everything recoverable
from the public Lean source:

* all 255 interior form-factor rows have the stated near-CUE error;
* the edge discrepancy has the stated sign and magnitude;
* the stability coefficient is the displayed 2.5431316e-6;
* the claimed simple-point fraction occurs only in a comment, not in an
  executable declaration; and
* the separately named exact-rational law artifact is present or absent and,
  when supplied, has the advertised SHA-256 digest.

Run from the repository root with ``.venv/bin/python``.  A clone of the public
companion repository is an external input, just as the paper is for the other
instruments in this hunt.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


N = 256
EXPECTED_SCALE = 2**140
ROW_TOLERANCE = Fraction(3, 10**40)
EDGE_BOUND = Fraction(82_395_317, 10**8)
LAW_SIMPLE_FRACTION = Fraction(
    10_909_258_999_421_303_588_095_230_195_816_054_408_197,
    16_000_000_000_000_000_000_000_000_000_000_000_000_000,
)
LAW_ARTIFACT_NAME = "cert_N256_blk_b128m.json"
LAW_ARTIFACT_SHA256 = (
    "cc3de9917db4d14d844630a4e97dda8387fd6e257e52b6967f430b8914584eb8"
)


@dataclass(frozen=True)
class LawAudit:
    """Exact consequences of the integer enclosures in ``LawN256.lean``."""

    source_sha256: str
    scale: int
    row_count: int
    worst_row: int
    worst_row_error: Fraction
    edge_lo: Fraction
    edge_hi: Fraction
    stability_coefficient: Fraction
    simple_fraction_in_executable_source: bool
    artifact_path: Path | None
    artifact_sha256: str | None

    @property
    def artifact_matches_advertised_digest(self) -> bool | None:
        if self.artifact_sha256 is None:
            return None
        return self.artifact_sha256 == LAW_ARTIFACT_SHA256


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _without_lean_comments(text: str) -> str:
    """Remove nested Lean block comments and line comments.

    A small scanner is used instead of a regular expression because Lean block
    comments may nest.  Strings do not matter for the source inspected here.
    """

    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("unterminated Lean block comment")
    return "".join(out)


def _parse_enclosures(text: str) -> tuple[int, list[tuple[int, int]]]:
    scale_match = re.search(r"\bK\s*:=\s*(\d+)", text)
    encl_match = re.search(r"\bencl\s*:=\s*\[(.*?)\]\s*tn\s*:=", text, re.DOTALL)
    if scale_match is None or encl_match is None:
        raise ValueError("could not locate K and encl in the Lean source")
    scale = int(scale_match.group(1))
    enclosures = [
        (int(lo), int(hi))
        for lo, hi in re.findall(r"\((\d+),\s*(\d+)\)", encl_match.group(1))
    ]
    return scale, enclosures


def audit_law_source(
    source: str | Path,
    artifact: str | Path | None = None,
) -> LawAudit:
    """Audit a public ``LawN256.lean`` source and optional underlying law file."""

    source_path = Path(source)
    text = source_path.read_text(encoding="utf-8")
    scale, enclosures = _parse_enclosures(text)
    if scale != EXPECTED_SCALE:
        raise ValueError(f"unexpected enclosure scale: {scale}")
    if len(enclosures) != N:
        raise ValueError(f"expected {N} enclosure rows, found {len(enclosures)}")
    for row, (lo, hi) in enumerate(enclosures, 1):
        if lo > hi:
            raise ValueError(f"row {row} has an inverted enclosure")

    errors: list[Fraction] = []
    for row, (lo, hi) in enumerate(enclosures[:-1], 1):
        lower_error = Fraction(N * lo, scale) - row
        upper_error = Fraction(N * hi, scale) - row
        errors.append(max(abs(lower_error), abs(upper_error)))
    worst_error = max(errors)
    worst_row = errors.index(worst_error) + 1

    sum_lo = sum(lo for lo, _ in enclosures)
    sum_hi = sum(hi for _, hi in enclosures)
    edge_lo = Fraction(sum_lo, N * scale) - Fraction(1, 2)
    edge_hi = Fraction(sum_hi, N * scale) - Fraction(1, 2)
    stability = Fraction(1, 6 * N**2) + ROW_TOLERANCE / (2 * N)

    if worst_error >= ROW_TOLERANCE:
        raise ValueError(
            f"interior row {worst_row} exceeds the advertised tolerance"
        )
    if edge_lo < 0:
        raise ValueError("the enclosures do not imply a nonnegative edge discrepancy")
    if max(abs(edge_lo), abs(edge_hi)) > EDGE_BOUND:
        raise ValueError("the edge discrepancy exceeds the advertised bound")

    executable = _without_lean_comments(text)
    fraction_is_executable = str(LAW_SIMPLE_FRACTION.numerator) in executable

    artifact_path = Path(artifact) if artifact is not None else None
    artifact_digest = None
    if artifact_path is not None:
        if not artifact_path.is_file():
            raise FileNotFoundError(artifact_path)
        artifact_digest = _sha256(artifact_path)

    return LawAudit(
        source_sha256=_sha256(source_path),
        scale=scale,
        row_count=len(enclosures),
        worst_row=worst_row,
        worst_row_error=worst_error,
        edge_lo=edge_lo,
        edge_hi=edge_hi,
        stability_coefficient=stability,
        simple_fraction_in_executable_source=fraction_is_executable,
        artifact_path=artifact_path,
        artifact_sha256=artifact_digest,
    )


def _decimal(value: Fraction, digits: int = 30) -> str:
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(value.numerator) / Decimal(value.denominator))


def render(audit: LawAudit) -> str:
    """Render a compact, diffable audit report."""

    artifact_state: str
    if audit.artifact_path is None:
        artifact_state = "not supplied"
    else:
        artifact_state = (
            f"{audit.artifact_path} sha256={audit.artifact_sha256} "
            f"matches={audit.artifact_matches_advertised_digest}"
        )

    return "\n".join(
        [
            f"source_sha256: {audit.source_sha256}",
            f"scale: {audit.scale} (=2^140: {audit.scale == 2**140})",
            f"rows: {audit.row_count}",
            (
                f"worst interior row: {audit.worst_row}, "
                f"error={_decimal(audit.worst_row_error, 12)} "
                f"(<3e-40: {audit.worst_row_error < ROW_TOLERANCE})"
            ),
            f"edge D(1): [{_decimal(audit.edge_lo)}, {_decimal(audit.edge_hi)}]",
            f"edge nonnegative: {audit.edge_lo >= 0}",
            f"edge within 0.82395317: {max(abs(audit.edge_lo), abs(audit.edge_hi)) <= EDGE_BOUND}",
            f"stability coefficient: {_decimal(audit.stability_coefficient)}",
            f"simple fraction from source comment: {_decimal(LAW_SIMPLE_FRACTION)}",
            (
                "simple-fraction numerator in executable source: "
                f"{audit.simple_fraction_in_executable_source}"
            ),
            f"underlying law artifact ({LAW_ARTIFACT_NAME}): {artifact_state}",
            f"advertised artifact sha256: {LAW_ARTIFACT_SHA256}",
        ]
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("law_source", type=Path, help="path to LawN256.lean")
    parser.add_argument(
        "--artifact",
        type=Path,
        help=f"optional path to the underlying {LAW_ARTIFACT_NAME}",
    )
    args = parser.parse_args()
    report = audit_law_source(args.law_source, args.artifact)
    print(render(report))


if __name__ == "__main__":
    main()
