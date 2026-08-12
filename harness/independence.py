"""``harness.independence`` — verification independence as declared structure.

"Checked by two implementations" is the repository's favourite sentence, and
the 2026-08-11 director run (``docs/25-the-director-run.md``) measured its
limit: a wrong sign came back from *both* numeric backends, because the fault
sat in a parsing layer the two paths shared, upstream of everything either
one duplicated. The two-backend cross-check was not broken; it was *bounded*,
and nobody had written down the bound. ``compiler/FINDINGS.md`` §6 is the
same finding in another department: two optimisation levels through one
toolchain are one check.

This module makes the bound declarable. A :class:`VerificationPath` is an
ordered declaration of the layers a verdict passes through, from input to
answer. :func:`compare` takes two of them and reports, without judgment:

* the **independence radius** — how deep the two paths run through the *same*
  leading layers before they first diverge (0 means they diverge at the
  input; the full length means they are one path);
* the **shared** layers — single implementations that both paths run, whose
  faults agreement can never see, wherever they sit;
* the **reconvergent** layers — shared layers that appear *after* the paths
  have diverged, the shape from the director run, where independent middles
  funnel back through one final summation;
* the **distinct** layers of each path — the only segments about which an
  agreement between the two paths is evidence at all.

Like :mod:`harness.provenance`, this is declaration, not attestation: nothing
here can verify that a declared layer list is complete or honest. What it can
do is refuse the two failure modes prose cannot: a path that declares nothing
(rejected, not defaulted), and a report collapsed to a single flattering
boolean (there is no aggregate, and ``bool(report)`` raises). The unit of
output is the same as everywhere else in this package: a tuple of named
reasons, each one a sentence a reader can dispute.

Domain-agnostic in the strict sense: imports nothing from any laboratory
package, names no quantity any laboratory computes, and sits under the same
three seam checks as :mod:`harness.protocol`. Subject declarations — which
layers a real instrument actually shares — live in ``harness/departments/``.
"""

from __future__ import annotations

from dataclasses import dataclass

__all__ = [
    "IndependenceError",
    "IndependenceReport",
    "VerificationPath",
    "agreement_bounds",
    "compare",
]


class IndependenceError(ValueError):
    """A path or comparison that cannot be measured as declared."""


@dataclass(frozen=True)
class VerificationPath:
    """One route from input to verdict, as an ordered tuple of named layers.

    ``layers`` runs upstream to downstream: ``layers[0]`` touches the input,
    ``layers[-1]`` produces the answer. A layer name identifies *one
    implementation*: two paths that list the same name are declaring that
    they run the same code or the same policy at that stage, not merely the
    same kind of stage. Name layers accordingly — ``"ball backend:
    python-flint"`` and ``"ball backend: mpmath.iv"`` are different layers;
    ``"input parsing (_exact)"`` listed by both paths is one layer used
    twice, which is precisely the thing this module exists to surface.

    An empty declaration is refused rather than defaulted: a path that names
    no layers is not "independent", it is unmeasured, and silence must stay
    visible (the same rule :mod:`harness.provenance` applies to its
    tri-states).
    """

    name: str
    layers: tuple[str, ...]

    def __post_init__(self) -> None:
        if not self.name or not self.name.strip():
            raise IndependenceError("a verification path needs a name")
        if not self.layers:
            raise IndependenceError(
                f"path {self.name!r} declares no layers: an undeclared path "
                "is unmeasured, not independent"
            )
        cleaned = []
        for layer in self.layers:
            if not isinstance(layer, str) or not layer.strip():
                raise IndependenceError(
                    f"path {self.name!r} has a blank layer: every stage "
                    "between input and verdict must carry a name"
                )
            cleaned.append(layer.strip())
        if len(set(cleaned)) != len(cleaned):
            raise IndependenceError(
                f"path {self.name!r} lists a layer twice: a layer name "
                "identifies one implementation, and one implementation "
                "appears once per path"
            )
        object.__setattr__(self, "layers", tuple(cleaned))


@dataclass(frozen=True)
class IndependenceReport:
    """What two declared paths share, where, and what that bounds.

    There is deliberately no ``independent`` boolean and no score. The
    report's content is structural: ``radius`` (the depth of the shared
    leading segment), ``shared`` (every layer both paths run, in path-a
    order), ``reconvergent`` (the subset of ``shared`` sitting past the
    divergence point in either path), and ``distinct_a`` / ``distinct_b``
    (the segments genuinely implemented twice — the only thing agreement
    between the paths is evidence about). Interpretation belongs to
    :func:`agreement_bounds`, which renders the structure as disputable
    sentences, and to the caller, who knows which layers matter.
    """

    path_a: str
    path_b: str
    layers_a: tuple[str, ...]
    layers_b: tuple[str, ...]
    radius: int
    shared: tuple[str, ...]
    reconvergent: tuple[str, ...]
    distinct_a: tuple[str, ...]
    distinct_b: tuple[str, ...]

    def __bool__(self) -> bool:
        raise TypeError(
            "an IndependenceReport has no single truth value: read radius, "
            "shared, reconvergent and the distinct segments, or render it "
            "with agreement_bounds()"
        )

    def describe(self) -> str:
        parts = [
            f"{self.path_a} vs {self.path_b}: "
            f"radius {self.radius} of {min(len(self.layers_a), len(self.layers_b))}"
        ]
        if self.shared:
            parts.append(f"shared: {', '.join(self.shared)}")
        if self.reconvergent:
            parts.append(f"reconvergent: {', '.join(self.reconvergent)}")
        parts.append(
            "agreement is evidence about: "
            + (", ".join(self.distinct_a + self.distinct_b) or "nothing")
        )
        return "; ".join(parts)


def compare(a: VerificationPath, b: VerificationPath) -> IndependenceReport:
    """Measure what two declared paths actually duplicate.

    The radius is the length of the *aligned* identical leading segment:
    the number of initial positions at which both paths name the same
    layer. Divergence at the input gives radius 0; two identical
    declarations give radius ``len(layers)`` and a report whose distinct
    segments are empty — one path, written down twice.
    """

    radius = 0
    for layer_a, layer_b in zip(a.layers, b.layers):
        if layer_a != layer_b:
            break
        radius += 1

    in_b = set(b.layers)
    shared = tuple(layer for layer in a.layers if layer in in_b)
    position_a = {layer: i for i, layer in enumerate(a.layers)}
    position_b = {layer: i for i, layer in enumerate(b.layers)}
    reconvergent = tuple(
        layer
        for layer in shared
        if position_a[layer] >= radius or position_b[layer] >= radius
    )
    distinct_a = tuple(layer for layer in a.layers if layer not in in_b)
    in_a = set(a.layers)
    distinct_b = tuple(layer for layer in b.layers if layer not in in_a)

    return IndependenceReport(
        path_a=a.name,
        path_b=b.name,
        layers_a=a.layers,
        layers_b=b.layers,
        radius=radius,
        shared=shared,
        reconvergent=reconvergent,
        distinct_a=distinct_a,
        distinct_b=distinct_b,
    )


def agreement_bounds(report: IndependenceReport) -> tuple[str, ...]:
    """Every reason an agreement between the two paths is bounded evidence.

    One sentence per shared layer, plus the structural degenerate cases.
    An empty tuple means the declaration contains no shared layer — which
    bounds nothing, and still verifies nothing about the declaration's own
    completeness; that caveat is the caller's to carry, the same way a
    :class:`~harness.provenance.Provenance` declaration is not attestation.
    """

    reasons: list[str] = []
    if report.radius == len(report.layers_a) == len(report.layers_b):
        reasons.append(
            f"{report.path_a} and {report.path_b} declare identical layers: "
            "they are one path written down twice, and their agreement is "
            "one measurement, not two"
        )
        return tuple(reasons)
    for layer in report.shared:
        where = (
            "downstream of the divergence"
            if layer in report.reconvergent
            else "upstream of the divergence"
        )
        reasons.append(
            f"layer {layer!r} is one implementation run by both paths "
            f"({where}): agreement cannot see a fault in it"
        )
    if not report.distinct_a and not report.distinct_b:
        reasons.append(
            "no layer is implemented twice: the comparison duplicates "
            "nothing and their agreement is evidence about nothing"
        )
    return tuple(reasons)
