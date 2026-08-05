"""ontology.knownness — the gate that catches the dominant outcome.

Most numerical "discoveries" are already known. This module is the screen that
says so, and it is deliberately built to be *hard to fool in the flattering
direction*: every route to the answer "recognised" has to survive a precision
increase or cite a source, while the answer "not recognised" is never allowed to
be rendered as "new".

Three capabilities, in order of how often they fire:

1. **Closed-form identification** (:func:`identify_constant`). An integer-relation
   search — :func:`mpmath.pslq` over subsets of a curated constant basis, with
   :func:`mpmath.identify` as an independent cross-check — asking whether a
   measured number is a recognisable expression. ``identify`` and ``pslq`` at low
   precision produce false positives at a rate set by the size of the search
   space, so a match is *provisional* until it is re-verified against the value
   recomputed at strictly higher precision. A provisional match that dissolves is
   reported as **not identified**, together with the expression that dissolved.
2. **A registry of known facts** (:class:`KnownFactRegistry`). A small, curated,
   citable table: statement, canonical form, source, matcher. This module
   populates it with domain-neutral mathematics only; anything specific to what
   the laboratory studies is registered by a domain module (see
   ``discovery/domains/``).
3. **A literature check** (:func:`check_literature`) — an *interface*, honestly
   stubbed. With no network there is no OEIS, no arXiv, no Zentralblatt, so the
   default backend returns :attr:`LiteratureStatus.UNKNOWN`: not "absent from the
   literature", but "the literature was not consulted".

The integrity rule
------------------
**"Not found offline" is not "novel".** ``UNKNOWN`` from the literature check maps
to the label :data:`NOT_RECOGNISED_OFFLINE`, never to a novelty claim, and there
is no code path in this module that emits one — :data:`FORBIDDEN_LABEL_WORDS`
names the words a label may not contain and :func:`funnel_label` enforces it, so
a funnel that consumes this module cannot launder a failed lookup into a find.
Establishing novelty requires a search this system cannot perform.

Domain neutrality
-----------------
This module knows *mathematics* (π, γ, PSLQ, the Wigner surmise) but not the
laboratory's subject. It imports ``mpmath``, ``ontology.schema`` and the
standard library — nothing else, and a test enforces it. It is one step less
strict than ``schema``/``funnel``/``metrics``/``registry``/``ledger``/
``historical_cases``, which know no mathematics at all; the subject-matter facts
live behind :data:`KNOWN_FACTS`, which a domain module fills in
(``discovery/domains/zeta_domain.py`` builds its own registry from
:data:`GENERAL_FACTS` plus its own table).

Where the line actually falls, stated rather than implied. Four entries of
:data:`GENERAL_FACTS` sit close enough to this particular laboratory's subject
to be worth naming: ``prime-number-theorem``, ``mertens-third-theorem``,
``hasse-weil-bound`` and ``gue-wigner-surmise``. They are here because each is a
standard result any catalogue of mathematics would carry, not because this
laboratory studies zeta — a chemistry lab would simply never match them. The
test of the seam is *dependency*, and it holds: nothing here imports the
laboratory, and no historical case is decided by this table (all four are
matched by the domain's own entries — ``test_the_seam_in_action`` and
``tests/test_discovery_historical_validation.py`` pin it). But a reader
comparing "knows no subject matter" against this list would be right to object
to the phrasing, so the phrasing is: **this module carries general results,
some of which a number-theoretic laboratory will find familiar.**

What this module cannot do
--------------------------
* It cannot establish that anything is new. See the integrity rule above.
* It cannot recognise a closed form outside its basis, outside ``max_terms``
  terms, or with coefficients above ``maxcoeff``. "Not identified" means "not
  identified by *this* search", and the report says what the search was.
* It cannot judge whether a domain has named a quantity honestly. A statement
  match is exact-string containment on identity strings, so a generator that
  spells the same thing two ways defeats it (``discovery/README.md``, dedup
  failure mode 3).
* It cannot tell a *significant* find from a merely unrecognised one. ``known``
  is a statement about the catalogue, not about importance.
"""

from __future__ import annotations

import ast
import datetime as _dt
import itertools
import math
import re
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field, replace
from decimal import Context as _DecimalContext
from decimal import Decimal, InvalidOperation
from enum import StrEnum
from typing import Any, Final

import mpmath
from mpmath import mp, mpf

from ontology.schema import (
    Candidate,
    CandidateKind,
    KnownEntry,
    Verdict,
    VerdictStatus,
    claim_keys,
    verdict_reasons,
)

__all__ = [
    # version
    "KNOWNNESS_VERSION",
    # errors
    "KnownnessError",
    # the constant basis
    "BasisConstant",
    "DEFAULT_BASIS",
    "basis_by_name",
    # closed-form identification
    "Identification",
    "IdentificationReport",
    "IdentificationConfidence",
    "identify_constant",
    "closed_form",
    "safe_eval_expression",
    "DEFAULT_BASE_DIGITS",
    "DEFAULT_ESCALATED_DIGITS",
    "DEFAULT_GUARD_DIGITS",
    "DEFAULT_MAX_TERMS",
    "DEFAULT_MAXCOEFF",
    "DEFAULT_MIN_SURPLUS_DIGITS",
    # the known-facts registry
    "KnownFact",
    "FACT_STATUSES",
    "FactMatch",
    "KnownFactRegistry",
    "KNOWN_FACTS",
    "GENERAL_FACTS",
    "default_fact_matcher",
    # the literature interface
    "LiteratureStatus",
    "LiteratureResult",
    "LiteratureBackend",
    "OfflineLiteratureBackend",
    "OFFLINE_BACKEND",
    "check_literature",
    "NOT_RECOGNISED_OFFLINE",
    "FORBIDDEN_LABEL_WORDS",
    "funnel_label",
    # the gate
    "Knownness",
    "KnownnessReport",
    "screen_known",
]

KNOWNNESS_VERSION: Final[str] = "1.0"


class KnownnessError(Exception):
    """A misuse of this module's own contracts (not a failed match)."""


# ---------------------------------------------------------------------------
# Numeric helpers
# ---------------------------------------------------------------------------

_NUMERIC_RE: Final[re.Pattern[str]] = re.compile(
    r"^[+-]?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?$"
)
_LOCAL_PATH_RE: Final[re.Pattern[str]] = re.compile(
    r"(?:/Users/|/home/|[A-Za-z]:\\Users\\)"
)

#: What a bare Python float can carry: 53 bits is 15.95 decimal digits, and the
#: honest integer floor of that is 15.
FLOAT64_DIGITS: Final[int] = 15


def _dec(value: Any) -> Decimal | None:
    """``value`` as an exact :class:`Decimal`, or ``None`` if it is not a number."""
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, int):
        return Decimal(value)
    if isinstance(value, float):
        return Decimal(repr(value)) if math.isfinite(value) else None
    if isinstance(value, Decimal):
        return value if value.is_finite() else None
    if isinstance(value, str):
        text = value.strip()
        if not _NUMERIC_RE.match(text):
            return None
        try:
            return Decimal(text)
        except InvalidOperation:  # pragma: no cover - regex already filtered
            return None
    # mpmath types and anything else that can spell itself as a decimal.
    try:
        return Decimal(mpmath.nstr(value, mp.dps, strip_zeros=False))
    except (TypeError, ValueError, InvalidOperation):
        return None


def _significant_digits(value: Any) -> int:
    """How many significant decimal digits the *literal* actually carries.

    Trailing zeros are stripped, which under-counts rather than over-counts: a
    value written ``1.500`` is credited with two digits, not four. Over-counting
    here would let the escalation check pass on digits nobody measured.
    """
    dec = _dec(value)
    if dec is None:
        return 0
    # Not ``Decimal.normalize()``: that rounds to the *ambient* decimal context,
    # which defaults to 28 digits and would silently cap a 40-digit literal.
    digits = dec.as_tuple().digits
    last = len(digits)
    while last > 1 and digits[last - 1] == 0:
        last -= 1
    return max(1, last)


def _available_digits(value: Any, known_digits: int | None) -> int:
    """The digits of ``value`` the caller is entitled to rely on."""
    if known_digits is not None:
        if known_digits < 1:
            raise KnownnessError("known_digits must be at least 1")
        return known_digits
    if isinstance(value, float):
        return FLOAT64_DIGITS
    if isinstance(value, (str, Decimal, int)):
        return _significant_digits(value)
    # An mpmath number carries the working precision it was built at; the only
    # honest reading available here is the current context.
    return int(mp.dps)


def _round_to_digits(value: Any, digits: int) -> Decimal:
    """``value`` rounded to ``digits`` significant decimal digits."""
    dec = _dec(value)
    if dec is None:
        raise KnownnessError(f"not a finite number: {value!r}")
    return _DecimalContext(prec=max(1, digits)).create_decimal(dec)


def _mpf(value: Any) -> Any:
    """A value as an ``mpf`` at the *current* working precision."""
    if isinstance(value, Decimal):
        return mpf(str(value))
    if isinstance(value, str):
        return mpf(value)
    return mpmath.mpmathify(value)


# ---------------------------------------------------------------------------
# The constant basis
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class BasisConstant:
    """One element of the basis an integer-relation search works over.

    ``evaluate`` is called inside an ``mp.workdps`` block, so it must read the
    ambient precision rather than capture one.
    """

    name: str
    identify_name: str
    evaluate: Callable[[], Any]
    description: str = ""

    def value(self) -> Any:
        return self.evaluate()


DEFAULT_BASIS: Final[tuple[BasisConstant, ...]] = (
    BasisConstant("pi", "pi", lambda: mp.pi, "Archimedes' constant"),
    BasisConstant("pi^2", "pi**2", lambda: mp.pi**2, "pi squared; zeta(2) = pi^2/6"),
    BasisConstant("e", "e", lambda: mp.e, "the base of the natural logarithm"),
    BasisConstant("gamma", "euler", lambda: mp.euler, "the Euler-Mascheroni constant"),
    BasisConstant("log(2)", "log(2)", lambda: mp.log(2), "the natural log of 2"),
    BasisConstant("log(pi)", "log(pi)", lambda: mp.log(mp.pi), "the natural log of pi"),
    BasisConstant("zeta(3)", "zeta(3)", lambda: mp.zeta(3), "Apery's constant"),
    BasisConstant("catalan", "catalan", lambda: mp.catalan, "Catalan's constant"),
    BasisConstant("sqrt(2)", "sqrt(2)", lambda: mp.sqrt(2), "the square root of 2"),
    BasisConstant("sqrt(3)", "sqrt(3)", lambda: mp.sqrt(3), "the square root of 3"),
    BasisConstant("sqrt(5)", "sqrt(5)", lambda: mp.sqrt(5), "the square root of 5"),
)


def basis_by_name(
    basis: Sequence[BasisConstant] = DEFAULT_BASIS,
) -> dict[str, BasisConstant]:
    """Name -> element. Names are unique within a basis; a clash is an error."""
    out: dict[str, BasisConstant] = {}
    for element in basis:
        if element.name in out:
            raise KnownnessError(f"duplicate basis name {element.name!r}")
        out[element.name] = element
    return out


# ---------------------------------------------------------------------------
# A safe evaluator for mpmath.identify's own output
# ---------------------------------------------------------------------------

_EVAL_NAMES: Final[frozenset[str]] = frozenset(
    {"pi", "e", "euler", "catalan", "phi", "degree", "log", "sqrt", "exp", "zeta", "ln"}
)
_EVAL_NODES: Final[tuple[type, ...]] = (
    ast.Expression,
    ast.BinOp,
    ast.UnaryOp,
    ast.Constant,
    ast.Name,
    ast.Call,
    ast.Load,
    ast.Add,
    ast.Sub,
    ast.Mult,
    ast.Div,
    ast.Pow,
    ast.USub,
    ast.UAdd,
)


class _IntToMpf(ast.NodeTransformer):
    """Rewrite integer literals as ``mpf(n)`` so ``1/7`` is not a float."""

    def visit_Constant(self, node: ast.Constant) -> ast.AST:
        if isinstance(node.value, int) and not isinstance(node.value, bool):
            return ast.Call(
                func=ast.Name(id="mpf", ctx=ast.Load()),
                args=[ast.Constant(value=node.value)],
                keywords=[],
            )
        return node


def safe_eval_expression(expression: str, dps: int) -> Any:
    """Evaluate a closed-form expression string at ``dps`` digits, safely.

    Only arithmetic, a whitelist of constant names and a whitelist of unary
    functions are permitted; every integer literal is promoted to ``mpf`` first,
    so ``(1/7)`` is a seventh and not a double. Anything else raises
    :class:`KnownnessError`. This exists because :func:`mpmath.identify` returns
    a *string*, and a string that is going to be evaluated must be checked.
    """
    try:
        tree = ast.parse(expression, mode="eval")
    except SyntaxError as exc:
        raise KnownnessError(f"not an expression: {expression!r}") from exc
    for node in ast.walk(tree):
        if not isinstance(node, _EVAL_NODES):
            raise KnownnessError(
                f"disallowed syntax {type(node).__name__} in {expression!r}"
            )
        if isinstance(node, ast.Name) and node.id not in _EVAL_NAMES:
            raise KnownnessError(f"disallowed name {node.id!r} in {expression!r}")
        if isinstance(node, ast.Call) and not (
            isinstance(node.func, ast.Name) and node.func.id in _EVAL_NAMES
        ):
            raise KnownnessError(f"disallowed call in {expression!r}")
        if isinstance(node, ast.Constant) and not isinstance(
            node.value, (int, float)
        ):
            raise KnownnessError(f"disallowed literal {node.value!r}")
    tree = ast.fix_missing_locations(_IntToMpf().visit(tree))
    with mp.workdps(dps):
        namespace: dict[str, Any] = {
            "__builtins__": {},
            "mpf": mpf,
            "pi": mp.pi,
            "e": mp.e,
            "euler": mp.euler,
            "catalan": mp.catalan,
            "phi": mp.phi,
            "degree": mp.degree,
            "log": mp.log,
            "ln": mp.log,
            "sqrt": mp.sqrt,
            "exp": mp.exp,
            "zeta": mp.zeta,
        }
        return eval(compile(tree, "<closed-form>", "eval"), namespace)  # noqa: S307


# ---------------------------------------------------------------------------
# Closed-form identification
# ---------------------------------------------------------------------------

DEFAULT_BASE_DIGITS: Final[int] = 15
DEFAULT_ESCALATED_DIGITS: Final[int] = 40
DEFAULT_GUARD_DIGITS: Final[int] = 3
DEFAULT_MAX_TERMS: Final[int] = 3
DEFAULT_MAXCOEFF: Final[int] = 24
#: Digits of agreement demanded *above* the log10 size of the search space
#: before a relation is called an identification. Eight digits means a spurious
#: match would have to be a one-in-10^8 accident on top of the multiple
#: comparisons already accounted for.
DEFAULT_MIN_SURPLUS_DIGITS: Final[float] = 8.0


class IdentificationConfidence(StrEnum):
    """How much the escalation actually established. Three states, no score."""

    #: The relation was re-verified against the value recomputed at strictly
    #: higher precision, and the surplus over the search space is sufficient.
    CONFIRMED = "confirmed"
    #: A relation was found, but no higher-precision value was available, or the
    #: surplus over the search space was too small to rule out coincidence.
    UNCONFIRMED = "unconfirmed"
    #: A relation was found at low precision and *failed* at higher precision.
    #: This is the false positive the escalation exists to catch.
    REJECTED = "rejected"


@dataclass(frozen=True)
class Identification:
    """One candidate closed form, with the measurements that judge it."""

    expression: str
    engine: str
    terms: tuple[tuple[int, str], ...]
    denominator: int
    base_digits: int
    escalated_digits: int | None = None
    digits_confirmed: float | None = None
    defect: str | None = None
    survived_escalation: bool = False
    search_space_log10: float = 0.0
    surplus_digits: float | None = None
    confidence: IdentificationConfidence = IdentificationConfidence.UNCONFIRMED
    cross_check: str | None = None

    @property
    def n_terms(self) -> int:
        """Non-rational terms — the complexity Occam is applied to."""
        return sum(1 for _, name in self.terms if name != "1")

    @property
    def complexity(self) -> tuple[int, int, int]:
        """Sort key: fewer terms, smaller coefficients, smaller denominator."""
        return (
            self.n_terms,
            sum(abs(c) for c, _ in self.terms) + abs(self.denominator),
            abs(self.denominator),
        )

    def evaluate(self, dps: int, basis: Sequence[BasisConstant] = DEFAULT_BASIS) -> Any:
        """Re-evaluate the expression at ``dps`` digits from the basis."""
        table = basis_by_name(basis)
        with mp.workdps(dps + 5):
            total = mpf(0)
            for coefficient, name in self.terms:
                unit = mpf(1) if name == "1" else table[name].value()
                total += mpf(coefficient) * unit
            return +(total / mpf(self.denominator))

    def to_dict(self) -> dict[str, Any]:
        return {
            "expression": self.expression,
            "engine": self.engine,
            "terms": [[c, n] for c, n in self.terms],
            "denominator": self.denominator,
            "base_digits": self.base_digits,
            "escalated_digits": self.escalated_digits,
            "digits_confirmed": self.digits_confirmed,
            "defect": self.defect,
            "survived_escalation": self.survived_escalation,
            "search_space_log10": self.search_space_log10,
            "surplus_digits": self.surplus_digits,
            "confidence": self.confidence.value,
            "cross_check": self.cross_check,
        }


@dataclass(frozen=True)
class IdentificationReport:
    """The outcome of a closed-form search, including what it refused.

    ``identified`` is the only field a caller may treat as a find. ``provisional``
    is the honest record of what the low-precision search proposed — a dissolved
    match is information, not embarrassment, and the funnel's metrics want it.
    """

    identified: bool
    match: Identification | None
    provisional: tuple[Identification, ...]
    reason: str
    base_digits: int
    escalated_digits: int | None
    search_space_log10: float
    min_surplus_digits: float
    n_provisional: int = 0
    n_rejected: int = 0

    @property
    def rejected(self) -> tuple[Identification, ...]:
        """The retained provisional matches that failed the escalation.

        ``n_rejected`` is the full count; ``provisional`` keeps only the
        simplest few, because a nine-digit search over three-term relations can
        return a hundred coincidences and the *number* is the useful statistic.
        """
        return tuple(
            i
            for i in self.provisional
            if i.confidence is IdentificationConfidence.REJECTED
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "identified": self.identified,
            "match": self.match.to_dict() if self.match else None,
            "provisional": [i.to_dict() for i in self.provisional],
            "n_provisional": self.n_provisional,
            "n_rejected": self.n_rejected,
            "reason": self.reason,
            "base_digits": self.base_digits,
            "escalated_digits": self.escalated_digits,
            "search_space_log10": self.search_space_log10,
            "min_surplus_digits": self.min_surplus_digits,
        }


def _render(coefficients: Sequence[int], names: Sequence[str]) -> tuple[
    str, tuple[tuple[int, str], int]
]:
    """Turn a PSLQ relation into ``x = <expression>``.

    ``coefficients[0]`` multiplies the unknown; ``names`` labels the rest, with
    ``"1"`` for the rational term. Returns the rendered string alongside the
    normalised ``(terms, denominator)`` the expression was built from.
    """
    lead = coefficients[0]
    if lead == 0:
        raise KnownnessError("relation does not involve the unknown")
    numerator = [-c for c in coefficients[1:]]
    denominator = lead
    if denominator < 0:
        denominator = -denominator
        numerator = [-c for c in numerator]
    divisor = math.gcd(denominator, *(abs(c) for c in numerator))
    if divisor > 1:
        denominator //= divisor
        numerator = [c // divisor for c in numerator]
    terms = tuple((c, n) for c, n in zip(numerator, names) if c != 0)
    if not terms:
        terms = ((0, "1"),)

    pieces: list[str] = []
    for index, (coefficient, name) in enumerate(terms):
        magnitude = abs(coefficient)
        if name == "1":
            body = str(magnitude)
        elif magnitude == 1:
            body = name
        else:
            body = f"{magnitude}*{name}"
        if index == 0:
            pieces.append(f"-{body}" if coefficient < 0 else body)
        else:
            pieces.append((" - " if coefficient < 0 else " + ") + body)
    body = "".join(pieces)
    if denominator == 1:
        expression = body
    elif len(terms) == 1:
        expression = f"{body}/{denominator}"
    else:
        expression = f"({body})/{denominator}"
    return expression, (terms, denominator)


def _search_level(
    x: Any,
    basis: Sequence[BasisConstant],
    size: int,
    maxcoeff: int,
    tol: Any,
) -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    """Every relation ``pslq`` finds at one subset size. Called inside workdps."""
    found: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    values = [element.value() for element in basis]
    for subset in itertools.combinations(range(len(basis)), size):
        vector = [x, mpf(1)] + [values[i] for i in subset]
        try:
            relation = mpmath.pslq(vector, tol=tol, maxcoeff=maxcoeff, maxsteps=200)
        except (ValueError, ZeroDivisionError):  # pragma: no cover - defensive
            relation = None
        if not relation or relation[0] == 0:
            continue
        found.append((tuple(subset), tuple(int(c) for c in relation)))
    return found


def _level_space_log10(n_basis: int, size: int, maxcoeff: int) -> float:
    """log10 of the number of integer vectors this level could have returned."""
    subsets = math.comb(n_basis, size)
    per_subset = (2 * maxcoeff + 1) ** (size + 2)
    return math.log10(subsets * per_subset)


def identify_constant(
    value: Any = None,
    *,
    provider: Callable[[int], Any] | None = None,
    known_digits: int | None = None,
    base_digits: int = DEFAULT_BASE_DIGITS,
    escalated_digits: int = DEFAULT_ESCALATED_DIGITS,
    guard_digits: int = DEFAULT_GUARD_DIGITS,
    basis: Sequence[BasisConstant] = DEFAULT_BASIS,
    max_terms: int = DEFAULT_MAX_TERMS,
    maxcoeff: int = DEFAULT_MAXCOEFF,
    min_surplus_digits: float = DEFAULT_MIN_SURPLUS_DIGITS,
    cross_check: bool = True,
    max_provisional: int = 12,
) -> IdentificationReport:
    """Is ``value`` a recognisable closed form? Offline, and with escalation.

    The search is an integer-relation hunt: for each subset of ``basis`` of size
    ``0 .. max_terms``, :func:`mpmath.pslq` looks for integers ``c`` with
    ``c0*x + c1 + sum(ci*bi) = 0``. Subsets are tried in order of size, so the
    simplest expression that works wins, and only the levels actually searched
    are charged to the multiple-comparison budget.

    **The escalation, which is the point.** A relation found at ``base_digits``
    is *provisional*. It becomes an identification only if the value recomputed
    at ``escalated_digits`` still satisfies it, and only if the digits of
    agreement exceed ``log10`` of the size of the search space by
    ``min_surplus_digits``. A match that dissolves is returned with
    ``confidence = REJECTED`` and ``identified = False``: a false positive is a
    non-result, and this function will not dress one up.

    Parameters
    ----------
    value:
        The measured number. Used directly when no ``provider`` is given, in
        which case its own significant digits set the escalation ceiling.
    provider:
        ``dps -> value`` — recomputes the quantity at a requested precision.
        This is what makes a real escalation possible; without it the ceiling is
        whatever the literal already carried, and a ``float`` carries 15 digits,
        which is not enough to confirm a three-term relation. Supplying a
        provider that returns the closed form itself would make the test
        circular; supply the laboratory routine that computes the quantity.
    known_digits:
        Overrides the inferred number of trustworthy digits in ``value``.

    Returns
    -------
    IdentificationReport
        Never ``None``; ``report.identified`` is the only claim.
    """
    if value is None and provider is None:
        raise KnownnessError("identify_constant needs a value or a provider")
    if base_digits < 4:
        raise KnownnessError("base_digits must be at least 4")
    if max_terms < 0 or max_terms > len(basis):
        raise KnownnessError("max_terms must lie in 0..len(basis)")

    # -- the two views of the quantity -------------------------------------
    if provider is not None:
        base_value: Any = provider(base_digits + guard_digits)
        ceiling = escalated_digits
    else:
        # Without a provider the literal is all there is, so the base search may
        # not use digits the caller did not vouch for, and the ceiling is the
        # literal's own resolution. A float carries 15 digits and no more.
        ceiling = min(escalated_digits, _available_digits(value, known_digits))
        base_digits = max(4, min(base_digits, ceiling))
        base_value = _round_to_digits(value, base_digits)
    headroom = ceiling > base_digits
    escalated_value: Any | None
    if not headroom:
        escalated_value = None
    elif provider is not None:
        escalated_value = provider(ceiling + guard_digits)
    else:
        escalated_value = value

    # -- level-by-level integer-relation search ----------------------------
    provisional: list[Identification] = []
    space_log10 = 0.0
    winner: Identification | None = None
    reason = ""
    seen: set[str] = set()

    work = base_digits + guard_digits + 15
    for size in range(0, max_terms + 1):
        space_log10 = math.log10(
            10.0**space_log10 + 10.0 ** _level_space_log10(len(basis), size, maxcoeff)
        )
        with mp.workdps(work):
            x = _mpf(base_value)
            tol = mpf(10) ** (-(base_digits - guard_digits)) * max(mpf(1), abs(x))
            relations = _search_level(x, basis, size, maxcoeff, tol)
        level: list[Identification] = []
        for subset, coefficients in relations:
            names = ["1"] + [basis[i].name for i in subset]
            try:
                expression, (terms, denominator) = _render(coefficients, names)
            except KnownnessError:  # pragma: no cover - filtered above
                continue
            level.append(
                Identification(
                    expression=expression,
                    engine="pslq",
                    terms=terms,
                    denominator=denominator,
                    base_digits=base_digits,
                    escalated_digits=ceiling if headroom else None,
                    search_space_log10=space_log10,
                )
            )
        # Distinct subsets often reduce to the same expression (a zero
        # coefficient drops a constant); count each expression once.
        unique: list[Identification] = []
        for item in sorted(level, key=lambda i: i.complexity):
            if item.expression in seen:
                continue
            seen.add(item.expression)
            unique.append(item)

        judged = [
            _judge(item, escalated_value, ceiling, guard_digits, basis,
                   min_surplus_digits, headroom, space_log10)
            for item in unique
        ]
        provisional.extend(judged)
        confirmed = [
            i for i in judged if i.confidence is IdentificationConfidence.CONFIRMED
        ]
        if confirmed:
            # Occam: the first level that yields a confirmed relation wins, and
            # the levels not searched are not charged to the budget.
            winner = min(confirmed, key=lambda i: i.complexity)
            reason = (
                f"relation confirmed at {ceiling} digits "
                f"({winner.digits_confirmed:.1f} digits of agreement, "
                f"{winner.surplus_digits:.1f} above the search space)"
            )
            break
        # Nothing survived at this size. Keep going: a low-precision coincidence
        # among two constants must not hide a real relation among three.

    if winner is None:
        # Re-charge every provisional with the *whole* space that was searched;
        # the per-level figures were only ever right for a search that stopped.
        provisional = [
            replace(
                item,
                search_space_log10=space_log10,
                surplus_digits=(
                    None
                    if item.digits_confirmed is None
                    else item.digits_confirmed - space_log10
                ),
            )
            for item in provisional
        ]
        survived = [i for i in provisional if i.survived_escalation]
        if not provisional:
            reason = (
                f"no integer relation was found at {base_digits} digits over "
                f"{len(basis)} constants, up to {max_terms} terms"
            )
        elif not headroom and provider is not None:
            reason = (
                f"a relation was found but no escalation was asked for: "
                f"escalated_digits={ceiling} does not exceed base_digits="
                f"{base_digits}, so nothing re-verified it"
            )
        elif not headroom:
            reason = (
                f"a relation was found but could not be escalated: the value "
                f"carries {ceiling} digits and the search already used "
                f"{base_digits}. Supply a provider that recomputes it."
            )
        elif survived:
            # Report the *surplus*, not the size of the space. Printing
            # ``space_log10`` here (as this line once did) put a number in the
            # message that contradicted the sentence around it: a search space
            # of 10.7 digits was rendered as a surplus of 10.7 "below 8.0".
            best = max(i.surplus_digits or 0.0 for i in survived)
            reason = (
                f"a relation survived to {ceiling} digits but its surplus over "
                f"the search space ({best:.1f} digits: {max((i.digits_confirmed or 0.0) for i in survived):.1f} "
                f"confirmed against a space of {space_log10:.1f}) is below "
                f"{min_surplus_digits}"
            )
        else:
            reason = (
                f"provisional match dissolved at {ceiling} digits: a "
                "low-precision coincidence, not an identification"
            )

    if winner is not None and cross_check:
        winner = replace(
            winner,
            cross_check=_cross_check(winner, escalated_value, ceiling, basis),
        )
        provisional = [
            winner if i.expression == winner.expression else i for i in provisional
        ]

    n_provisional = len(provisional)
    n_rejected = sum(
        1 for i in provisional if i.confidence is IdentificationConfidence.REJECTED
    )
    kept = sorted(provisional, key=lambda i: i.complexity)[: max(0, max_provisional)]
    return IdentificationReport(
        identified=winner is not None,
        match=winner,
        provisional=tuple(kept),
        reason=reason,
        base_digits=base_digits,
        escalated_digits=ceiling if headroom else None,
        search_space_log10=space_log10,
        min_surplus_digits=min_surplus_digits,
        n_provisional=n_provisional,
        n_rejected=n_rejected,
    )


def _judge(
    item: Identification,
    escalated_value: Any | None,
    ceiling: int,
    guard_digits: int,
    basis: Sequence[BasisConstant],
    min_surplus_digits: float,
    headroom: bool,
    space_log10: float,
) -> Identification:
    """Re-verify one provisional relation at the escalated precision."""
    item = replace(item, search_space_log10=space_log10)
    if not headroom or escalated_value is None:
        return replace(item, confidence=IdentificationConfidence.UNCONFIRMED)
    work = ceiling + guard_digits + 15
    with mp.workdps(work):
        target = _mpf(escalated_value)
        predicted = item.evaluate(work, basis)
        defect = abs(target - predicted)
        scale = abs(target) if target != 0 else mpf(1)
        relative = defect / scale
        if relative == 0:
            digits_confirmed = float(ceiling)
        else:
            digits_confirmed = min(float(ceiling), float(-mp.log10(relative)))
        survived = relative <= mpf(10) ** (-(ceiling - guard_digits))
        defect_text = mpmath.nstr(defect, 6)
    surplus = digits_confirmed - space_log10
    if not survived:
        confidence = IdentificationConfidence.REJECTED
    elif surplus >= min_surplus_digits:
        confidence = IdentificationConfidence.CONFIRMED
    else:
        confidence = IdentificationConfidence.UNCONFIRMED
    return replace(
        item,
        escalated_digits=ceiling,
        digits_confirmed=digits_confirmed,
        defect=defect_text,
        survived_escalation=bool(survived),
        surplus_digits=surplus,
        confidence=confidence,
    )


def _cross_check(
    item: Identification,
    escalated_value: Any | None,
    ceiling: int,
    basis: Sequence[BasisConstant],
) -> str | None:
    """Ask :func:`mpmath.identify` the same question, independently.

    ``identify`` is given only the constants the winning relation used: with the
    whole basis it is orders of magnitude slower and returns nothing useful. A
    ``None`` here is not a refutation — the two engines have different search
    strategies — but agreement is worth recording.
    """
    if escalated_value is None:
        return None
    table = basis_by_name(basis)
    constants = [
        table[name].identify_name for _, name in item.terms if name in table
    ]
    try:
        with mp.workdps(ceiling + 10):
            found = mpmath.identify(_mpf(escalated_value), constants)
    except (ValueError, TypeError, ZeroDivisionError):  # pragma: no cover
        return None
    return str(found) if found else None


def closed_form(value: Any = None, **kwargs: Any) -> str | None:
    """The confirmed closed form of ``value``, or ``None``. See :func:`identify_constant`."""
    report = identify_constant(value, **kwargs)
    return report.match.expression if report.identified and report.match else None


# ---------------------------------------------------------------------------
# The known-facts registry
# ---------------------------------------------------------------------------


def _norm_key(text: Any) -> str:
    return " ".join(str(text).strip().casefold().split())


@dataclass(frozen=True)
class FactMatch:
    """Why a candidate was judged already known, and by which entry."""

    fact_id: str
    match_kind: str  # "value" | "statement" | "identity"
    source: str
    canonical_form: str
    statement: str = ""
    detail: Mapping[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "fact_id": self.fact_id,
            "match_kind": self.match_kind,
            "source": self.source,
            "canonical_form": self.canonical_form,
            "statement": self.statement,
            "detail": dict(self.detail),
        }


#: How settled a catalogue entry is. ``known`` is one verdict, but "known to be
#: true" and "known to be an open question" are not the same knowledge, and a
#: catalogue that cannot tell them apart lets a matched conjecture be read as a
#: matched theorem. The vocabulary is closed on purpose: a free-text field would
#: be re-derived by every reader as a confidence score.
#:
#: * ``established`` — settled, and the entry does not say by which route.
#: * ``theorem`` — proved. A citation exists for the proof itself.
#: * ``conjecture`` — believed on evidence, not proved. Matching it says the
#:   observation is not new; it says nothing about whether it is true.
#: * ``equivalent_to_open_problem`` — provably equivalent to a question nobody
#:   has settled. No finite computation moves it in either direction.
#: * ``disproved`` — settled the other way. A match here is a warning, not a
#:   confirmation: the observation reproduces something already known to fail.
FACT_STATUSES: Final[tuple[str, ...]] = (
    "established",
    "theorem",
    "conjecture",
    "equivalent_to_open_problem",
    "disproved",
)


@dataclass(frozen=True)
class KnownFact:
    """One citable thing the laboratory, or the literature, already knows.

    Four parts, all mandatory in spirit: what it says (``statement``), how it is
    written (``canonical_form``), who says so (``source``), and how to recognise
    it (``keys``/``value``, or a bespoke ``matcher``). An entry without a source
    is an opinion, and :meth:`KnownFactRegistry.register` refuses it.

    ``status`` is the fifth part and it is not decoration: see
    :data:`FACT_STATUSES`. Every match carries it through into the verdict's
    evidence as ``literature_status``, so a record can be read for what it
    actually established.
    """

    id: str
    statement: str
    canonical_form: str
    source: str
    domain: str = "general"
    #: **Conjunctive.** Every one of these must appear among a candidate's
    #: identity strings for a statement match. Use it to demand a combination.
    keys: tuple[str, ...] = ()
    #: **Disjunctive.** Any single one of these suffices. This is where spelling
    #: variants of the same name belong ("Hasse bound", "Hasse-Weil bound") —
    #: putting them in ``keys`` would demand a candidate spell it both ways.
    aliases: tuple[str, ...] = ()
    value: str | float | None = None
    tolerance: str | float | None = None
    matcher: Callable[[Candidate, "KnownFact"], FactMatch | None] | None = None
    tags: tuple[str, ...] = ()
    #: One of :data:`FACT_STATUSES`. The default is the weakest true thing.
    status: str = "established"

    def match(self, candidate: Candidate) -> FactMatch | None:
        """Does this fact already cover ``candidate``?"""
        if self.matcher is not None:
            return self.matcher(candidate, self)
        return default_fact_matcher(candidate, self)

    def to_known_entry(self) -> KnownEntry:
        """The ``schema.KnownEntry`` view, for ``schema.match_known`` interop.

        ``schema.KnownEntry`` has only the conjunctive form, so an entry that
        relies on ``aliases`` matches less there than it does here. The bridge
        exists for interoperability, not as a replacement for :meth:`match`.
        """
        return KnownEntry(
            id=self.id,
            reference=self.source,
            keys=self.keys,
            value=self.value,
            tolerance=self.tolerance,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "statement": self.statement,
            "canonical_form": self.canonical_form,
            "source": self.source,
            "domain": self.domain,
            "keys": list(self.keys),
            "aliases": list(self.aliases),
            "value": self.value,
            "tolerance": self.tolerance,
            "has_custom_matcher": self.matcher is not None,
            "tags": list(self.tags),
            "status": self.status,
        }


def default_fact_matcher(candidate: Candidate, fact: KnownFact) -> FactMatch | None:
    """The matcher used when an entry supplies none.

    Two routes, in decreasing strength:

    * **value** — the candidate is a ``constant`` whose measured value agrees
      with the entry to within *its own* error bound plus the entry's. Matching
      to the digits the candidate actually determined is a strong test; matching
      to a generous global tolerance is not, which is why no global tolerance
      exists here.
    * **statement** — every one of the entry's ``keys`` appears among the
      candidate's identity strings, or any single one of its ``aliases`` does.
      This is only as good as the domain's naming discipline
      (``discovery/README.md``, dedup failure mode 3): a generator that spells a
      quantity a third way will not match, and this matcher cannot tell.
    """
    if fact.value is not None and candidate.kind is CandidateKind.CONSTANT:
        measured = _dec(candidate.claim.get("value"))
        target = _dec(fact.value)
        own = _dec(candidate.evidence.get("uncertainty"))
        theirs = _dec(fact.tolerance) or Decimal(0)
        if measured is not None and target is not None and own is not None and own > 0:
            defect = abs(measured - target)
            budget = own + abs(theirs)
            if defect <= budget:
                return FactMatch(
                    fact_id=fact.id,
                    match_kind="value",
                    source=fact.source,
                    canonical_form=fact.canonical_form,
                    statement=fact.statement,
                    detail={
                        "defect": float(defect),
                        "tolerance": float(budget),
                        "own_uncertainty": float(own),
                        "literature_status": fact.status,
                    },
                )
    if fact.keys or fact.aliases:
        keys = {_norm_key(k) for k in claim_keys(candidate.kind, candidate.claim)}
        wanted = {_norm_key(k) for k in fact.keys}
        matched: set[str] | None = None
        if wanted and wanted <= keys:
            matched = wanted
        else:
            hits = {_norm_key(a) for a in fact.aliases} & keys
            if hits:
                matched = hits
        if matched:
            return FactMatch(
                fact_id=fact.id,
                match_kind="statement",
                source=fact.source,
                canonical_form=fact.canonical_form,
                statement=fact.statement,
                detail={
                    "matched_keys": sorted(matched),
                    "literature_status": fact.status,
                },
            )
    return None


class KnownFactRegistry:
    """A curated table of established results, keyed by id.

    Domain-agnostic in mechanism, domain-populated in content: this module
    registers :data:`GENERAL_FACTS` (mathematics anyone would recognise), and a
    domain module registers the rest. Registration is validated — an entry with
    no source, or with a machine-local path in it, is refused — because a
    catalogue that accepts anything cannot make ``known`` a meaningful verdict.
    """

    def __init__(self, facts: Iterable[KnownFact] = ()) -> None:
        self._facts: dict[str, KnownFact] = {}
        self.register_all(facts)

    # -- population -------------------------------------------------------
    def register(self, fact: KnownFact, *, replace: bool = False) -> KnownFact:
        """Add one entry. Raises on a malformed entry or a duplicate id."""
        reasons = self.reasons(fact)
        if reasons:
            raise KnownnessError(
                f"cannot register {fact.id!r}: " + "; ".join(reasons)
            )
        if fact.id in self._facts and not replace:
            raise KnownnessError(
                f"a fact with id {fact.id!r} is already registered; "
                "pass replace=True to supersede it"
            )
        self._facts[fact.id] = fact
        return fact

    def register_all(
        self, facts: Iterable[KnownFact], *, replace: bool = False
    ) -> tuple[KnownFact, ...]:
        return tuple(self.register(f, replace=replace) for f in facts)

    @staticmethod
    def reasons(fact: KnownFact) -> tuple[str, ...]:
        """Every way ``fact`` fails the catalogue's own standards."""
        bad: list[str] = []
        if not isinstance(fact, KnownFact):
            return (f"not a KnownFact: {fact!r}",)
        for name in ("id", "statement", "canonical_form", "source", "domain"):
            text = getattr(fact, name)
            if not isinstance(text, str) or not text.strip():
                bad.append(f"{name} must be non-empty text")
        if isinstance(fact.id, str) and " " in fact.id.strip():
            bad.append("id must not contain spaces (it is an identifier)")
        for name in ("keys", "aliases"):
            group = getattr(fact, name)
            if not isinstance(group, tuple) or any(
                not isinstance(k, str) or not k.strip() for k in group
            ):
                bad.append(f"{name} must be a tuple of non-empty strings")
        if fact.value is not None and _dec(fact.value) is None:
            bad.append("value must be a finite number or decimal string")
        if fact.tolerance is not None and _dec(fact.tolerance) is None:
            bad.append("tolerance must be a finite number or decimal string")
        if fact.value is not None and fact.tolerance is None:
            bad.append("a numeric entry must state the tolerance of its own value")
        if (
            not fact.keys
            and not fact.aliases
            and fact.value is None
            and fact.matcher is None
        ):
            bad.append(
                "an entry needs keys, aliases, a value or a matcher, or it can "
                "never match"
            )
        for name in ("statement", "canonical_form", "source"):
            text = getattr(fact, name)
            if isinstance(text, str) and _LOCAL_PATH_RE.search(text):
                bad.append(f"{name} contains a machine-local absolute path")
        if fact.status not in FACT_STATUSES:
            bad.append(
                f"status must be one of {list(FACT_STATUSES)}, got {fact.status!r}"
            )
        return tuple(bad)

    # -- query ------------------------------------------------------------
    def __len__(self) -> int:
        return len(self._facts)

    def __iter__(self) -> Iterator[KnownFact]:
        return iter(self._facts.values())

    def __contains__(self, fact_id: object) -> bool:
        return fact_id in self._facts

    def get(self, fact_id: str) -> KnownFact:
        try:
            return self._facts[fact_id]
        except KeyError as exc:
            raise KnownnessError(f"no such fact: {fact_id!r}") from exc

    def facts(self, domain: str | None = None) -> tuple[KnownFact, ...]:
        items = tuple(self._facts.values())
        if domain is None:
            return items
        return tuple(f for f in items if f.domain == domain)

    def domains(self) -> tuple[str, ...]:
        return tuple(sorted({f.domain for f in self._facts.values()}))

    def known_entries(self) -> tuple[KnownEntry, ...]:
        """The ``schema.KnownEntry`` view of the whole catalogue."""
        return tuple(f.to_known_entry() for f in self._facts.values())

    def match(self, candidate: Candidate) -> FactMatch | None:
        """The first entry that already covers ``candidate``, or ``None``.

        Entries are tried in registration order, so a domain's own precise
        statement is consulted before a general one only if it was registered
        first — an operator responsibility the registry does not disguise.
        """
        for fact in self._facts.values():
            hit = fact.match(candidate)
            if hit is not None:
                return hit
        return None

    def clear(self) -> None:
        """Empty the catalogue. Exists for tests and for domain reloads."""
        self._facts.clear()

    def snapshot(self) -> tuple[KnownFact, ...]:
        return tuple(self._facts.values())


# --- the domain-neutral part of the catalogue ------------------------------
#
# Mathematics anybody would recognise, with a citation each. Everything tied to
# what this particular laboratory studies belongs to a domain module, which
# registers into KNOWN_FACTS at import time.

GENERAL_FACTS: Final[tuple[KnownFact, ...]] = (
    KnownFact(
        id="euler-mascheroni-constant",
        statement=(
            "The Euler-Mascheroni constant gamma is the limit of "
            "1 + 1/2 + ... + 1/n - log n."
        ),
        canonical_form="gamma = 0.57721566490153286060651209008240243104...",
        source="DLMF 5.2.3; Sloane, OEIS A001620",
        domain="general",
        aliases=("gamma", "euler-mascheroni constant", "euler's constant"),
        value="0.5772156649015328606065120900824024310422",
        tolerance="1e-40",
        tags=("constant",),
    ),
    KnownFact(
        id="catalan-constant",
        statement="Catalan's constant G = sum (-1)^n/(2n+1)^2.",
        canonical_form="G = 0.91596559417721901505460351493238411077...",
        source="DLMF 25.11.40; Sloane, OEIS A006752",
        domain="general",
        aliases=("catalan's constant", "catalan constant", "catalan's g"),
        value="0.9159655941772190150546035149323841107741",
        tolerance="1e-40",
        tags=("constant",),
    ),
    KnownFact(
        id="apery-constant",
        statement="Apery's constant, proved irrational by Apery in 1978.",
        canonical_form="1.20205690315959428539973816151144999076...",
        source="Apery (1979), Asterisque 61, 11-13; Sloane, OEIS A002117",
        domain="general",
        aliases=("apery's constant", "apery constant", "zeta(3)"),
        value="1.2020569031595942853997381615114499907650",
        tolerance="1e-40",
        tags=("constant", "irrationality"),
    ),
    KnownFact(
        id="gue-wigner-surmise",
        statement=(
            "The Wigner surmise for the nearest-neighbour spacing distribution of "
            "the Gaussian Unitary Ensemble."
        ),
        canonical_form="p(s) = (32/pi^2) s^2 exp(-4 s^2/pi)",
        source="Wigner (1957); Mehta, Random Matrices, 3rd ed., ch. 1",
        domain="general",
        aliases=("gue wigner surmise", "wigner surmise", "gue spacing law"),
        tags=("random-matrix",),
    ),
    KnownFact(
        id="hasse-weil-bound",
        statement=(
            "For a smooth projective curve of genus g over F_q the number of "
            "rational points satisfies |N - (q+1)| <= 2 g sqrt(q); for elliptic "
            "curves this is Hasse's bound."
        ),
        canonical_form="|#C(F_q) - (q + 1)| <= 2 g sqrt(q)",
        source="Hasse (1936); Weil (1948); Silverman, AEC V.1.1",
        domain="general",
        aliases=("hasse bound", "hasse-weil bound", "weil bound"),
        tags=("finite-fields", "theorem"),
    ),
    KnownFact(
        id="prime-number-theorem",
        statement="The number of primes up to x is asymptotic to x/log x.",
        canonical_form="pi(x) ~ x/log(x) ~ li(x)",
        source="Hadamard (1896); de la Vallee Poussin (1896)",
        domain="general",
        aliases=("prime number theorem", "pnt"),
        tags=("analytic-number-theory", "theorem"),
    ),
    KnownFact(
        id="mertens-third-theorem",
        statement=(
            "The product over primes p <= x of (1 - 1/p)^(-1) is asymptotic to "
            "e^gamma log x."
        ),
        canonical_form="prod_{p<=x} (1 - 1/p)^{-1} ~ e^gamma log x",
        source="Mertens (1874), J. reine angew. Math. 78, 46-62",
        domain="general",
        aliases=("mertens' third theorem", "mertens third theorem"),
        tags=("analytic-number-theory", "theorem"),
    ),
    KnownFact(
        id="stirling-asymptotic",
        statement="Stirling's asymptotic expansion for the logarithm of the Gamma function.",
        canonical_form="log Gamma(z) ~ (z - 1/2) log z - z + log(2 pi)/2 + 1/(12 z) - ...",
        source="Stirling (1730); DLMF 5.11.1",
        domain="general",
        aliases=("stirling's formula", "stirling asymptotic", "stirling's approximation"),
        tags=("asymptotic", "theorem"),
    ),
)

#: The process-wide catalogue. Domain modules register into it at import time.
KNOWN_FACTS: Final[KnownFactRegistry] = KnownFactRegistry(GENERAL_FACTS)


# ---------------------------------------------------------------------------
# The literature check — an interface, and an honest one
# ---------------------------------------------------------------------------


class LiteratureStatus(StrEnum):
    """Three states, and the distinction between the last two is the point."""

    #: A lookup ran and the candidate is in the literature.
    FOUND = "found"
    #: A lookup ran against named sources and returned nothing. Only a backend
    #: that actually queried something may return this.
    NOT_FOUND = "not_found"
    #: No lookup ran. This is what offline operation returns, always.
    UNKNOWN = "unknown"


#: The only label the offline gate may attach to a candidate it did not
#: recognise. Not "novel", not "new", not "unpublished".
NOT_RECOGNISED_OFFLINE: Final[str] = "not-recognised-offline"

#: Words that may never appear in a label produced by this module. A search of
#: the literature is the only thing that could justify them, and this system
#: cannot perform one. Whole words only, so "renewed" and "originally" are not
#: caught by "new" and "original"; a multi-word entry is refused when every one
#: of its words is present.
FORBIDDEN_LABEL_WORDS: Final[tuple[str, ...]] = (
    "novel",
    "novelty",
    "new",
    "newly",
    "unpublished",
    "original",
    "first",
    "undiscovered",
    "unrecorded",
    "unseen",
    "unknown-to-science",
)


@dataclass(frozen=True)
class LiteratureResult:
    """What a literature lookup established — including that it did not run."""

    status: LiteratureStatus
    label: str
    backend: str
    online: bool
    sources_queried: tuple[str, ...] = ()
    detail: str = ""
    references: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        funnel_label(self.label)  # refuses a novelty claim outright
        if self.status is LiteratureStatus.NOT_FOUND and not self.sources_queried:
            raise KnownnessError(
                "'not_found' asserts that sources were consulted; name them, or "
                "return 'unknown'"
            )
        if self.status is LiteratureStatus.FOUND and not [
            r for r in self.references if isinstance(r, str) and r.strip()
        ]:
            # The symmetric, and stronger, requirement. 'found' is the claim that
            # manufactures a terminal ``known`` verdict, and ``verdict_reasons``
            # refuses that verdict without a reference — so a backend that says
            # 'found' and cites nothing would make the gate emit an unearned
            # verdict and the funnel abort. Refuse it at the source.
            raise KnownnessError(
                "'found' asserts that the observation is in the literature; cite "
                "at least one reference, or return 'unknown'"
            )
        if self.status is LiteratureStatus.UNKNOWN and self.online:
            raise KnownnessError("an online backend must not return 'unknown' silently")

    @property
    def establishes_novelty(self) -> bool:
        """Always ``False``. Kept as a property so callers can ask and be told."""
        return False

    def to_dict(self) -> dict[str, Any]:
        return {
            "status": self.status.value,
            "label": self.label,
            "backend": self.backend,
            "online": self.online,
            "sources_queried": list(self.sources_queried),
            "detail": self.detail,
            "references": list(self.references),
            "establishes_novelty": False,
        }


class LiteratureBackend:
    """The interface a real (networked) lookup would implement.

    A conforming backend names itself, says whether it had network access, and
    returns a :class:`LiteratureResult`. It may return
    :attr:`LiteratureStatus.NOT_FOUND` only if it actually queried the sources it
    names — otherwise the honest answer is ``UNKNOWN``.
    """

    name: str = "abstract"
    online: bool = False

    def lookup(self, candidate: Candidate) -> LiteratureResult:  # pragma: no cover
        raise NotImplementedError


class OfflineLiteratureBackend(LiteratureBackend):
    """The default: no network, therefore no lookup, therefore no conclusion.

    Returns :attr:`LiteratureStatus.UNKNOWN` for every candidate. This is not a
    placeholder to be optimistically reinterpreted downstream: the sources that
    would settle the question (OEIS, arXiv, MathSciNet, Zentralblatt, the LMFDB)
    are unreachable, so the only true statement available is "this system did not
    recognise it, offline".
    """

    name = "offline"
    online = False

    #: Named so the gap is legible, not so it looks thorough.
    WOULD_QUERY: Final[tuple[str, ...]] = (
        "OEIS",
        "arXiv",
        "MathSciNet",
        "zbMATH",
        "LMFDB",
    )

    def lookup(self, candidate: Candidate) -> LiteratureResult:
        return LiteratureResult(
            status=LiteratureStatus.UNKNOWN,
            label=NOT_RECOGNISED_OFFLINE,
            backend=self.name,
            online=False,
            sources_queried=(),
            detail=(
                "No network access: none of "
                + ", ".join(self.WOULD_QUERY)
                + " was consulted. 'unknown' means the literature was not "
                "checked, not that the observation is absent from it."
            ),
        )


OFFLINE_BACKEND: Final[OfflineLiteratureBackend] = OfflineLiteratureBackend()


def check_literature(
    candidate: Candidate, backend: LiteratureBackend | None = None
) -> LiteratureResult:
    """Ask the literature about ``candidate``. Offline, the answer is ``UNKNOWN``.

    **Offline degradation is the normal case here.** The default backend performs
    no lookup at all and says so in ``detail``; the caller gets
    :attr:`LiteratureStatus.UNKNOWN` and the label
    :data:`NOT_RECOGNISED_OFFLINE`. A funnel must not read that as novelty — see
    :func:`funnel_label`, which refuses to produce such a label at all.

    Pass a ``backend`` implementing :class:`LiteratureBackend` when a networked
    lookup becomes available; nothing else in this module needs to change.
    """
    chosen = backend if backend is not None else OFFLINE_BACKEND
    result = chosen.lookup(candidate)
    if not isinstance(result, LiteratureResult):  # pragma: no cover - defensive
        raise KnownnessError(f"backend {chosen.name!r} returned {result!r}")
    return result


def funnel_label(label: str) -> str:
    """Return ``label`` if a funnel may use it; raise if it claims novelty.

    The one thing this module must never let happen is a failed offline lookup
    being rendered as a discovery. This function is the choke point: every label
    produced here passes through it, and it refuses any of
    :data:`FORBIDDEN_LABEL_WORDS`.

    **What it does not do.** It is a word list, not a semantic check. A caller
    determined to claim novelty can spell it as a phrase this list does not
    contain (``"not-in-the-literature"`` passes). The guarantee is therefore
    narrow and exact: *no label this module itself emits can be a novelty
    claim*, and a test enumerates them. A third-party backend that lies in
    prose is beyond what any list can catch.
    """
    if not isinstance(label, str) or not label.strip():
        raise KnownnessError("a label must be non-empty text")
    words = set(re.split(r"[^a-z]+", label.casefold()))
    for word in FORBIDDEN_LABEL_WORDS:
        if set(re.split(r"[^a-z]+", word)) <= words:
            raise KnownnessError(
                f"label {label!r} claims novelty; offline this system can only say "
                f"{NOT_RECOGNISED_OFFLINE!r}"
            )
    return label


# ---------------------------------------------------------------------------
# The gate
# ---------------------------------------------------------------------------


class Knownness(StrEnum):
    """The gate's two possible answers. Neither of them is "new"."""

    #: Matched a catalogued fact, or a closed form that survived escalation.
    KNOWN = "known"
    #: Nothing offline recognised it. Says nothing about the literature.
    NOT_RECOGNISED_OFFLINE = NOT_RECOGNISED_OFFLINE


@dataclass(frozen=True)
class KnownnessReport:
    """Everything the gate concluded, and everything it declined to conclude."""

    candidate_id: str
    outcome: Knownness
    label: str
    references: tuple[str, ...]
    literature: LiteratureResult
    fact_match: FactMatch | None = None
    identification: IdentificationReport | None = None
    verdict: Verdict | None = None
    notes: tuple[str, ...] = ()

    @property
    def is_known(self) -> bool:
        return self.outcome is Knownness.KNOWN

    @property
    def establishes_novelty(self) -> bool:
        """Always ``False``. Offline, novelty is not a conclusion this can reach."""
        return False

    def to_dict(self) -> dict[str, Any]:
        return {
            "candidate_id": self.candidate_id,
            "outcome": self.outcome.value,
            "label": self.label,
            "references": list(self.references),
            "literature": self.literature.to_dict(),
            "fact_match": self.fact_match.to_dict() if self.fact_match else None,
            "identification": (
                self.identification.to_dict() if self.identification else None
            ),
            "verdict": self.verdict.to_dict() if self.verdict else None,
            "notes": list(self.notes),
            "establishes_novelty": False,
        }


def _utc_now() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


def _earned(verdict: Verdict) -> Verdict:
    """Return ``verdict`` if it already earns its status, else raise.

    :func:`screen_known` documents that the verdict it hands back satisfies
    :func:`~ontology.schema.verdict_reasons`, and the funnel relies on that: a
    detector returning an unearned verdict aborts the whole run. Checking it
    here turns any such bug into a :class:`KnownnessError` raised at the line
    that built the verdict, rather than a ``FunnelError`` three layers away.
    """
    reasons = verdict_reasons(verdict)
    if reasons:
        raise KnownnessError(
            f"this module built an unearned {verdict.status.value!r} verdict: "
            + "; ".join(reasons)
        )
    return verdict


def screen_known(
    candidate: Candidate,
    *,
    facts: KnownFactRegistry | None = None,
    literature: LiteratureBackend | None = None,
    value_provider: Callable[[int], Any] | None = None,
    identify: bool = True,
    decided_by: str = "ontology.knownness.screen_known",
    **identify_kwargs: Any,
) -> KnownnessReport:
    """The already-known gate: catalogue, then closed form, then literature.

    Order matters. The catalogue is cheap and citable, so it runs first; the
    integer-relation search is expensive and only applies to ``constant``
    candidates; the literature check runs last and, offline, concludes nothing.

    The returned ``verdict`` is a ``schema.Verdict`` that already satisfies
    ``schema.verdict_reasons`` when the outcome is ``KNOWN`` — the funnel can
    attach it directly. When the outcome is
    :attr:`Knownness.NOT_RECOGNISED_OFFLINE` the verdict is ``None``: *not
    recognised* is not a verdict, and manufacturing one here would be exactly the
    accounting error this package exists to prevent.
    """
    registry = facts if facts is not None else KNOWN_FACTS
    notes: list[str] = []

    hit = registry.match(candidate)
    if hit is not None:
        evidence: dict[str, Any] = {
            "references": [hit.source],
            "match_kind": hit.match_kind,
            "entry_id": hit.fact_id,
            "canonical_form": hit.canonical_form,
        }
        evidence.update(dict(hit.detail))
        verdict = Verdict(
            status=VerdictStatus.KNOWN,
            decided_by=decided_by,
            decided_by_version=KNOWNNESS_VERSION,
            decided_at=_utc_now(),
            evidence=evidence,
            notes=f"catalogued: {hit.statement}",
        )
        return KnownnessReport(
            candidate_id=candidate.id,
            outcome=Knownness.KNOWN,
            label=funnel_label("known-catalogued"),
            references=(hit.source,),
            literature=check_literature(candidate, literature),
            fact_match=hit,
            verdict=_earned(verdict),
            notes=tuple(notes),
        )

    report: IdentificationReport | None = None
    if identify and candidate.kind is CandidateKind.CONSTANT:
        kwargs = dict(identify_kwargs)
        if value_provider is None and "known_digits" not in kwargs:
            # Two ceilings, and the honest one is the lower: the digits the error
            # bound determines, and the digits the literal actually spells out.
            determined = _determined_digits(
                candidate.claim.get("value"), candidate.evidence.get("uncertainty")
            )
            written = _available_digits(candidate.claim.get("value"), None)
            if determined:
                kwargs["known_digits"] = max(1, min(determined, written))
        report = identify_constant(
            candidate.claim.get("value"), provider=value_provider, **kwargs
        )
        notes.append(f"closed-form search: {report.reason}")
        if report.identified and report.match is not None:
            match = report.match
            references = (
                f"closed-form: {match.expression}",
                f"engine: mpmath.pslq over {{{', '.join(n for _, n in match.terms if n != '1')}}}",
            )
            verdict = Verdict(
                status=VerdictStatus.KNOWN,
                decided_by=decided_by,
                decided_by_version=KNOWNNESS_VERSION,
                decided_at=_utc_now(),
                evidence={
                    "references": list(references),
                    "match_kind": "identity",
                    "expression": match.expression,
                    "defect": match.defect,
                    "digits_confirmed": match.digits_confirmed,
                    "escalated_digits": match.escalated_digits,
                    "surplus_digits": match.surplus_digits,
                    "cross_check": match.cross_check,
                },
                notes=(
                    "a closed form is a recognisable expression, not a citation: "
                    "the value is known, the significance is not."
                ),
            )
            return KnownnessReport(
                candidate_id=candidate.id,
                outcome=Knownness.KNOWN,
                label=funnel_label("known-closed-form"),
                references=references,
                literature=check_literature(candidate, literature),
                identification=report,
                verdict=_earned(verdict),
                notes=tuple(notes),
            )

    result = check_literature(candidate, literature)
    if result.status is LiteratureStatus.FOUND:
        verdict = Verdict(
            status=VerdictStatus.KNOWN,
            decided_by=decided_by,
            decided_by_version=KNOWNNESS_VERSION,
            decided_at=_utc_now(),
            evidence={
                "references": list(result.references),
                "match_kind": "statement",
                "backend": result.backend,
            },
        )
        return KnownnessReport(
            candidate_id=candidate.id,
            outcome=Knownness.KNOWN,
            label=funnel_label("known-literature"),
            references=result.references,
            literature=result,
            identification=report,
            verdict=_earned(verdict),
            notes=tuple(notes),
        )

    notes.append(
        "not recognised offline. This is the absence of a match, not the "
        "presence of novelty: the literature was not searched."
    )
    return KnownnessReport(
        candidate_id=candidate.id,
        outcome=Knownness.NOT_RECOGNISED_OFFLINE,
        label=funnel_label(result.label),
        references=(),
        literature=result,
        identification=report,
        verdict=None,
        notes=tuple(notes),
    )


def _determined_digits(value: Any, uncertainty: Any) -> int:
    """Significant digits an error bound actually pins down (0 if it pins none)."""
    val, unc = _dec(value), _dec(uncertainty)
    if val is None or unc is None or unc <= 0 or val == 0:
        return 0
    ratio = abs(val) / unc
    if ratio <= 1:
        return 0
    return int(math.floor(ratio.log10()))
