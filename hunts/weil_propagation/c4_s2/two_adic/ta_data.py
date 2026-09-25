"""Local data at 2: Satake parameters, the tower s_k(2), and the refusal gate.

Mission kill-control 2: the T_S builder must refuse non-unitary local data.
The data at 2 are accepted in one of two forms and must pass every check:

* ``("satake", (alpha_1, ..., alpha_d))``: each |alpha_j| = 1;
* ``("tower", {k: s_k})``: s_k = Lambda(2^k) / log 2 for k = 1 .. K, with
  K >= d. The parameters are recovered by Newton's identities from
  s_1 .. s_d, checked for |alpha_j| = 1, and the recovered alphas must
  reproduce every given s_k (k = 1 .. K). The cheap necessary condition
  |s_k| <= d is checked first and named separately.

Why unitarity is the gate (theory RESULTS s7.1 part (2)): the construction
T_S(g) = Tr(theta(g) Pi_S theta(g)^*) uses the local data only through the
factor Theta_alpha = 1 - alpha 2^{-1/2} D of CCM arXiv:2310.18423 (57), with
D the dilation by 2. For |alpha| = 1 the Weil distribution at 2 is the trace
of a unitary representation and the trace term is a diagonal (hence
nonnegative) quantity. For |alpha| != 1 (W_a has alpha = 2^{+-1/4}) the Weil
form is a pairing of two different vectors (theory s4 C2), so a nonnegative
trace term would not be a term of that form at all. Refusal is therefore a
correctness condition, not a numerical guard.

Tolerances: exact inputs (int, Fraction, sympy Rational or algebraic) are
checked exactly. Float or mpmath inputs are checked with ``tol`` and the
tolerance used is returned in the report, so a caller can see it.
"""

from __future__ import annotations

from fractions import Fraction

import sympy

__all__ = [
    "NonUnitaryLocalData",
    "LocalData",
    "validate",
    "ZETA",
    "DEDEKIND_Q_SQRT_M23",
    "W_A_QUARTER",
    "EPSTEIN_116_TOWER",
]


class NonUnitaryLocalData(ValueError):
    """Raised when the local data at 2 are not unitary Satake data."""


class LocalData:
    """Validated unitary Satake parameters at 2 (exact sympy numbers)."""

    def __init__(self, alphas, source: str, checks: list[str]):
        self.alphas = tuple(alphas)
        self.degree = len(self.alphas)
        self.source = source
        self.checks = checks

    def complex_alphas(self, dps: int = 40):
        from mpmath import mp

        with mp.workdps(dps):
            return [mp.mpc(complex(sympy.N(a, dps + 10))) for a in self.alphas]

    def __repr__(self) -> str:  # pragma: no cover
        return f"LocalData(alphas={self.alphas}, source={self.source!r})"


def _exact(x) -> sympy.Expr:
    if isinstance(x, Fraction):
        return sympy.Rational(x.numerator, x.denominator)
    return sympy.sympify(x)


def _abs_is_one(a: sympy.Expr, tol) -> bool:
    if tol is None:
        return sympy.simplify(sympy.Abs(a) - 1) == 0
    return abs(abs(complex(sympy.N(a, 30))) - 1.0) <= tol


def _roots_from_power_sums(s: list[sympy.Expr], d: int) -> list[sympy.Expr]:
    """Newton's identities: power sums s_1..s_d -> roots of the monic poly."""
    e = [sympy.Integer(1)]
    for k in range(1, d + 1):
        acc = sum((-1) ** (i - 1) * e[k - i] * s[i - 1] for i in range(1, k + 1))
        e.append(sympy.nsimplify(acc / k) if not acc.free_symbols else acc / k)
    x = sympy.Symbol("x")
    poly = sum((-1) ** k * e[k] * x ** (d - k) for k in range(d + 1))
    roots = sympy.roots(sympy.Poly(sympy.expand(poly), x))
    out = []
    for r, mult in roots.items():
        out.extend([sympy.simplify(r)] * mult)
    if len(out) != d:
        raise NonUnitaryLocalData(f"could not recover {d} Satake parameters from the tower")
    return out


def validate(data, degree: int | None = None, tol=None) -> LocalData:
    """Return LocalData for unitary data at 2, or raise NonUnitaryLocalData.

    ``data`` is ("satake", alphas) or ("tower", {k: s_k}); a bare tuple or
    list is read as Satake parameters. ``degree`` is required for a tower.
    """
    if isinstance(data, (tuple, list)) and data and data[0] in ("satake", "tower"):
        kind, payload = data
    else:
        kind, payload = "satake", data
    checks: list[str] = []
    if kind == "satake":
        alphas = [_exact(a) if tol is None else a for a in payload]
        if not alphas:
            raise NonUnitaryLocalData("empty Satake data")
        for j, a in enumerate(alphas):
            if not _abs_is_one(_exact(a) if tol is None else sympy.sympify(a), tol):
                raise NonUnitaryLocalData(
                    f"Satake parameter alpha_{j + 1} = {a} has |alpha| != 1 (non-unitary)"
                )
        checks.append("|alpha_j| = 1 for every j" + ("" if tol is None else f" (tol {tol})"))
        return LocalData([_exact(a) for a in alphas], "satake", checks)
    if kind != "tower":
        raise ValueError(f"unknown local data kind {kind!r}")
    if degree is None:
        raise ValueError("a tower needs its degree d")
    tower = {int(k): _exact(v) for k, v in dict(payload).items()}
    K = max(tower)
    if sorted(tower) != list(range(1, K + 1)) or K < degree:
        raise ValueError(f"tower must give s_1 .. s_K with K >= d = {degree}")
    for k in range(1, K + 1):
        if sympy.Abs(tower[k]) > degree:
            raise NonUnitaryLocalData(
                f"|s_{k}(2)| = {tower[k]} > d = {degree}: no unitary Satake parameters "
                f"(necessary condition |s_k| <= d fails at n = 2^{k} = {2 ** k})"
            )
    checks.append(f"|s_k| <= d for k = 1..{K}")
    alphas = _roots_from_power_sums([tower[k] for k in range(1, degree + 1)], degree)
    for j, a in enumerate(alphas):
        if not _abs_is_one(a, tol):
            raise NonUnitaryLocalData(
                f"recovered Satake parameter {a} has |alpha| != 1 (non-unitary)"
            )
    checks.append("recovered alphas have |alpha| = 1")
    for k in range(1, K + 1):
        pk = sympy.simplify(sum(a**k for a in alphas) - tower[k])
        if pk != 0:
            raise NonUnitaryLocalData(
                f"tower is not a power-sum tower of {degree} unitary parameters: "
                f"alphas {alphas} give s_{k} = {sympy.simplify(sum(a**k for a in alphas))}, "
                f"data say {tower[k]}"
            )
    checks.append(f"alphas reproduce s_k for k = 1..{K}")
    return LocalData(alphas, "tower", checks)


#: zeta: degree 1, alpha = 1.
ZETA = ("satake", (1,))
#: Dedekind zeta of Q(sqrt(-23)): 2 splits (-23 = 1 mod 8), alpha = (1, 1).
DEDEKIND_Q_SQRT_M23 = ("satake", (1, 1))
#: W_a with a = 1/4: Lambda_W(n) = Lambda(n)(n^a + n^-a), so alpha = 2^{+-1/4}.
W_A_QUARTER = ("satake", (sympy.Integer(2) ** sympy.Rational(1, 4), sympy.Integer(2) ** sympy.Rational(-1, 4)))
#: Epstein (1,1,6) tower at 2, s_1..s_7, from numerics us_check.json (commit
#: 8449c29 on teal-sea/weil-propagation), exact rationals there.
EPSTEIN_116_TOWER = ("tower", {1: 0, 2: 2, 3: 6, 4: 2, 5: 0, 6: 2, 7: 0})
