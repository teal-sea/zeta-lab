"""Cross-checks of Wang arXiv:2609.07918 and Lamzouri arXiv:2609.02882.

Nothing here is a result. This file exists for three reasons:

1. **It re-derives Wang's Proposition 4.1 independently and checks it.**
   The closed form ``C_lambda = lambda/2 + (1/sqrt 2) cot(lambda/sqrt 2)`` is
   Wang's equation (4.2), published 2026-09-07. This hunt derived it before
   reading the paper, which makes it a cross-check of the paper and not a
   finding. See ``MISSION.md`` section 2.

2. **It pins the finding: Wang's curve is already in this tree.**
   ``hunts/frontier_map/frontier.py:zeta_H_closed`` computes the
   unconditional proportion as a function of bandwidth ``lambda``, from the
   source paper's eq. (7.4). It equals Wang's ``c(theta)`` to 1e-16 at every
   bandwidth, and crosses zero at Wang's ``theta_0``. The laboratory's
   bandwidth dial and Wang's short-interval exponent are the same number.
   ``MISSION.md`` section 3.

   Note: two different constants in this tree are both called ``c*``. The
   zeta one (kernel ``|alpha|``, ``1/c*_1 = 1.3274992963205884``) is Wang's.
   The ``xi'`` one in ``lean/ZetaLean/Pub1/Setting.lean`` (kernel ``F_1``,
   ``H* = 0.8686415005``) is a different object and is not Wang's. An earlier
   draft of this file conflated them.

3. **It records the bridge diagnostic**, that the lab's two affine bridges
   carry a fixed overhead which does not shrink with their input, which is one
   of the two independent reasons the naive transplant fails.
   ``MISSION.md`` section 3.

House rule: run with the repository virtualenv.

    .venv/bin/python hunts/short_interval/verify.py

Deliberately stdlib only, no numpy and no mpmath, so it also runs in a bare
container during triage. Double precision is ample: every claim below is
checked to 1e-12 or looser, and nothing here enters an inequality that would
need an enclosure.
"""

from __future__ import annotations

from math import cos, sin, sqrt, tan

# ---------------------------------------------------------------------------
# The two papers' constants
# ---------------------------------------------------------------------------


def C(lam: float) -> float:
    """Wang (4.2): the minimum of his functional over the window of length lam.

    Equals ``1/c*(lam)`` for the laboratory's window operator. At ``lam = 1``
    this is the Montgomery-Taylor constant ``C_MT``.
    """
    return lam / 2 + (1 / sqrt(2)) / tan(lam / sqrt(2))


def c_simple(theta: float) -> float:
    """Wang Theorem 1.1 (1.7): simple-and-on-line proportion, ``2 - C_theta``."""
    return 2 - C(theta)


def d_distinct(theta: float) -> float:
    """Wang Theorem 1.1 (1.8): distinct-zero proportion, ``(1 + c)/2``."""
    return (1 + c_simple(theta)) / 2


def c_prime(theta: float) -> float:
    """Wang's stated derivative: ``c'(theta) = (1/2) cot^2(theta/sqrt 2)``."""
    return 0.5 / tan(theta / sqrt(2)) ** 2


# ---------------------------------------------------------------------------
# Route A: the closed form, derived from the integral equation
# ---------------------------------------------------------------------------


def C_from_extremal(lam: float) -> float:
    """``C_lambda`` via Wang's extremal function, assembled independently.

    Wang's Euler-Lagrange condition is ``f(u) + int_J |u-v| f(v) dv = const``
    on ``J = [-lam/2, lam/2]``, whose differentiated form is ``f'' + 2f = 0``.
    So ``f = A cos(sqrt 2 u)``, and imposing ``int_J f = 1`` fixes ``A``. The
    constant value of the left side is then ``C_lambda``.

    With ``s = lam/sqrt 2``: ``int_J cos(sqrt 2 u) du = sqrt 2 sin(s)``, so
    ``A = 1/(sqrt 2 sin s)``, which is Wang's (4.1). Evaluating the condition
    at the right endpoint, where the first moment of a symmetric ``f`` drops
    out, gives ``C = f(lam/2) + lam/2``.
    """
    s = lam / sqrt(2)
    A = 1 / (sqrt(2) * sin(s))
    return A * cos(s) + lam / 2


# ---------------------------------------------------------------------------
# Route B: an independent numerical solve, sharing no algebra with Route A
# ---------------------------------------------------------------------------


def _solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    """Gaussian elimination with partial pivoting. Stdlib substitute for numpy."""
    n = len(rhs)
    aug = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(aug[r][col]))
        aug[col], aug[piv] = aug[piv], aug[col]
        inv = 1.0 / aug[col][col]
        pivot_row = aug[col]
        for r in range(col + 1, n):
            factor = aug[r][col] * inv
            if factor:
                row = aug[r]
                for k in range(col, n + 1):
                    row[k] -= factor * pivot_row[k]
    out = [0.0] * n
    for r in range(n - 1, -1, -1):
        acc = aug[r][n] - sum(aug[r][k] * out[k] for k in range(r + 1, n))
        out[r] = acc / aug[r][r]
    return out


def C_from_solve(lam: float, n: int = 250) -> float:
    """``C_lambda`` as ``1/<1, w>`` with ``(I + T) w = 1``, kernel ``|u - v|``.

    Midpoint Nystrom discretization. This is the Rayleigh-quotient form:
    minimizing ``<A f, f>`` subject to ``<1, f> = 1`` gives
    ``1/<1, A^-1 1>``, so this route never forms the extremal function and
    never uses a trigonometric identity. Error is ``O(h^2)``.
    """
    h = lam / n
    nodes = [(i + 0.5) * h - lam / 2 for i in range(n)]
    matrix = [
        [(1.0 if i == j else 0.0) + h * abs(nodes[i] - nodes[j]) for j in range(n)]
        for i in range(n)
    ]
    w = _solve(matrix, [1.0] * n)
    return 1.0 / (h * sum(w))


# ---------------------------------------------------------------------------
# The laboratory's affine bridges, exact rationals
# ---------------------------------------------------------------------------

#: Palomar PALOMAR-2026-08-25-000005, three- and four-point instances.
#: Both unconditional, both affine in their analytic input.
BRIDGES = {
    "Phi_3": (149000000, -99200, 148800133),
    "Phi_4": (906250, -1085, 904171),
}


def bridge(name: str, h: float) -> float:
    num, shift, den = BRIDGES[name]
    return (num * h + shift) / den


def lab_landscape(lam: float) -> float:
    """``hunts/frontier_map/frontier.py:zeta_H_closed``, copied verbatim.

    The source paper's eq. (7.4): the unconditional proportion as a function
    of bandwidth, with ``c*_lambda = sqrt 2 tan(t)/(1 + t tan(t))``,
    ``t = lambda/sqrt 2``. Copied rather than imported because that module
    imports ``xiprime`` and therefore numpy, which this file avoids so it can
    run during triage in a bare container. A test that the copy still matches
    its source belongs in this hunt's own tests if the hunt grows any.
    """
    t = lam / sqrt(2.0)
    tan_t = tan(t)
    c = sqrt(2.0) * tan_t / (1.0 + t * tan_t)
    return 2.0 - 1.0 / c


def _bisect(f, lo: float, hi: float, iters: int = 200) -> float:
    sign_lo = f(lo) < 0
    for _ in range(iters):
        mid = (lo + hi) / 2
        if (f(mid) < 0) == sign_lo:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


# ---------------------------------------------------------------------------

#: Values as printed in the two papers. Any drift here is a reading error in
#: this file or a change in the source, and either way wants investigating.
PAPER_VALUES = {
    "C_MT = C(1), Lamzouri (3.1)": (1.3274992963206, C(1.0), 1e-12),
    "c(1-) global simple, Lamzouri (1.1)": (0.6725007036794116, c_simple(1.0), 1e-15),
    "d(1-) global distinct, Lamzouri Thm 1.1": (0.8362503518397058, d_distinct(1.0), 1e-15),
    "c(3/4), Wang section 1": (0.41907501297542415, c_simple(0.75), 1e-15),
    "d(3/4), Wang section 1": (0.7095375064877121, d_distinct(0.75), 1e-15),
}

#: The two thresholds Wang prints to fifteen places.
PAPER_ROOTS = {
    "theta_0, zero of c in (0,1)": (0.550193964744154, c_simple),
    "theta_d, zero of d in (0,1)": (0.346658926139761, d_distinct),
}


def main() -> None:
    failures: list[str] = []

    print("1. Wang's printed constants, recomputed from his closed form")
    print()
    for label, (printed, got, tol) in PAPER_VALUES.items():
        ok = abs(printed - got) <= tol
        failures += [] if ok else [label]
        print(f"   {'ok ' if ok else 'BAD'}  {label}")
        print(f"        paper {printed!r}")
        print(f"        here  {got!r}")

    print()
    print("2. The two thresholds, by bisection")
    print()
    for label, (printed, fn) in PAPER_ROOTS.items():
        root = _bisect(fn, 0.2, 0.99)
        ok = abs(printed - root) <= 1e-13
        failures += [] if ok else [label]
        print(f"   {'ok ' if ok else 'BAD'}  {label}: paper {printed!r}, here {root!r}")

    print()
    print("3. Two independent routes to C_lambda, and Wang's closed form")
    print()
    print("   lambda   Nystrom solve      extremal function   Wang (4.2)         |solve - Wang|")
    for lam in (0.55, 0.60, 0.70, 0.80, 0.90, 1.00):
        solved = C_from_solve(lam)
        extremal = C_from_extremal(lam)
        closed = C(lam)
        # the extremal route is exact; the solve carries O(h^2)
        ok = abs(extremal - closed) <= 1e-12 and abs(solved - closed) <= 2e-5
        failures += [] if ok else [f"C({lam})"]
        print(
            f"   {lam:5.2f}    {solved:.12f}     {extremal:.12f}      "
            f"{closed:.12f}     {abs(solved - closed):.2e}"
        )

    print()
    print("4. Monotonicity: Wang's c'(theta) against a difference quotient")
    print()
    for theta in (0.6, 0.8, 1.0):
        h = 1e-6
        numeric = (c_simple(theta + h) - c_simple(theta - h)) / (2 * h)
        stated = c_prime(theta)
        ok = abs(numeric - stated) <= 1e-6 * max(1.0, abs(stated))
        failures += [] if ok else [f"c'({theta})"]
        print(f"   {'ok ' if ok else 'BAD'}  theta {theta}: stated {stated:.12f}, numeric {numeric:.12f}")

    print()
    print("5. Bridge diagnostic. NOT a bound in a short interval: the bridges")
    print("   read band width 1 and Wang's theorem supplies band width theta.")
    print("   This only shows the fixed overhead does not shrink with the input.")
    print()
    for name in BRIDGES:
        slope = bridge(name, 1.0) - bridge(name, 0.0)
        intercept = bridge(name, 0.0)
        breakeven = -intercept / (slope - 1)
        theta_be = _bisect(lambda t: c_simple(t) - breakeven, 0.56, 0.999)
        print(
            f"   {name}: slope {slope:.9f}  intercept {intercept:+.9f}  "
            f"overhead cancels at input {breakeven:.6f} (c(theta) there: theta {theta_be:.6f})"
        )
    print()
    print(f"   at the full-range input: Phi_3 {bridge('Phi_3', c_simple(1.0)):.10f}, "
          f"Phi_4 {bridge('Phi_4', c_simple(1.0)):.10f}")

    print()
    print("6. THE FINDING: this tree's bandwidth landscape against Wang's curve")
    print("   hunts/frontier_map/frontier.py:zeta_H_closed, source paper eq. (7.4)")
    print()
    print("   lambda    frontier.py           Wang c(theta)         difference")
    for lam in (0.50, 0.60, 0.75, 0.90, 1.00):
        lab = lab_landscape(lam)
        wang = c_simple(lam)
        ok = abs(lab - wang) <= 1e-14
        failures += [] if ok else [f"landscape({lam})"]
        print(f"   {lam:6.4f}    {lab:.15f}   {wang:.15f}   {abs(lab - wang):.2e}")
    crossing = _bisect(lab_landscape, 0.3, 0.99)
    ok = abs(crossing - 0.550193964744154) <= 1e-13
    failures += [] if ok else ["landscape zero crossing"]
    print()
    print(f"   {'ok ' if ok else 'BAD'}  lab curve crosses zero at {crossing!r}")
    print(f"        Wang's printed theta_0  0.550193964744154")
    print(f"        the source paper states only 'empty for lambda <= 1/2';")
    print(f"        at lambda = 1/2 the curve is {lab_landscape(0.5):.12f}")

    print()
    if failures:
        raise SystemExit(f"FAILED: {failures}")
    print("all cross-checks passed")


if __name__ == "__main__":
    main()
