"""checker/: the seam to kernel/ and two_adic/.

Phase 1 (this commit): nothing is routed. Every loader raises ``NotRouted``
and the provider tests skip with that literal reason. No stand-in T_S exists
anywhere in checker/: a passing stand-in would read as a result.

Phase 2 replaces the bodies below with calls into the routed modules. Only
this call glue may change after routing; the properties the tests assert may
not (checker BRIEF, independence rule).

Expected shapes (mission interface contract): Hermitian (2N+1) x (2N+1)
mpmath matrices on U_n, n = -N..N, index 0 is n = -N, F(f) = v^* M v.
"""

from __future__ import annotations


class NotRouted(RuntimeError):
    """kernel/ or two_adic/ output has not been routed to checker/ yet."""


def T_inf(c, N: int, dps: int = 40):
    """kernel/: the S = {inf} trace term T_inf(c, N, dps)."""
    raise NotRouted("kernel/ T_inf not routed to checker/ yet")


def T_S(c, N: int, dps: int = 40):
    """two_adic/: T_S for S = {inf, 2}, zeta's data, product-ball cutoff."""
    raise NotRouted("two_adic/ T_S not routed to checker/ yet")


def T_S_places(c, N: int, dps: int = 40, places=("inf", 2)):
    """two_adic/: the builder with an explicit set of places (P6 uses
    places=("inf",)). Raises NotRouted, or NotExposed if the builder has no
    such path."""
    raise NotRouted("two_adic/ builder not routed to checker/ yet")


def T_S_with_data(c, N: int, dps: int, obj: str):
    """two_adic/: the builder fed the named object's data at 2 and its
    archimedean type (kill-controls 2 and 3). obj is a key of
    checker_gate.OBJECTS. Must raise Refused for W_a and Epstein (control 2)."""
    raise NotRouted("two_adic/ builder not routed to checker/ yet")


class NotExposed(RuntimeError):
    """The routed builder has no code path for the requested variant."""


class Refused(RuntimeError):
    """The routed builder refused the data (the provider's own refusal,
    translated here). Any other exception propagates and fails the test:
    a TypeError is not a refusal."""
