"""Exact squarefree cluster algebra for the frozen level-two resolvent.

Write ``A=Lambda``, ``B=Lambda log`` and

    D(z) = (1-z*A)^2 + z^2*B = 1-X(z),
    X(z) = 2*z*A-z^2*(A*A+B).

The inverse is treated without a coefficient-order cutoff.  Borel transform
in the Neumann order turns it into ``exp(t*X)``.  On squarefree support this
is a monomer-dimer model: singleton weights come from ``A`` and ``B``, and
the only non-singleton atom is the rank-one pair weight from ``A*A``.

The arithmetic object in the level-two logarithmic derivative is

    Q(z) = -A-mathcal_L(log_* D(z)),

where ``mathcal_L`` is the coefficient derivation
``f(n) -> log(n) f(n)`` and ``log_*`` is the convolution logarithm.  The Borel
representation below gives an exact matching formula for its squarefree
coefficients and an all-support-size majorant for their Hadamard square.

Everything in this module is finite algebra.  The prime-simplex asymptotic
and the powerful-support passage remain analytic inputs.
"""

from __future__ import annotations

from functools import lru_cache
from math import factorial
import sympy as sp


Edge = tuple[int, int]
Matching = tuple[Edge, ...]


@lru_cache(maxsize=None)
def matchings(vertices: tuple[int, ...]) -> tuple[Matching, ...]:
    """Return every matching on the supplied labelled vertices."""

    if not vertices:
        return ((),)
    first, *rest_list = vertices
    rest = tuple(rest_list)
    answer: list[Matching] = list(matchings(rest))
    for position, partner in enumerate(rest):
        remaining = rest[:position] + rest[position + 1 :]
        for following in matchings(remaining):
            answer.append(((first, partner),) + following)
    return tuple(answer)


def _matching_size_count(vertex_count: int, edge_count: int) -> int:
    if edge_count < 0 or 2 * edge_count > vertex_count:
        return 0
    return factorial(vertex_count) // (
        2**edge_count
        * factorial(edge_count)
        * factorial(vertex_count - 2 * edge_count)
    )


def inverse_series_terms(max_power: int) -> dict[int, dict[tuple[int, int], int]]:
    """Return the exact ``A^k B^j`` terms of ``D(z)^-1`` by z-power.

    A key ``(k,j)`` denotes ``A`` convolved ``k`` times and ``B`` convolved
    ``j`` times.  The coefficient is

        (-1)^j binomial(2j+k+1,k).
    """

    if max_power < 0:
        raise ValueError("max_power must be nonnegative")
    answer: dict[int, dict[tuple[int, int], int]] = {}
    for power in range(max_power + 1):
        layer: dict[tuple[int, int], int] = {}
        for j in range(power // 2 + 1):
            k = power - 2 * j
            layer[(k, j)] = (-1) ** j * int(sp.binomial(2 * j + k + 1, k))
        answer[power] = layer
    return answer


def squarefree_inverse_closed(logs: tuple[sp.Expr, ...], z: sp.Expr) -> sp.Expr:
    """Closed ``A^k B^j`` evaluation of the inverse on distinct primes."""

    size = len(logs)
    if size == 0:
        return sp.Integer(1)
    product = sp.prod(logs)
    answer = sp.Integer(0)
    for j in range(size + 1):
        e_j = sum(
            sp.prod(logs[index] for index in subset)
            for subset in _subsets_of_size(tuple(range(size)), j)
        )
        coefficient = (
            (-1) ** j
            * factorial(j)
            * factorial(size + j + 1)
            // factorial(2 * j + 1)
        )
        answer += coefficient * z ** (size + j) * product * e_j
    return sp.expand(answer)


def _subsets_of_size(values: tuple[int, ...], size: int) -> tuple[tuple[int, ...], ...]:
    if size == 0:
        return ((),)
    if size > len(values):
        return ()
    if not values:
        return ()
    first = values[0]
    tail = values[1:]
    with_first = tuple((first,) + item for item in _subsets_of_size(tail, size - 1))
    return with_first + _subsets_of_size(tail, size)


def squarefree_inverse_convolution(
    logs: tuple[sp.Expr, ...], z: sp.Expr
) -> sp.Expr:
    """Evaluate the inverse by subset-convolution recurrence."""

    size = len(logs)
    values: dict[int, sp.Expr] = {0: sp.Integer(1)}

    def denominator(mask: int) -> sp.Expr:
        indices = [index for index in range(size) if mask & (1 << index)]
        if len(indices) == 1:
            value = logs[indices[0]]
            return -2 * z * value + z**2 * value**2
        if len(indices) == 2:
            return 2 * z**2 * logs[indices[0]] * logs[indices[1]]
        return sp.Integer(0)

    for mask in range(1, 1 << size):
        subtotal = sp.Integer(0)
        submask = mask
        while submask:
            subtotal += denominator(submask) * values[mask ^ submask]
            submask = (submask - 1) & mask
        values[mask] = sp.expand(-subtotal)
    return values[(1 << size) - 1]


def borel_monomer(log_prime: sp.Expr, z: sp.Expr, t: sp.Expr) -> sp.Expr:
    """Singleton weight in ``exp(t*X)`` on squarefree support."""

    return t * z * log_prime * (2 - z * log_prime)


def borel_dimer(
    left_log: sp.Expr, right_log: sp.Expr, z: sp.Expr, t: sp.Expr
) -> sp.Expr:
    """The connected two-prime ``A*A`` weight in ``exp(t*X)``."""

    return -2 * t * z**2 * left_log * right_log


def prime_power_borel_local(
    exponent: int,
    log_prime: sp.Expr,
    z: sp.Expr,
    t: sp.Expr,
    eta: sp.Expr,
) -> sp.Expr:
    """Conditional coefficient at ``p^exponent`` in the Gaussian mixture.

    ``eta`` denotes ``i*sqrt(2t)*G``.  Before taking its Gaussian moments the
    local Euler series is

        exp((2tz+eta*z) log(p) u/(1-u)
            -t z^2 log(p)^2 u/(1-u)^2).
    """

    if exponent < 1:
        raise ValueError("exponent must be positive")
    u = sp.Symbol("u")
    local_exponent = sum(
        ((2 * t * z + eta * z) * log_prime - t * z**2 * power * log_prime**2)
        * u**power
        for power in range(1, exponent + 1)
    )
    return sp.expand(sp.exp(local_exponent).series(u, 0, exponent + 1).removeO().coeff(u, exponent))


def gaussian_eta_expectation(
    expression: sp.Expr, eta: sp.Symbol, t: sp.Expr
) -> sp.Expr:
    """Apply ``eta=i*sqrt(2t)*G`` moments to a polynomial."""

    polynomial = sp.Poly(sp.expand(expression), eta)
    answer = sp.Integer(0)
    for (power,), coefficient in polynomial.terms():
        if power % 2:
            continue
        half = power // 2
        moment = (
            (-1) ** half
            * t**half
            * sp.Rational(factorial(power), factorial(half))
        )
        answer += coefficient * moment
    return sp.expand(answer)


def _laplace_polynomial(expression: sp.Expr, t: sp.Symbol) -> sp.Expr:
    polynomial = sp.Poly(sp.expand(expression), t)
    answer = sp.Integer(0)
    for (power,), coefficient in polynomial.terms():
        if power < 0:
            raise ValueError("Laplace integrand must be polynomial")
        answer += coefficient * factorial(power)
    return sp.expand(answer)


def prime_power_inverse_cluster(
    exponent: int, log_prime: sp.Expr, z: sp.Expr
) -> sp.Expr:
    """Exact inverse coefficient at ``p^exponent`` from the Gaussian route."""

    t, eta = sp.symbols("t eta")
    conditional = prime_power_borel_local(exponent, log_prime, z, t, eta)
    averaged = gaussian_eta_expectation(conditional, eta, t)
    return _laplace_polynomial(averaged, t)


def prime_power_q_cluster(
    exponent: int, log_prime: sp.Expr, z: sp.Expr
) -> sp.Expr:
    """Exact ``Q(z)`` coefficient at ``p^exponent`` from the Gaussian route."""

    t, eta = sp.symbols("t eta")
    conditional = prime_power_borel_local(exponent, log_prime, z, t, eta)
    averaged = sp.cancel(gaussian_eta_expectation(conditional, eta, t) / t)
    return sp.expand(
        -log_prime + exponent * log_prime * _laplace_polynomial(averaged, t)
    )


def prime_power_q_direct(
    exponent: int, log_prime: sp.Expr, z: sp.Expr
) -> sp.Expr:
    """Direct local-series evaluation of ``-A-(log D)`` at ``p^exponent``."""

    if exponent < 1:
        raise ValueError("exponent must be positive")
    u = sp.Symbol("u")
    a_local = log_prime * sum(u**power for power in range(1, exponent + 1))
    b_local = log_prime**2 * sum(
        power * u**power for power in range(1, exponent + 1)
    )
    denominator = sp.expand((1 - z * a_local) ** 2 + z**2 * b_local)
    inverse = sp.series(1 / denominator, u, 0, exponent + 1).removeO()
    log_derivative = sum(
        power * log_prime * sp.expand(denominator).coeff(u, power) * u**power
        for power in range(1, exponent + 1)
    )
    q_series = -a_local - sp.expand(log_derivative * inverse)
    return sp.expand(q_series).coeff(u, exponent)


def borel_squarefree_coefficient(
    logs: tuple[sp.Expr, ...], z: sp.Expr, t: sp.Expr
) -> sp.Expr:
    """Return the monomer-dimer partition sum for ``exp(t*X)``."""

    answer = sp.Integer(0)
    vertices = tuple(range(len(logs)))
    for matching in matchings(vertices):
        covered = {vertex for edge in matching for vertex in edge}
        term = sp.prod(
            borel_dimer(logs[left], logs[right], z, t)
            for left, right in matching
        )
        term *= sp.prod(
            borel_monomer(logs[index], z, t)
            for index in vertices
            if index not in covered
        )
        answer += term
    return sp.expand(answer)


def squarefree_inverse_cluster(logs: tuple[sp.Expr, ...], z: sp.Expr) -> sp.Expr:
    """Laplace-integrate the Borel matching model exactly."""

    size = len(logs)
    if size == 0:
        return sp.Integer(1)
    answer = sp.Integer(0)
    product = sp.prod(logs)
    vertices = tuple(range(size))
    for matching in matchings(vertices):
        edge_count = len(matching)
        covered = {vertex for edge in matching for vertex in edge}
        answer += (
            factorial(size - edge_count)
            * (-2) ** edge_count
            * z**size
            * product
            * sp.prod(2 - z * logs[index] for index in vertices if index not in covered)
        )
    return sp.expand(answer)


def squarefree_q_cluster(logs: tuple[sp.Expr, ...], z: sp.Expr) -> sp.Expr:
    """Exact level-two ``Q(z)`` coefficient on distinct-prime support."""

    size = len(logs)
    if size == 0:
        return sp.Integer(0)
    product = sp.prod(logs)
    log_integer = sum(logs)
    vertices = tuple(range(size))
    answer = sp.Integer(0)
    for matching in matchings(vertices):
        edge_count = len(matching)
        covered = {vertex for edge in matching for vertex in edge}
        answer += (
            factorial(size - edge_count - 1)
            * (-2) ** edge_count
            * z**size
            * product
            * sp.prod(2 - z * logs[index] for index in vertices if index not in covered)
        )
    if size == 1:
        answer *= log_integer
        answer -= logs[0]
    else:
        answer *= log_integer
    return sp.expand(answer)


def pq_direct_resolvent(
    left_log: sp.Expr, right_log: sp.Expr, z: sp.Expr
) -> sp.Expr:
    """Coefficient at ``pq`` from direct inversion in the squarefree ring."""

    left = -2 * z * left_log + z**2 * left_log**2
    right = -2 * z * right_log + z**2 * right_log**2
    pair = 2 * z**2 * left_log * right_log
    return sp.expand(-pair + 2 * left * right)


def pq_connected_defect(
    left_log: sp.Expr, right_log: sp.Expr, z: sp.Expr
) -> sp.Expr:
    """Return ``b(pq)-b(p)b(q)`` for arbitrary distinct primes."""

    pair = pq_direct_resolvent(left_log, right_log, z)
    left = 2 * z * left_log - z**2 * left_log**2
    right = 2 * z * right_log - z**2 * right_log**2
    return sp.factor(pair - left * right)


def pq_borel_defect(
    left_log: sp.Expr, right_log: sp.Expr, z: sp.Expr, t: sp.Expr
) -> sp.Expr:
    """Return the new connected defect before the Laplace integral."""

    pair = borel_squarefree_coefficient((left_log, right_log), z, t)
    singles = borel_monomer(left_log, z, t) * borel_monomer(
        right_log, z, t
    )
    return sp.factor(pair - singles)


def _union_connected(size: int, first: Matching, second: Matching) -> bool:
    if size <= 1:
        return True
    adjacency = [set() for _ in range(size)]
    for left, right in first + second:
        adjacency[left].add(right)
        adjacency[right].add(left)
    seen = {0}
    frontier = [0]
    while frontier:
        vertex = frontier.pop()
        for following in adjacency[vertex]:
            if following not in seen:
                seen.add(following)
                frontier.append(following)
    return len(seen) == size


def connected_hadamard_weight_direct(
    logs: tuple[sp.Expr, ...], z: sp.Expr, t: sp.Expr, u: sp.Expr
) -> sp.Expr:
    """Sum pairs of matchings whose two-colour union is connected."""

    size = len(logs)
    vertices = tuple(range(size))

    def configuration(matching: Matching, parameter: sp.Expr) -> sp.Expr:
        covered = {vertex for edge in matching for vertex in edge}
        return sp.prod(
            borel_dimer(logs[left], logs[right], z, parameter)
            for left, right in matching
        ) * sp.prod(
            borel_monomer(logs[index], z, parameter)
            for index in vertices
            if index not in covered
        )

    answer = sp.Integer(0)
    all_matchings = matchings(vertices)
    for first in all_matchings:
        for second in all_matchings:
            if _union_connected(size, first, second):
                answer += configuration(first, t) * configuration(second, u)
    return sp.expand(answer)


def connected_hadamard_weight_closed(
    logs: tuple[sp.Expr, ...], z: sp.Expr, t: sp.Expr, u: sp.Expr
) -> sp.Expr:
    """Closed alternating-path/even-cycle connected component weight."""

    size = len(logs)
    if size == 0:
        return sp.Integer(0)
    measure = z ** (2 * size) * sp.prod(value**2 for value in logs)
    if size == 1:
        return sp.expand(t * u * measure * (2 - z * logs[0]) ** 2)

    endpoint_sum = sum(
        (2 - z * logs[left]) * (2 - z * logs[right])
        for left, right in _subsets_of_size(tuple(range(size)), 2)
    )
    if size % 2:
        path = (
            (-2) ** (size - 1)
            * 2
            * factorial(size - 2)
            * (t * u) ** ((size + 1) // 2)
            * measure
            * endpoint_sum
        )
        return sp.expand(path)

    path = (
        (-2) ** (size - 1)
        * factorial(size - 2)
        * (t * u) ** (size // 2)
        * (t + u)
        * measure
        * endpoint_sum
    )
    cycle = (
        2**size
        * factorial(size - 1)
        * (t * u) ** (size // 2)
        * measure
    )
    return sp.expand(path + cycle)


def full_squarefree_majorant_coefficient(size: int) -> sp.Rational:
    """Coefficient in the all-matching square-density support majorant.

    After a prime-simplex bound with constant ``D``, the contribution of
    support size ``r`` is bounded by

        x log(x) * c_r * (D*rho^2)^r,

    where ``rho=z log(x)`` and this function returns ``c_r``.  We retain the
    exact finite matching count instead of the simpler ``exp(r/4)`` bound.
    """

    if size < 1:
        raise ValueError("size must be positive")
    one_colour = sum(
        sp.Rational(
            _matching_size_count(size, edges)
            * factorial(size - edges - 1),
            2**edges,
        )
        for edges in range(size // 2 + 1)
    )
    return sp.Rational(4**size * one_colour**2, factorial(size) * factorial(2 * size - 1))


def majorant_ratios(limit: int = 20) -> tuple[sp.Rational, ...]:
    """Successive exact ratios of the support-size majorant coefficients."""

    if limit < 2:
        raise ValueError("limit must be at least two")
    coefficients = [full_squarefree_majorant_coefficient(size) for size in range(1, limit + 1)]
    return tuple(
        sp.factor(coefficients[index] / coefficients[index - 1])
        for index in range(1, len(coefficients))
    )


def rc2_parameter_margins() -> dict[str, sp.Rational]:
    """Exact margins for the first unoptimized level-two contour band."""

    alpha_0 = sp.Rational(1, 100)
    delta = sp.Rational(1, 2)
    beta = sp.Rational(11, 500)
    rho_0 = sp.Rational(1, 10)
    return {
        "target_rams": rho_0 - 2 * alpha_0 / delta,
        "upper_cutoff_rams": rho_0 - 2 * beta / delta,
        "tail_at_epsilon_zero": beta - 2 * alpha_0,
        "maximum_epsilon": (1 - 2 * alpha_0 / beta) / 2,
    }


def exact_route_defects(max_size: int = 5) -> tuple[sp.Expr, ...]:
    """Compare closed, recurrence, and cluster routes on symbolic primes."""

    if max_size < 1:
        raise ValueError("max_size must be positive")
    z = sp.Symbol("z")
    logs = tuple(sp.symbols(f"l1:{max_size + 1}"))
    defects: list[sp.Expr] = []
    for size in range(1, max_size + 1):
        current = logs[:size]
        closed = squarefree_inverse_closed(current, z)
        recurrence = squarefree_inverse_convolution(current, z)
        cluster = squarefree_inverse_cluster(current, z)
        defects.extend(
            (sp.expand(closed - recurrence), sp.expand(closed - cluster))
        )
    return tuple(defects)


def connected_component_defects(max_size: int = 6) -> tuple[sp.Expr, ...]:
    """Compare enumeration with the alternating path/cycle formula."""

    if max_size < 1:
        raise ValueError("max_size must be positive")
    z, t, u = sp.symbols("z t u")
    logs = tuple(sp.symbols(f"l1:{max_size + 1}"))
    return tuple(
        sp.expand(
            connected_hadamard_weight_direct(logs[:size], z, t, u)
            - connected_hadamard_weight_closed(logs[:size], z, t, u)
        )
        for size in range(1, max_size + 1)
    )


def audit() -> dict[str, object]:
    z, t, left, right = sp.symbols("z t lp lq")
    return {
        "inverse_route_defects": exact_route_defects(),
        "connected_component_defects": connected_component_defects(),
        "pq_inverse": pq_direct_resolvent(left, right, z),
        "pq_connected_defect": pq_connected_defect(left, right, z),
        "pq_borel_defect": pq_borel_defect(left, right, z, t),
        "majorant_coefficients": [
            full_squarefree_majorant_coefficient(size) for size in range(1, 13)
        ],
        "majorant_ratios": majorant_ratios(12),
        "rc2_parameter_margins": rc2_parameter_margins(),
    }


if __name__ == "__main__":
    for key, value in audit().items():
        print(f"{key}: {value}")
