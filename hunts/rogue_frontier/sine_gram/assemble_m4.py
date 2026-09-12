"""Full position-space assembly of m_k(1) = lim tr G^k / d for the sine process.

Independent of the Toeplitz/Wick engine in exact_moments.py: this route uses
only the determinantal correlation functions rho_b = det[S(x_i - x_j)] and
graph integrals evaluated in Fourier space (B-splines), via position_space.py.

Assembly.  tr G^k = sum over functions from the k cycle positions to points.
Group by the set partition P of the k positions (which positions coincide).
For a partition with blocks B_1..B_b (b distinct points):

    contribution = integral over configurations of b distinct points of
                   [ product of K over the k cycle edges, collapsed onto
                     the blocks ]  *  rho_b(y_1..y_b)

with rho_b = det[S(y_i - y_j)] = sum over permutations sigma of S_b of
sign(sigma) * product over non-fixed i of S(y_i - y_sigma(i)).

Every permutation term turns the integral into a multigraph integral: the
collapsed K-cycle edges plus one S-edge per non-fixed point of sigma
(a 2-cycle of sigma gives S^2 on that pair).  Self-loops K(0) = lambda = 1
contribute factor 1.  Each such integral is evaluated by graph_integral.

The b = 1 partition contributes 1.  Everything is at lambda = 1, so all
B-spline widths are 1.
"""

from __future__ import annotations

import itertools
from fractions import Fraction

from position_space import graph_integral, _perm_sign


def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for part in set_partitions(rest):
        for i in range(len(part)):
            yield part[:i] + [[first] + part[i]] + part[i + 1:]
        yield [[first]] + part


def m_k_position_space(k: int, verbose: bool = True) -> float:
    total = 0.0
    rows = []
    for part in set_partitions(list(range(k))):
        b = len(part)
        block_of = {}
        for bi, block in enumerate(part):
            for pos in block:
                block_of[pos] = bi
        # collapsed K-cycle edges (self-loops contribute K(0) = 1, drop them)
        base: dict[tuple[int, int], int] = {}
        for i in range(k):
            u, v = block_of[i], block_of[(i + 1) % k]
            if u == v:
                continue
            e = (min(u, v), max(u, v))
            base[e] = base.get(e, 0) + 1
        if b == 1:
            val = 1.0
            rows.append((part, val))
            total += val
            continue
        val = 0.0
        for sigma in itertools.permutations(range(b)):
            mult = dict(base)
            ok = True
            for i in range(b):
                j = sigma[i]
                if i == j:
                    continue
                e = (min(i, j), max(i, j))
                mult[e] = mult.get(e, 0) + 1
            if not mult:
                # empty graph: infinite volume; cannot happen because the
                # base cycle always connects at least two blocks when b >= 2
                raise RuntimeError("empty multigraph")
            # A disconnected multigraph integrates to +infinity * 0 issues;
            # here every term is connected through the K-cycle when sigma
            # only permutes within components joined by base edges.  If the
            # multigraph is disconnected the integral over the relative
            # coordinates of the components diverges -- but rho_b subtracts
            # these divergences; in the determinant expansion each
            # disconnected term must be dropped because its complement in
            # the inclusion-exclusion cancels the divergence.  Standard
            # cluster argument: only terms where sigma connects the
            # components of the base graph survive with finite total.  We
            # therefore require connectivity of base+sigma edges.
            if not _connected(b, mult):
                ok = False
            if not ok:
                continue
            val += _perm_sign(sigma) * graph_integral(b, mult)
        rows.append((part, val))
        total += val
    if verbose:
        for part, val in rows:
            print("  partition", part, "->", round(val, 10))
    return total


def _connected(n: int, edges: dict) -> bool:
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for (u, v) in edges:
        ru, rv = find(u), find(v)
        if ru != rv:
            parent[ru] = rv
    return len({find(i) for i in range(n)}) == 1


if __name__ == "__main__":
    import sys
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    val = m_k_position_space(k)
    fr = Fraction(val).limit_denominator(3000)
    print(f"m_{k}(1) [position space] = {val:.10f}  ~ {fr}")
    if k == 4:
        print("paper: 13/4 =", 13 / 4, "   wick engine: 49/15 =", 49 / 15)
