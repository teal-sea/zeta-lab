"""Independent position-space route to the sine-Gram moments.

This module shares NO machinery with `exact_moments.py`.  That one works on
the circle through the CUE Toeplitz representation and Wick pairing of the
power traces.  This one works directly on the line with the determinantal
correlation functions of the sine process:

    rho_b(y_1..y_b) = det[ S(y_i - y_j) ]_{b x b},    S(x) = sin(pi x)/(pi x).

Expanding tr G^k over the coincidence pattern of the k summation indices gives
a sum over set partitions of the cyclic word 1..k.  A block-diagonal edge is a
self loop and contributes K(0) = lambda; the remaining edges form a multigraph
on the blocks.  Each term is therefore a translation-invariant integral of a
product of functions of differences over a multigraph, which Fourier transforms
into an integral over the cycle space of the graph:

    integral over R^{b-1} of prod_e f_e(y_{u(e)} - y_{v(e)}) dy
        = integral over the cycle space of prod_e fhat_e(flow_e).

Every f_e here is a convolution power of the indicator of [-1/2, 1/2] (for S)
or of [-lambda/2, lambda/2] (for K_lambda), so fhat_e is a B-spline / Irwin-Hall
density and the whole integral is a piecewise-polynomial integral over a
polytope.  Parallel edges merge by convolution, i.e. by adding multiplicities,
and every factor is even so orientations do not matter.

The routine `connected_term` computes the fully connected (all-singleton)
contribution, which for k = 4 is the term this campaign needed to decide.
"""

from __future__ import annotations

import itertools

import numpy as np
from scipy import integrate


def bspline(order: int, x: np.ndarray, width: float = 1.0) -> np.ndarray:
    """Density of the sum of `order` uniforms on [-width/2, width/2].

    This is the Fourier transform of S^order (width 1) or of K_lambda^order
    (width lambda), by the convolution theorem.
    """
    if order == 0:
        raise ValueError("order must be >= 1")
    # Explicit Irwin-Hall density, shifted to be centred at 0.
    n = order
    t = np.asarray(x, dtype=float) / width + n / 2.0        # shift to [0, n]
    out = np.zeros_like(t)
    inside = (t >= 0) & (t <= n)
    tt = t[inside]
    acc = np.zeros_like(tt)
    for j in range(0, n + 1):
        term = (-1.0) ** j * _binom(n, j) * np.maximum(tt - j, 0.0) ** (n - 1)
        acc += term
    out[inside] = acc / _factorial(n - 1)
    return out / width


def _binom(n: int, k: int) -> float:
    from math import comb
    return float(comb(n, k))


def _factorial(n: int) -> float:
    from math import factorial
    return float(factorial(n))


def cycle_basis(n_vertices: int, edges: list[tuple[int, int]]):
    """Fundamental cycle matrix: rows = edges, columns = independent cycles.

    Built from a spanning tree, so the basis is unimodular and the flow
    coordinates carry Lebesgue measure with unit Jacobian.
    """
    parent = list(range(n_vertices))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    tree, extra = [], []
    for idx, (u, v) in enumerate(edges):
        ru, rv = find(u), find(v)
        if ru != rv:
            parent[ru] = rv
            tree.append(idx)
        else:
            extra.append(idx)

    adj: dict[int, list[tuple[int, int]]] = {v: [] for v in range(n_vertices)}
    for idx in tree:
        u, v = edges[idx]
        adj[u].append((v, idx))
        adj[v].append((u, idx))

    def tree_path(src, dst):
        """Signed edge list of the tree path src -> dst."""
        stack, seen = [(src, [])], {src}
        while stack:
            node, path = stack.pop()
            if node == dst:
                return path
            for nxt, idx in adj[node]:
                if nxt not in seen:
                    seen.add(nxt)
                    u, v = edges[idx]
                    sign = 1 if (u == node and v == nxt) else -1
                    stack.append((nxt, path + [(idx, sign)]))
        raise RuntimeError("spanning tree is disconnected")

    basis = np.zeros((len(edges), len(extra)))
    for col, idx in enumerate(extra):
        u, v = edges[idx]
        basis[idx, col] = 1.0
        for eidx, sign in tree_path(v, u):
            basis[eidx, col] = sign
    return basis


def graph_integral(n_vertices: int, edge_mult: dict[tuple[int, int], int],
                   widths: dict[tuple[int, int], float] | None = None,
                   limit: int = 200) -> float:
    """Cycle-space integral of the product of B-splines over a multigraph."""
    edges = sorted(edge_mult)
    mults = [edge_mult[e] for e in edges]
    wid = [1.0 if widths is None else widths.get(e, 1.0) for e in edges]
    basis = cycle_basis(n_vertices, edges)
    rank = basis.shape[1]
    if rank == 0:
        val = 1.0
        for m, w in zip(mults, wid):
            val *= float(bspline(m, np.array([0.0]), w)[0])
        return val

    def integrand(*z):
        flows = basis @ np.array(z)
        val = 1.0
        for f, m, w in zip(flows, mults, wid):
            b = float(bspline(m, np.array([f]), w)[0])
            if b == 0.0:
                return 0.0
            val *= b
        return val

    # each flow coordinate is bounded by the widest edge it traverses
    span = [sum(m * w for m, w in zip(mults, wid)) / 2.0] * rank
    ranges = [(-s, s) for s in span]
    val, _err = integrate.nquad(
        integrand, ranges, opts={"limit": limit, "epsabs": 1e-11, "epsrel": 1e-11}
    )
    return val


def connected_term(k: int) -> float:
    """The all-singleton (fully connected) contribution to m_k(1).

    The k summation indices are distinct points y_1..y_k; the K-edges form the
    k-cycle, and det[S] expands over permutations sigma of the k points.
    """
    total = 0.0
    for sigma in itertools.permutations(range(k)):
        sign = _perm_sign(sigma)
        mult: dict[tuple[int, int], int] = {}
        for i in range(k):                      # the K-cycle
            e = (min(i, (i + 1) % k), max(i, (i + 1) % k))
            mult[e] = mult.get(e, 0) + 1
        for i in range(k):                      # the permutation edges
            j = sigma[i]
            if i == j:
                continue
            e = (min(i, j), max(i, j))
            mult[e] = mult.get(e, 0) + 1
        total += sign * graph_integral(k, mult)
    return total


def _perm_sign(sigma: tuple[int, ...]) -> int:
    seen = [False] * len(sigma)
    sign = 1
    for i in range(len(sigma)):
        if seen[i]:
            continue
        length, j = 0, i
        while not seen[j]:
            seen[j] = True
            j = sigma[j]
            length += 1
        if length % 2 == 0:
            sign = -sign
    return sign


if __name__ == "__main__":
    from fractions import Fraction
    for k in (3, 4):
        val = connected_term(k)
        fr = Fraction(val).limit_denominator(2000)
        print(f"all-distinct term for k={k} (lambda=1) = {val:.12f}   ~ {fr}")
    print()
    print("NOTE: the decisive m_4 computation lives in exact_finite_N.py,")
    print("which needs no Wick approximation and no quadrature.  This module")
    print("is retained as an independent check on individual graph integrals.")
