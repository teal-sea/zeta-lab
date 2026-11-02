"""Horizontal visibility graphs (HVG) of real sequences.

Definition (Luque, Lacasa, Ballesteros and Luque, Phys. Rev. E 80, 046103, 2009): the
nodes are the indices of x_0, ..., x_{n-1}, and i < j are joined iff x_k < min(x_i, x_j)
for every i < k < j. Neighbours are always joined. An equal value blocks the view.

Exact facts used by the lab (proofs in lab/RESULTS.md, checked in lab/test_hvg.py):

* With +inf sentinels at both ends (equivalently, in a bi-infinite sequence whose every
  value is eventually exceeded on both sides), an interior node has degree 2 iff it is a
  strict local minimum. In a bare finite sequence this is FALSE: in (..., 5, 4, 3, 2, 1)
  the 5 sees only the 4, because nothing after the 4 is taller than it. The first version
  of this docstring stated the bare claim; lab/test_hvg.py refuted it on (2, 1, 0).
* For distinct values, the edge count is |E| = 2n - L - R, where L and R count the strict
  left-to-right and right-to-left maxima (records) of the sequence.
* For i.i.d. continuous data the bi-infinite degree law is P(k) = (1/3)(2/3)^(k-2), k >= 2,
  and the directed out-degree law is P(k) = 2^(-k), k >= 1 (Luque et al. 2009; Lacasa et
  al., Eur. Phys. J. B 85, 217, 2012).
"""
from __future__ import annotations

import numpy as np


def hvg_edges(x) -> np.ndarray:
    """Every HVG edge (i, j), i < j, as an (m, 2) int array, by the O(n) stack algorithm.

    The stack holds the indices that can still see to the right, in non-increasing order
    of value. A new value j joins every smaller stacked value (each is then blocked by j)
    and the first stacked value that is not smaller; an equal value is joined and then
    blocked, because x_j = x_i is not below min(x_i, x_j') for any later j'.
    """
    x = np.asarray(x, dtype=np.float64)
    if x.ndim != 1:
        raise ValueError("hvg_edges needs a one-dimensional sequence")
    if not np.all(np.isfinite(x)):
        raise ValueError("hvg_edges needs finite values")
    vals = x.tolist()
    edges: list[tuple[int, int]] = []
    stack: list[int] = []
    for j, v in enumerate(vals):
        while stack and vals[stack[-1]] < v:
            edges.append((stack.pop(), j))
        if stack:
            edges.append((stack[-1], j))
            if vals[stack[-1]] == v:
                stack.pop()
        stack.append(j)
    return np.asarray(edges, dtype=np.int64).reshape(-1, 2)


def hvg_edges_brute(x) -> np.ndarray:
    """The definition applied literally, O(n^3). For tests only."""
    x = [float(v) for v in x]
    n = len(x)
    out = [
        (i, j)
        for i in range(n)
        for j in range(i + 1, n)
        if all(x[k] < min(x[i], x[j]) for k in range(i + 1, j))
    ]
    return np.asarray(out, dtype=np.int64).reshape(-1, 2)


def degrees(x) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """(undirected, out, in) degree arrays. out[i] counts j > i joined to i, in[j] counts i < j."""
    n = len(x)
    e = hvg_edges(x)
    out = np.bincount(e[:, 0], minlength=n)
    inn = np.bincount(e[:, 1], minlength=n)
    return out + inn, out, inn


def records(x) -> tuple[int, int]:
    """(L, R): counts of strict left-to-right and right-to-left maxima."""
    x = np.asarray(x, dtype=np.float64)
    if x.size == 0:
        return 0, 0
    run_l = np.maximum.accumulate(x)
    left = 1 + int(np.count_nonzero(x[1:] > run_l[:-1]))
    xr = x[::-1]
    run_r = np.maximum.accumulate(xr)
    right = 1 + int(np.count_nonzero(xr[1:] > run_r[:-1]))
    return left, right


def iid_degree_law(k) -> np.ndarray:
    """P(k) = (1/3)(2/3)^(k-2) for k >= 2, else 0: the i.i.d. theorem."""
    k = np.asarray(k)
    return np.where(k >= 2, (1.0 / 3.0) * (2.0 / 3.0) ** (k - 2.0), 0.0)


def iid_out_degree_law(k) -> np.ndarray:
    """P(k_out = k) = 2^(-k) for k >= 1, else 0: the i.i.d. directed theorem."""
    k = np.asarray(k)
    return np.where(k >= 1, 0.5 ** k.astype(float), 0.0)


def degree_histogram(deg: np.ndarray, kmax: int) -> np.ndarray:
    """Counts c[k] for k = 0..kmax, with every degree above kmax pooled into c[kmax]."""
    return np.bincount(np.minimum(deg, kmax), minlength=kmax + 1)


def interior(deg: np.ndarray, trim: int) -> np.ndarray:
    """Drop `trim` nodes at each end: boundary nodes see only one way."""
    if trim <= 0:
        return deg
    if 2 * trim >= deg.size:
        raise ValueError("trim removes every node")
    return deg[trim:-trim]


def kl_divergence(p_counts: np.ndarray, q_counts: np.ndarray) -> float:
    """KL(p || q) in nats over the bins where both are positive.

    Bins where exactly one side is empty are reported by `kl_support_mismatch`, never
    silently dropped.
    """
    p = p_counts / p_counts.sum()
    q = q_counts / q_counts.sum()
    both = (p > 0) & (q > 0)
    return float(np.sum(p[both] * np.log(p[both] / q[both])))


def kl_support_mismatch(p_counts: np.ndarray, q_counts: np.ndarray) -> int:
    """Number of bins that are empty on exactly one side."""
    return int(np.count_nonzero((p_counts > 0) != (q_counts > 0)))
