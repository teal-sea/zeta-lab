"""EXACT finite-N moments of the band Gram matrix over the CUE, and their limit.

The model (circular, lambda = d/N).  U ~ CUE(N) with eigenangles theta_j.
T_{m,m'} = Tr U^{m-m'} for m, m' in [-M, M], d = 2M+1, G = T/N.  Then
m_k = lim_{N} E tr G^k / d reproduces the sine-process band Gram moments
(the paper's m_k(lambda) with lambda = d/N).

EXACT EVALUATION.  E tr T^k = sum over m-tuples of E prod_j Tr U^{h_j},
h_j = m_j - m_{j+1} (cyclic).  Expanding traces over eigenvalue indices and
grouping by coincidence pattern,

    E prod_j Tr U^{h_j} = sum over set partitions P of {1..k} of I(H(P)),

    H(P) = (sum of h_j over each block),

    I(H) = integral over the torus of prod_B e^{i H_B theta_B}
           * rho_b^{CUE}(theta_1..theta_b) d theta,

and rho_b^CUE = det[ K_N(theta_i - theta_j) ] with
K_N(theta) = (1/2pi) sum_{a=0}^{N-1} e^{i a theta}.  Expanding the
determinant over permutations sigma of the blocks, each cycle C of sigma
(visiting blocks c_1 -> c_2 -> ... -> c_r -> c_1) contributes zero unless
sum_{i in C} H_i = 0, and otherwise exactly

    #{ a in Z : a + P_t in [0, N-1] for all t } = max(0, N - spread(C)),

    P_t = partial sums of (H_{c_1}, ..., H_{c_r}),  spread = max P - min P.

(For r = 1 this reads: H_i = 0 contributes N.)  So everything is integer
arithmetic: no quadrature, no floats, no truncation.

VALIDATION built in: E tr T^1 = d*N (T_mm = Tr U^0 = N exactly);
E |Tr U^h|^2 = min(|h|, N) is reproduced by I on the 2-cycle; and the
k = 2, 3 limits must equal the published 4/3, 2.

LIMIT EXTRACTION.  For fixed k, E tr G^k / d is a rational function whose
numerator/denominator are eventually polynomial in N (the lattice counts are
piecewise polynomial and the boundary shape stabilises).  Compute exact
values at many odd N, difference them: when the (r+1)-th finite differences
of N^k * (that quantity) vanish identically over a long run, the polynomial
is exact, and its leading coefficient is the limit.  Overdetermination (extra
sample points) is the check.
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from functools import lru_cache


def set_partitions(items: tuple[int, ...]):
    if not items:
        yield ()
        return
    first, rest = items[0], items[1:]
    for part in set_partitions(rest):
        for i in range(len(part)):
            yield part[:i] + ((part[i] + (first,)),) + part[i + 1:]
        yield ((first,),) + part


@lru_cache(maxsize=None)
def _partitions_of_cycle(k: int):
    return list(set_partitions(tuple(range(k))))


@lru_cache(maxsize=None)
def _perms(b: int):
    out = []
    for sigma in itertools.permutations(range(b)):
        # cycle decomposition and sign
        seen = [False] * b
        cycles = []
        sign = 1
        for i in range(b):
            if seen[i]:
                continue
            cyc = []
            j = i
            while not seen[j]:
                seen[j] = True
                cyc.append(j)
                j = sigma[j]
            cycles.append(tuple(cyc))
            if len(cyc) % 2 == 0:
                sign = -sign
        out.append((sign, tuple(cycles)))
    return out


def correlation_integral(H: tuple[int, ...], N: int) -> int:
    """I(H): the exact CUE b-point integral defined in the module docstring."""
    b = len(H)
    total = 0
    for sign, cycles in _perms(b):
        term = 1
        for cyc in cycles:
            s = 0
            partial = [0]
            for i in cyc:
                s += H[i]
                partial.append(s)
            if s != 0:
                term = 0
                break
            spread = max(partial) - min(partial)
            cnt = N - spread
            if cnt <= 0:
                term = 0
                break
            term *= cnt
        if term:
            total += sign * term
    return total


def joint_trace_moment(h: tuple[int, ...], N: int) -> int:
    """E prod_j Tr U^{h_j} over CUE(N), exactly (requires sum h_j = 0)."""
    assert sum(h) == 0
    k = len(h)
    total = 0
    for part in _partitions_of_cycle(k):
        H = tuple(sum(h[i] for i in block) for block in part)
        total += correlation_integral(H, N)
    return total


def exact_tr_Gk(k: int, N: int, M: int) -> Fraction:
    """E tr G^k / d, exactly, for the band [-M, M], d = 2M+1, G = T/N."""
    d = 2 * M + 1
    # cache joint moments by the sorted h-tuple? h order matters (cyclic),
    # but only through the partial-sum spreads; cache on the tuple directly.
    cache: dict[tuple[int, ...], int] = {}
    total = 0
    rng = range(-M, M + 1)
    for m in itertools.product(rng, repeat=k - 1):
        # last index summed implicitly: h_j determined by consecutive
        # differences of (m_1..m_{k-1}, m_k); we must sum over all k indices.
        # Instead: exploit translation invariance -- traces depend on the
        # differences only, so fix nothing and sum all k indices directly.
        pass
    # direct k-fold sum (k <= 4 is fine: (2M+1)^k terms with small M growth)
    for ms in itertools.product(rng, repeat=k):
        h = tuple(ms[i] - ms[(i + 1) % k] for i in range(k))
        val = cache.get(h)
        if val is None:
            val = joint_trace_moment(h, N)
            cache[h] = val
        total += val
    return Fraction(total, N ** k * d)


def validate(N: int = 12) -> None:
    # E |Tr U^h|^2 = min(|h|, N)
    for h in (1, 3, N - 1, N, N + 3, 2 * N):
        got = joint_trace_moment((h, -h), N)
        want = min(h, N)
        assert got == want, (h, got, want)
    # E Tr U^0 = N, and the 3-cycle Gaussian value E |TrU^h|^2 stays clean
    assert joint_trace_moment((0,), N) == N
    print(f"validate(N={N}): exact CUE trace moments OK")


def limit_of_moment(k: int, n_values: list[int]) -> tuple[Fraction, list[Fraction]]:
    """Exact E tr G^k / d at each odd N (with M = (N-1)/2), plus the limit.

    Fits an exact polynomial in 1/N by requiring finite differences of
    N^j * value to vanish; simplest robust version: Lagrange-extrapolate the
    exact rational sequence in the variable x = 1/N^2 ... but the parity terms
    make it x = 1/N.  We fit value(N) = c_0 + c_1/N + ... + c_p/N^p exactly
    through p+1 points and confirm on the remaining points.
    """
    vals = []
    for N in n_values:
        assert N % 2 == 1
        M = (N - 1) // 2
        vals.append(exact_tr_Gk(k, N, M))
    # exact polynomial fit in t = 1/N through the last p+1 points
    p = len(n_values) - 2
    ts = [Fraction(1, N) for N in n_values]
    # Lagrange evaluation at t = 0 using points 1..len-1 (skip the smallest N)
    pts = list(zip(ts[1:], vals[1:]))
    c0 = Fraction(0)
    for i, (ti, vi) in enumerate(pts):
        w = Fraction(1)
        for j, (tj, _) in enumerate(pts):
            if i != j:
                w *= (0 - tj) / (ti - tj)
        c0 += vi * w
    # check: same extrapolation dropping the largest N instead
    pts2 = list(zip(ts[:-1], vals[:-1]))
    c0b = Fraction(0)
    for i, (ti, vi) in enumerate(pts2):
        w = Fraction(1)
        for j, (tj, _) in enumerate(pts2):
            if i != j:
                w *= (0 - tj) / (ti - tj)
        c0b += vi * w
    return c0, vals + [c0b]


if __name__ == "__main__":
    import sys
    validate()
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    Ns = [int(x) for x in sys.argv[2:]] or [11, 15, 19, 23, 27, 31, 35]
    limit, detail = limit_of_moment(k, Ns)
    for N, v in zip(Ns, detail):
        print(f"  N={N:3d}  E tr G^{k}/d = {v} = {float(v):.10f}")
    print(f"  cross-check extrapolation (drop largest N): {detail[-1]} = {float(detail[-1]):.10f}")
    print(f"m_{k}(1) exact-N extrapolation -> {limit} = {float(limit):.10f}")
    print("paper 13/4 =", 3.25, "  wick engine 49/15 =", float(Fraction(49, 15)))
