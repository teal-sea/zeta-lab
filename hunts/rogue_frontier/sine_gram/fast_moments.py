"""Optimized exact engine for E tr T^k over CUE(N), band of d consecutive frequencies.

The quantity.  T_{m,m'} = Tr U^{m-m'} for m, m' in a band of d consecutive
integers, U ~ CUE(N).  E tr T^k is an integer.  With d = lambda N, G = T/N,
the target moments are m_k(lambda) = lim_N E tr T^k / (N^k d).

Method (mathematically identical to exact_finite_N.py, reorganised for speed):

1.  Sum over h-tuples, not m-tuples.  E tr T^k =
        sum_{h in Z^k, sum h = 0} R(h) * J(h, N),
    R(h) = #{bands positions} = max(0, d - spread(0, s_1, ..., s_{k-1})),
    s_j the partial sums of h, and J(h, N) = E prod_j Tr U^{h_j}.
    R > 0 forces every |h_j| <= d - 1, a finite box.

2.  Sum over sorted classes.  J is a symmetric function of the h entries
    (it is a sum over set partitions of the index positions), so group the
    ordered tuples by their sorted class:
        E tr T^k = sum_{classes c} J(c, N) * A(c) / mult(c),
    A(c) = sum over ALL k! column orderings pi of R(pi(c)) and mult(c) =
    prod (multiplicity of each repeated value)!.  A is divisible by mult.

3.  Rotation reduction for A.  R is invariant under cyclic rotation of the
    h sequence (the partial-sum set only shifts), so
    A = k * sum over the (k-1)! orderings that keep the last column last;
    the last entry never enters the spread (s_k = 0 is automatic).

4.  Global negation symmetry.  J(-h) = J(h), R is invariant under negating
    the sequence, so classes are paired with their negated-sorted partner
    and only canonical representatives are computed (weight 2, or 1 if
    self-paired).

5.  J per class, vectorized.  J(c, N) = sum over set partitions P of the
    k positions, block sums H_B, then sum over permutations sigma of the
    blocks with sign(sigma), each cycle contributing
    max(0, N - spread(0, partial sums of H along the cycle)) if the cycle's
    H-sum is 0, else 0 (a 1-cycle gives N iff H_B = 0).  The partition and
    permutation structures are imported from exact_finite_N so the two
    engines share one combinatorial definition.  Cycle weights are memoized
    per (chunk, partition); everything is int64 numpy over class chunks.

Exactness.  All arithmetic is integer.  int64 overflow is excluded by
runtime guards: |J| <= (number of (P, sigma) terms) * N^b with b <= k, the
per-class product is checked against 2^62, and the final accumulation is
chunked into Python big integers with a provably safe chunk length.

Validation this engine passed (run `fast_moments.py validate`):
  - term-count identity: sum over partitions of b! equals the Fubini
    numbers 13, 75, 541, 4683, 47293 for k = 3..7;
  - J against exact_finite_N.joint_trace_moment on the unit tests
    E |Tr U^h|^2 = min(|h|, N) (h = 1, 3, N-1, N, N+3, 2N) and on random
    sum-zero h-tuples for k = 3..7 at several N;
  - E tr T^k against the naive engine exact_tr_Gk at (k=2, N=7,9),
    (k=3, N=7,9,11), (k=4, N=7,9,11,13,15), (k=5, N=7), and the recorded
    values E tr T^4 = 53739, 190029, 519981, 1201031, 2459255 at
    N = 7, 9, 11, 13, 15;
  - the negation-symmetry shortcut against the unreduced sum at
    (k=5, N=7) and (k=6, N=5);
  - E tr T^1 = d N and E tr T^3 = 2 N^4 - N^2 on the sweep range.

Usage:
  .venv/bin/python fast_moments.py validate [--slow]
  .venv/bin/python fast_moments.py sweep --k 5 --N 5 7 9 ...        (lambda = 1, d = N)
  .venv/bin/python fast_moments.py sweep-lambda --p 4 --q 5 --k 4 --t 1 2 3 ...
                                                        (N = q t, d = p t)
  .venv/bin/python fast_moments.py analyze --k 5
  .venv/bin/python fast_moments.py analyze-lambda --p 4 --q 5 --k 4
Results are checkpointed to exact_trTk_values.json (lambda = 1) and
exact_trTk_values_lambda.json (other lambda) after every (k, N).
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from fractions import Fraction
from functools import lru_cache
from itertools import permutations

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from exact_finite_N import _perms, joint_trace_moment, set_partitions  # noqa: E402

JSON_PATH = os.path.join(_HERE, "exact_trTk_values.json")
JSON_LAMBDA_PATH = os.path.join(_HERE, "exact_trTk_values_lambda.json")

#: sum over set partitions of {1..k} of (number of blocks)! (Fubini numbers).
FUBINI = {1: 1, 2: 3, 3: 13, 4: 75, 5: 541, 6: 4683, 7: 47293, 8: 545835}


@lru_cache(maxsize=None)
def structures(k: int):
    """All (blocks, [(sign, cycles), ...]) pairs for partitions of {0..k-1}."""
    out = []
    for part in set_partitions(tuple(range(k))):
        blocks = tuple(tuple(b) for b in part)
        out.append((blocks, _perms(len(blocks))))
    n_terms = sum(len(pl) for _, pl in out)
    assert n_terms == FUBINI[k], (k, n_terms)
    return out


# ---------------------------------------------------------------------------
# class generation: sorted k-tuples, entries in [-B, B], sum zero
# ---------------------------------------------------------------------------


def gen_classes(k: int, B: int) -> np.ndarray:
    """All nondecreasing k-tuples with entries in [-B, B] summing to zero."""
    assert k >= 2
    prefixes: list[tuple[tuple[int, ...], int, int]] = []

    def rec(i: int, lo: int, s: int, buf: list[int]) -> None:
        r = k - i
        if r == 2:
            vmin = max(lo, -s - B)
            vmax = min(B, (-s) // 2)
            if vmax >= vmin:
                prefixes.append((tuple(buf), vmin, vmax - vmin + 1))
            return
        vmin = max(lo, -s - (r - 1) * B)
        vmax = min(B, (-s) // r)
        for v in range(vmin, vmax + 1):
            buf.append(v)
            rec(i + 1, v, s + v, buf)
            buf.pop()

    rec(0, -B, 0, [])
    n = sum(c for _, _, c in prefixes)
    out = np.empty((n, k), dtype=np.int64)
    pos = 0
    for pref, vmin, c in prefixes:
        if pref:
            out[pos:pos + c, : k - 2] = pref
        v = np.arange(vmin, vmin + c, dtype=np.int64)
        out[pos:pos + c, k - 2] = v
        out[pos:pos + c, k - 1] = -sum(pref) - v
        pos += c
    return out


def canonical_weights(cls: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Keep-mask and weight for the negation pairing c <-> sorted(-c).

    sorted(-c) is (-c) reversed since c is nondecreasing.  A row is kept iff
    it is lexicographically <= its partner; weight 2 if strictly smaller
    (it stands for the pair), 1 if self-paired.
    """
    neg = -cls[:, ::-1]
    n, k = cls.shape
    lt = np.zeros(n, dtype=bool)
    gt = np.zeros(n, dtype=bool)
    decided = np.zeros(n, dtype=bool)
    for j in range(k):
        a, b = cls[:, j], neg[:, j]
        l = ~decided & (a < b)
        g = ~decided & (a > b)
        lt |= l
        gt |= g
        decided |= l | g
    keep = ~gt
    weight = np.where(lt, 2, 1).astype(np.int64)
    return keep, weight


def multiplicities(cls: np.ndarray) -> np.ndarray:
    """prod over distinct values of (repeat count)! per sorted row."""
    n, k = cls.shape
    mult = np.ones(n, dtype=np.int64)
    run = np.ones(n, dtype=np.int64)
    for j in range(1, k):
        same = cls[:, j] == cls[:, j - 1]
        run = np.where(same, run + 1, 1)
        mult = np.where(same, mult * run, mult)
    return mult


# ---------------------------------------------------------------------------
# A: ordering-summed band counts.  J: joint trace moments.  Vectorized.
# ---------------------------------------------------------------------------


def band_count_sum(chunk: np.ndarray, d: int, perms) -> np.ndarray:
    """sum over ALL k! column orderings of max(0, d - spread(0, partial sums)).

    Rotation reduction: only the (k-1)! orderings of the first k-1 columns
    are enumerated (last column pinned last; it never enters the spread),
    and the result is multiplied by k.
    """
    n, k = chunk.shape
    total = np.zeros(n, dtype=np.int64)
    cols = [chunk[:, j] for j in range(k - 1)]
    for perm in perms:
        s = cols[perm[0]].copy()
        mx = np.maximum(s, 0)
        mn = np.minimum(s, 0)
        for idx in perm[1:]:
            s += cols[idx]
            np.maximum(mx, s, out=mx)
            np.minimum(mn, s, out=mn)
        r = d - (mx - mn)
        np.maximum(r, 0, out=r)
        total += r
    return total * k


def _cycle_weight(H: list[np.ndarray], cyc: tuple[int, ...], N: int) -> np.ndarray:
    """max(0, N - spread(0, partial sums of H along cyc)), 0 unless sum is 0."""
    s = H[cyc[0]].copy()
    mx = np.maximum(s, 0)
    mn = np.minimum(s, 0)
    for c in cyc[1:]:
        s += H[c]
        np.maximum(mx, s, out=mx)
        np.minimum(mn, s, out=mn)
    w = N - (mx - mn)
    np.maximum(w, 0, out=w)
    return np.where(s == 0, w, 0)


def joint_moment_chunk(chunk: np.ndarray, N: int, structs) -> np.ndarray:
    """J(row, N) = E prod_j Tr U^{h_j} for every row of the chunk, exactly."""
    n = chunk.shape[0]
    J = np.zeros(n, dtype=np.int64)
    for blocks, perm_list in structs:
        H = [chunk[:, list(blk)].sum(axis=1) for blk in blocks]
        cache: dict[tuple[int, ...], np.ndarray] = {}
        for sign, cycles in perm_list:
            term = None
            for cyc in cycles:
                w = cache.get(cyc)
                if w is None:
                    w = _cycle_weight(H, cyc, N)
                    cache[cyc] = w
                term = w if term is None else term * w
            if sign > 0:
                J += term
            else:
                J -= term
    return J


def _exact_int64_sum(arr: np.ndarray) -> int:
    """Exact sum of an int64 array as a Python integer (no overflow)."""
    if len(arr) == 0:
        return 0
    m = int(np.abs(arr).max())
    if m == 0:
        return 0
    step = max(1, (2 ** 62) // (m + 1))
    return sum(int(arr[i:i + step].sum()) for i in range(0, len(arr), step))


# ---------------------------------------------------------------------------
# the assembled quantity
# ---------------------------------------------------------------------------


def band_trace_moment(
    k: int,
    N: int,
    d: int | None = None,
    cls: np.ndarray | None = None,
    use_sym: bool = True,
    chunk_size: int | None = None,
) -> int:
    """E tr T^k over CUE(N) for a band of d consecutive frequencies, exact."""
    if d is None:
        d = N
    if k == 1:
        return d * N
    B = d - 1
    if cls is None:
        cls = gen_classes(k, B)
    else:
        mask = (cls[:, 0] >= -B) & (cls[:, -1] <= B)
        cls = cls[mask]
    if use_sym:
        keep, weight = canonical_weights(cls)
        cls = cls[keep]
        weight = weight[keep]
    else:
        weight = np.ones(len(cls), dtype=np.int64)
    structs = structures(k)
    perms = list(permutations(range(k - 1)))
    if chunk_size is None:
        chunk_size = 8192 if k >= 7 else 32768
    total = 0
    for i0 in range(0, len(cls), chunk_size):
        ch = np.ascontiguousarray(cls[i0:i0 + chunk_size])
        w = weight[i0:i0 + chunk_size]
        A = band_count_sum(ch, d, perms)
        mult = multiplicities(ch)
        assert (A % mult == 0).all(), "A not divisible by multiplicity"
        q = A // mult
        J = joint_moment_chunk(ch, N, structs)
        mj = int(np.abs(J).max(initial=0))
        mq = int(q.max(initial=0))
        assert mj * mq * 2 < 2 ** 62, "per-class product would overflow int64"
        contrib = w * q * J
        total += _exact_int64_sum(contrib)
    return total


# ---------------------------------------------------------------------------
# exact polynomial identification (Fractions throughout)
# ---------------------------------------------------------------------------


def _polymul(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def lagrange_fit(points: list[tuple[int, int]]) -> list[Fraction]:
    """Exact monomial coefficients (ascending) through the given points."""
    coeffs = [Fraction(0)] * len(points)
    for xi, yi in points:
        num = [Fraction(1)]
        den = Fraction(1)
        for xj, _ in points:
            if xj == xi:
                continue
            num = _polymul(num, [Fraction(-xj), Fraction(1)])
            den *= xi - xj
        for t, c in enumerate(num):
            coeffs[t] += Fraction(yi) * c / den
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs


def poly_eval(coeffs: list[Fraction], x: int) -> Fraction:
    acc = Fraction(0)
    for c in reversed(coeffs):
        acc = acc * x + c
    return acc


def poly_str(coeffs: list[Fraction], var: str = "N") -> str:
    parts = []
    for p in range(len(coeffs) - 1, -1, -1):
        c = coeffs[p]
        if c == 0:
            continue
        mono = "" if p == 0 else (var if p == 1 else f"{var}^{p}")
        cs = str(c)
        parts.append(f"({cs})*{mono}" if mono else f"({cs})")
    return " + ".join(parts) if parts else "0"


def identify_polynomial(values: dict[int, int], degree: int, min_extra: int = 2):
    """Find the smallest grid start x0 whose degree-fit predicts all later values.

    Fits through the first degree+1 grid points at or after x0 and demands
    exact agreement on every remaining computed value (at least min_extra of
    them).  Returns (x0, coeffs, checked_points, pre_regime_defects) or None.
    """
    xs = sorted(values)
    for i0 in range(len(xs)):
        pts = xs[i0:i0 + degree + 1]
        rest = xs[i0 + degree + 1:]
        if len(pts) < degree + 1 or len(rest) < min_extra:
            break
        coeffs = lagrange_fit([(x, values[x]) for x in pts])
        if all(poly_eval(coeffs, x) == values[x] for x in rest):
            pre = [(x, values[x] - poly_eval(coeffs, x)) for x in xs[:i0]]
            return pts[0], coeffs, rest, pre
    return None


# ---------------------------------------------------------------------------
# checkpointing
# ---------------------------------------------------------------------------


def _load(path: str) -> dict:
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return {}


def _store(path: str, data: dict) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(data, f, indent=1, sort_keys=True)
    os.replace(tmp, path)


def checkpoint(k: int, N: int, value: int, path: str = JSON_PATH) -> None:
    data = _load(path)
    data.setdefault(str(k), {})[str(N)] = str(value)
    _store(path, data)


def checkpoint_lambda(lam: str, k: int, N: int, value: int,
                      path: str = JSON_LAMBDA_PATH) -> None:
    data = _load(path)
    data.setdefault(lam, {}).setdefault(str(k), {})[str(N)] = str(value)
    _store(path, data)


# ---------------------------------------------------------------------------
# validation
# ---------------------------------------------------------------------------

KNOWN_TR_T4 = {7: 53739, 9: 190029, 11: 519981, 13: 1201031, 15: 2459255}


def validate(slow: bool = False) -> None:
    rng = np.random.default_rng(20260817)

    # term counts against the Fubini numbers
    for k in range(2, 8):
        structures(k)
    print("term counts match Fubini numbers for k = 2..7")

    # J against the naive joint_trace_moment: pair-correlation unit tests
    N = 12
    for h in (1, 3, N - 1, N, N + 3, 2 * N):
        row = np.array([[-h, h]], dtype=np.int64)
        got = int(joint_moment_chunk(row, N, structures(2))[0])
        assert got == min(h, N), (h, got)
    print("E |Tr U^h|^2 = min(|h|, N) reproduced (h = 1..2N)")

    # J against the naive engine on random sum-zero tuples
    for k in range(3, 8):
        for N in (5, 9, 12):
            for _ in range(12):
                h = rng.integers(-N, N + 1, size=k - 1)
                h = np.append(h, -h.sum())
                row = np.sort(h)[None, :].astype(np.int64)
                fast = int(joint_moment_chunk(row, N, structures(k))[0])
                naive = joint_trace_moment(tuple(int(x) for x in row[0]), N)
                assert fast == naive, (k, N, row, fast, naive)
    print("J matches exact_finite_N.joint_trace_moment on random tuples, k = 3..7")

    # full moment against the naive engine (integer identity)
    from exact_finite_N import exact_tr_Gk

    def naive_total(k: int, N: int) -> int:
        M = (N - 1) // 2
        d = 2 * M + 1
        frac = exact_tr_Gk(k, N, M) * N ** k * d
        assert frac.denominator == 1
        return frac.numerator

    for k, Ns in ((2, (7, 9)), (3, (7, 9, 11)), (4, (7, 9, 11, 13, 15))):
        for N in Ns:
            fast = band_trace_moment(k, N)
            naive = naive_total(k, N)
            assert fast == naive, (k, N, fast, naive)
            if k == 4:
                assert fast == KNOWN_TR_T4[N], (N, fast)
    print("E tr T^k matches the naive engine: k=2 (N=7,9), k=3 (N=7..11), "
          "k=4 (N=7..15, incl. recorded values)")

    # E tr T^3 = 2 N^4 - N^2 on a wider range
    for N in (5, 7, 9, 11, 13, 17, 21):
        assert band_trace_moment(3, N) == 2 * N ** 4 - N ** 2, N
    print("E tr T^3 = 2N^4 - N^2 on N = 5..21 odd")

    # negation-symmetry shortcut against the unreduced sum
    for k, N in ((5, 7), (6, 5)):
        a = band_trace_moment(k, N, use_sym=True)
        b = band_trace_moment(k, N, use_sym=False)
        assert a == b, (k, N, a, b)
    print("negation-symmetry shortcut agrees with the unreduced sum")

    if slow:
        fast = band_trace_moment(5, 7)
        naive = naive_total(5, 7)
        assert fast == naive, (fast, naive)
        print(f"k=5, N=7: fast {fast} == naive {naive}")
        fast = band_trace_moment(6, 7)
        naive = naive_total(6, 7)
        assert fast == naive, (fast, naive)
        print(f"k=6, N=7: fast {fast} == naive {naive}")

    print("validate: ALL CHECKS PASSED")


# ---------------------------------------------------------------------------
# sweeps and analysis
# ---------------------------------------------------------------------------


def sweep(k: int, Ns: list[int]) -> None:
    Bmax = max(Ns) - 1
    t0 = time.time()
    cls = gen_classes(k, Bmax)
    print(f"k={k}: {len(cls)} classes at B={Bmax} "
          f"({time.time() - t0:.1f}s)", flush=True)
    done = _load(JSON_PATH).get(str(k), {})
    for N in sorted(Ns):
        if str(N) in done:
            print(f"k={k} N={N}: already done, skipping", flush=True)
            continue
        t0 = time.time()
        val = band_trace_moment(k, N, d=N, cls=cls)
        checkpoint(k, N, val)
        print(f"k={k} N={N}: E tr T^k = {val}  "
              f"(m_k proxy {val / N ** (k + 1):.8f}, {time.time() - t0:.1f}s)",
              flush=True)


def sweep_lambda(p: int, q: int, k: int, ts: list[int]) -> None:
    """lambda = p/q exactly: N = q t, d = p t."""
    lam = f"{p}/{q}"
    Bmax = p * max(ts) - 1
    cls = gen_classes(k, Bmax)
    print(f"lambda={lam} k={k}: {len(cls)} classes at B={Bmax}", flush=True)
    done = _load(JSON_LAMBDA_PATH).get(lam, {}).get(str(k), {})
    for t in sorted(ts):
        N, d = q * t, p * t
        if str(N) in done:
            continue
        t0 = time.time()
        val = band_trace_moment(k, N, d=d, cls=cls)
        checkpoint_lambda(lam, k, N, val)
        print(f"lambda={lam} k={k} N={N} d={d}: E tr T^k = {val}  "
              f"(m_k proxy {val / (N ** k * d):.8f}, {time.time() - t0:.1f}s)",
              flush=True)


def analyze(k: int, degree: int | None = None, min_extra: int = 2) -> None:
    vals = {int(N): int(v) for N, v in _load(JSON_PATH).get(str(k), {}).items()}
    if not vals:
        print(f"no values recorded for k={k}")
        return
    degree = degree if degree is not None else k + 1
    res = identify_polynomial(vals, degree, min_extra)
    print(f"k={k}: {len(vals)} exact values, N = {min(vals)}..{max(vals)}")
    if res is None:
        print(f"  NO degree-{degree} polynomial regime found with "
              f">= {min_extra} spare points")
        return
    N0, coeffs, rest, pre = res
    print(f"  polynomial regime observed from N = {N0} (odd grid)")
    print(f"  fit points: N = {N0}..{N0 + 2 * degree}; "
          f"reproduced exactly at N = {rest}")
    for x, defect in pre:
        print(f"  pre-regime N={x}: value - poly = {defect}")
    print(f"  E tr T^{k} = {poly_str(coeffs)}")
    lead = coeffs[-1] if len(coeffs) == degree + 1 else Fraction(0)
    print(f"  leading coefficient (= m_{k}(1)): {lead} = {float(lead):.10f}")
    if 41 not in vals:
        v41 = poly_eval(coeffs, 41) / Fraction(41 ** (k + 1))
        print(f"  predicted E tr G^{k}/d at N=41 (for MC comparison): "
              f"{float(v41):.6f}")


def analyze_lambda(p: int, q: int, k: int, min_extra: int = 2) -> None:
    lam = f"{p}/{q}"
    raw = _load(JSON_LAMBDA_PATH).get(lam, {}).get(str(k), {})
    vals_t = {int(N) // q: int(v) for N, v in raw.items()}
    if not vals_t:
        print(f"no values recorded for lambda={lam}, k={k}")
        return
    degree = k + 1
    res = identify_polynomial(vals_t, degree, min_extra)
    print(f"lambda={lam} k={k}: {len(vals_t)} exact values, "
          f"t = {min(vals_t)}..{max(vals_t)} (N = q t)")
    if res is None:
        print(f"  NO degree-{degree} polynomial regime found in t")
        return
    t0_, coeffs, rest, pre = res
    print(f"  polynomial regime in t observed from t = {t0_}; "
          f"reproduced exactly at t = {rest}")
    for x, defect in pre:
        print(f"  pre-regime t={x}: value - poly = {defect}")
    print(f"  E tr T^{k} = {poly_str(coeffs, 't')}   (N = {q} t, d = {p} t)")
    lead = coeffs[-1] if len(coeffs) == degree + 1 else Fraction(0)
    mk = lead / (q ** k * p)
    print(f"  m_{k}({lam}) = lead/(q^k p) = {mk} = {float(mk):.10f}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    v = sub.add_parser("validate")
    v.add_argument("--slow", action="store_true")
    s = sub.add_parser("sweep")
    s.add_argument("--k", type=int, required=True)
    s.add_argument("--N", type=int, nargs="+", required=True)
    sl = sub.add_parser("sweep-lambda")
    sl.add_argument("--p", type=int, required=True)
    sl.add_argument("--q", type=int, required=True)
    sl.add_argument("--k", type=int, required=True)
    sl.add_argument("--t", type=int, nargs="+", required=True)
    a = sub.add_parser("analyze")
    a.add_argument("--k", type=int, required=True)
    a.add_argument("--degree", type=int, default=None)
    a.add_argument("--min-extra", type=int, default=2)
    al = sub.add_parser("analyze-lambda")
    al.add_argument("--p", type=int, required=True)
    al.add_argument("--q", type=int, required=True)
    al.add_argument("--k", type=int, required=True)
    args = ap.parse_args()
    if args.cmd == "validate":
        validate(slow=args.slow)
    elif args.cmd == "sweep":
        sweep(args.k, args.N)
    elif args.cmd == "sweep-lambda":
        sweep_lambda(args.p, args.q, args.k, args.t)
    elif args.cmd == "analyze":
        analyze(args.k, degree=args.degree, min_extra=args.min_extra)
    elif args.cmd == "analyze-lambda":
        analyze_lambda(args.p, args.q, args.k)


if __name__ == "__main__":
    main()
