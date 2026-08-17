"""Independent symbolic computation of the true C(v,w), and comparison
against the three evaluation modes of bian_engine.

Route (fully independent of the chapter 6-7 combinatorics):

1. On the squarefree slice n = p_1 ... p_m (distinct primes), compute
   B(v,n) exactly as a polynomial in the logs s_i = log p_i, directly from
   the defining recursion (3.6): b_1 = -Lambda,
   b_{j+1} = -(b_j * Lambda + b_j log), and
   B((v_1..v_l), n) = b_{v_1} * ... * b_{v_{l-1}} * (b_{v_l} log)(n).
   Convolution on squarefree n is a sum over ordered set partitions of the
   prime set; this is finite algebra (sympy), checkable per n.

2. B(v,n) B(w,n) is homogeneous of degree |v|+|w|+2 in the s_i.  By the
   standard multi-prime asymptotic (= thesis Lemma 8, which carries the
   1/m! correctly),

     sum_{p_1<...<p_m, prod p <= x} prod s_i^{h_i}
        = (prod (h_i - 1)!) / (m! (H-1)!) x (log x)^{H-1} + O(x log^{H-2} x),

   with H = sum h_i.  Summing over the monomials of B(v,.)B(w,.) on each
   slice m and adding slices gives the true leading constant C(v,w) of
   S(v,w;x) = (-1)^{|v|+|w|} C(v,w) x (log x)^{|v|+|w|+1} + ...

The script compares this against bian_engine.C_pair in modes "skip"
(Bian's code), "zero", and "corrected", for a battery of pairs.  Expected:
"corrected" agrees everywhere; "skip" and "zero" disagree whenever a
component >= 2 (overcount) or >= 3 (phantom slots) is involved.

Also prints the two finite counterexamples that pin the defects without
any asymptotics:
  (a) eq (6.18) at n = 6, alpha = (2), beta = (1): printed RHS doubles
      Lambda_2(6) log 6;
  (b) C((j),(1)) = 1 for every j (b_j(p) = (-1)^j log^j p on primes),
      against skip's 6/5 (j=3) and 9/7 (j=5).

Run:  .venv/bin/python hunts/rogue_frontier/fkappa/validate_pairs.py
"""

import itertools
import sys
import os
from fractions import Fraction
from math import factorial as fact

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bian_engine as be


def set_partitions_ordered(items, blocks):
    """All ways to distribute `items` into `blocks` labeled possibly-empty
    blocks (as tuples of frozensets)."""
    if blocks == 1:
        yield (frozenset(items),)
        return
    items = list(items)
    n = len(items)
    for mask in range(2 ** n):
        first = frozenset(items[i] for i in range(n) if mask >> i & 1)
        rest = [items[i] for i in range(n) if not (mask >> i & 1)]
        for tail in set_partitions_ordered(rest, blocks - 1):
            yield (first,) + tail


class SqfreeFunc:
    """An arithmetical function restricted to squarefree n, represented as
    {frozenset of prime-symbols: sympy expr}."""

    def __init__(self, table):
        self.t = table

    @staticmethod
    def Lambda(syms):
        # Lambda on squarefree: log p on single primes
        return SqfreeFunc({frozenset([s]): s for s in syms})

    def conv(self, other, syms):
        out = {}
        for S in all_subsets(syms):
            tot = 0
            Sl = list(S)
            n = len(Sl)
            for mask in range(2 ** n):
                A = frozenset(Sl[i] for i in range(n) if mask >> i & 1)
                B = S - A
                fa = self.t.get(A, 0)
                fb = other.t.get(B, 0)
                if fa != 0 and fb != 0:
                    tot += fa * fb
            if tot != 0:
                out[S] = sp.expand(tot)
        return SqfreeFunc(out)

    def mul_log(self, syms):
        out = {}
        for S, val in self.t.items():
            logn = sum(S) if S else 0
            v = sp.expand(val * logn)
            if v != 0:
                out[S] = v
        return SqfreeFunc(out)

    def neg(self):
        return SqfreeFunc({S: -v for S, v in self.t.items()})


def all_subsets(syms):
    out = []
    sl = list(syms)
    for r in range(len(sl) + 1):
        for c in itertools.combinations(sl, r):
            out.append(frozenset(c))
    return out


def b_funcs(jmax, syms):
    lam = SqfreeFunc.Lambda(syms)
    b = {1: lam.neg()}
    for j in range(1, jmax):
        conv = b[j].conv(lam, syms)
        lg = b[j].mul_log(syms)
        b[j + 1] = SqfreeFunc(
            {S: sp.expand(-(conv.t.get(S, 0) + lg.t.get(S, 0)))
             for S in set(conv.t) | set(lg.t)})
    return b


def B_func(v, b, syms):
    """B(v, .) on squarefree support."""
    lam_like = b[v[-1]].mul_log(syms)
    out = lam_like
    for u in reversed(v[:-1]):
        out = b[u].conv(out, syms)
    return out


def true_C(v, w, mmax=None):
    """The true constant C(v,w) via slices + Lemma 8."""
    nv, nw = sum(v), sum(w)
    if min(nv, nw) < max(len(v), len(w)):
        return Fraction(0)
    H1 = nv + nw + 1  # exponent of log x; (H-1)! with H-1 = H1
    mmax = mmax if mmax is not None else min(nv, nw)
    total = Fraction(0)
    for m in range(1, mmax + 1):
        syms = sp.symbols(f"s1:{m+1}", positive=True)
        b = b_funcs(max(max(v), max(w)), syms)
        Bv = B_func(v, b, syms)
        Bw = B_func(w, b, syms)
        S = frozenset(syms)
        prod = sp.expand(Bv.t.get(S, 0) * Bw.t.get(S, 0))
        if prod == 0:
            continue
        poly = sp.Poly(prod, *syms)
        slice_sum = Fraction(0)
        for monom, coeff in poly.terms():
            c = Fraction(int(sp.numer(coeff)), int(sp.denom(coeff)))
            num = 1
            for h in monom:
                num *= fact(h - 1)
            slice_sum += c * Fraction(num, fact(m) * fact(H1))
        total += slice_sum
    # Convention: return the raw leading coefficient of S(v,w;x)/(x log^H1 x),
    # which is what bian_engine.C_pair computes (sumgen folds the
    # (-1)^{|v|+|w|} of eq (7.7) into its return value).
    return total


def engine_C(v, w, mode):
    be.READING = mode
    for c in (be._prof_cache, be._prefix_cache, be._side_cache,
              be._ss_cache, be._c4_cache, be._consi_cache):
        c.clear()
    return be.C_pair(v, w)


def finite_counterexamples():
    print("(a) eq (6.18) at n = 6 = 2*3, alpha=(2), beta=(1):")
    L2, L3 = sp.log(2), sp.log(3)
    truth = 2 * L2 * L3 * (L2 + L3)      # Lambda_2(6) log 6
    printed = 4 * L2 * L3 * (L2 + L3)    # sum_sigma 2! sum_c ...
    print(f"    Lambda_2(6) log 6      = 2 log2 log3 log6")
    print(f"    printed (6.18) RHS     = 4 log2 log3 log6"
          f"   (ratio {sp.simplify(printed/truth)})")
    print("(b) |C((j),(1))| = 1 for all j (exact: b_j(p) = (-1)^j log^j p,"
          " so S((j),(1);x) = (-1)^{j+1} sum_p log^{j+3} p + O(sqrt x)):")
    for j in (2, 3, 4, 5):
        vals = {m: engine_C((j,), (1,), m) for m in
                ("skip", "zero", "corrected")}
        truth = (-1) ** (j + 1)
        print(f"    j={j}: skip={vals['skip']}, zero={vals['zero']}, "
              f"corrected={vals['corrected']}  (truth {truth})")


def main():
    finite_counterexamples()
    print()
    battery = [
        ((1,), (1,)), ((2,), (1,)), ((2,), (2,)), ((3,), (1,)),
        ((3,), (2,)), ((3,), (3,)), ((4,), (2,)), ((4,), (4,)),
        ((2,), (1, 1)), ((3,), (1, 1)), ((3,), (1, 1, 1)),
        ((2, 1), (3,)), ((1, 2), (3,)), ((2, 2), (2,)),
        ((2, 1), (1, 1, 1)), ((2, 2), (1, 1, 1)), ((3, 1), (2, 2)),
        ((1, 1), (1, 1)), ((2, 1), (2, 1)), ((5,), (3,)),
    ]
    print(f"{'pair':20s} {'true C':>10s} {'corrected':>10s} "
          f"{'zero':>10s} {'skip':>10s}")
    bad = 0
    for v, w in battery:
        t = true_C(v, w)
        cc = engine_C(v, w, "corrected")
        cz = engine_C(v, w, "zero")
        cs = engine_C(v, w, "skip")
        mark = "" if cc == t else "   <-- MISMATCH corrected vs true"
        if cc != t:
            bad += 1
        print(f"{str(v)+' '+str(w):20s} {str(t):>10s} {str(cc):>10s} "
              f"{str(cz):>10s} {str(cs):>10s}{mark}")
    print()
    if bad == 0:
        print("corrected mode agrees with the independent symbolic route "
              "on every pair in the battery")
    else:
        print(f"{bad} MISMATCHES between corrected mode and symbolic route")
    return bad


if __name__ == "__main__":
    sys.exit(0 if main() == 0 else 1)
