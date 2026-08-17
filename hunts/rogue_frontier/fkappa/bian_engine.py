"""Exact recomputation of Bian's pair-correlation coefficients C_{kappa,i}.

Reference: Ji Bian, "The Pair Correlation of Zeros of xi^(kappa)(s)",
PhD thesis, University of Rochester, 2008 (advisor S. Gonek).  Under RH,
Theorem 1 of the thesis gives, for |alpha| < 1 and any fixed B,

    F_kappa(alpha,T) = (1+o(1)) T^{-2|alpha|} log T
                       + sum_{i=1}^{2 kappa B + 1} C_{kappa,i} |alpha|^i
                       + o_{kappa,B}(1),

and eq. (10.1) expresses, for i >= 3,

    C_{kappa,i} = 2^{i-1} sum_{l,k>=1} (-1)^{l+k}
                  sum_{|v_l|+|w_k| = i-1} theta(v_l,w_k) C(v_l,w_k),

where v_l, w_k run over integral vectors of dimensions l, k with components
in {1..kappa}, theta(v,w) = [max(l,k) <= min(|v|,|w|)], and C(v,w) is the
14-fold combinatorial sum of eq. (7.8) built from the inner constant
C(alpha,beta,alpha',beta') of eq. (6.23).  The values C_{kappa,1} = 1 and
C_{kappa,2} = -4 are universal (thesis Lemma 12); they come from analytic
main terms outside this combinatorial machinery (compare Farmer-Gonek,
arXiv:0803.0425, for kappa = 1) and are inserted as constants here.

This module contains two independent implementations:

1. A LITERAL PORT (functions ref_*) of the Mathematica code in Appendix A
   of the thesis (transcribed in bian_mathematica.txt), following the code
   line by line, including the double sum over permutation pairs in
   cons4vec.  It is exponentially slow and is used only as an oracle for
   small cases.

2. A FAST ENGINE built on four exact reorganisations, each of which is
   checked against the literal port by the self test:

   (a) The double permutation sum in (6.23) collapses:
       sum_{sigma,tau in S_m} prod_j (c_{sigma^-1(j)} + d_{tau^-1(j)} + 1)!
       = m! * perm[ (c_j + d_k + 1)! ]_{j,k}.

   (b) The E-matrix sums of (7.8) enter only through column sums btilde
       and the weight prod beta_i! / prod E_{ij}!, so they aggregate into
       multinomial coefficients: the generating polynomial
       prod_i (x_1 + ... + x_i)^{beta_i}   [times (x_1+...+x_V) for the
       last component, which carries the extra unit vector f].

   (c) C(v,w) depends on v only through (multiset of v_1..v_{l-1}, v_l)
       and is independent of kappa: every inner kappa-bound of the
       Appendix-A code (mclkapa, egenkapa, mycompositionkapa) is slack
       because all quantities it bounds are already <= max component of v
       <= kappa.  kappa enters only as the height bound on v and w.
       Consequently one aggregation over compositions serves every kappa.

   (d) The sum over (c,d) of the permanent in (a) is computed by an exact
       dynamic program over "blocks" (the positions j of the flat alpha
       vector), using coefficients of powers of
       P(y,z) = sum_{c,d} ((c+d+1)!/(c! d!)) y^c z^d.

   Signatures: after (b), each side of C(alpha,beta,alpha',beta') is
   determined by the multiset of pairs (alpha_j, btilde_j); the constant
   is cached on that canonical form.

READING FLAG.  The printed (6.23) sums c_i over E_{alpha_i}(beta_i).  When
alpha_j = 0 and btilde_j > 0 (this happens exactly when the extra unit
vector f of (7.8) lands on a padding position of an odd-length block),
E_0(btilde_j) is empty, so a literal reading of (6.23) makes the whole
term vanish.  Bian's code (fulllist / fulllistkapa) instead SKIPS such a
block (contributing an empty product, factor 1) while keeping btilde_j in
the norm |beta| and in prod beta_j!.  READING = "skip" reproduces the
code; READING = "zero" reproduces the literal formula.  The validation
grid decides which one produced Figure 10.1 (see RESULTS.md).

All arithmetic is exact (Python ints and fractions.Fraction).

Usage:
    .venv/bin/python hunts/rogue_frontier/fkappa/bian_engine.py --selftest
    .venv/bin/python hunts/rogue_frontier/fkappa/bian_engine.py --grid
    .venv/bin/python hunts/rogue_frontier/fkappa/bian_engine.py --extend IMAX
"""

import argparse
import itertools
import json
import os
import sys
import time
from collections import defaultdict
from fractions import Fraction
from math import comb, factorial as fact

HERE = os.path.dirname(os.path.abspath(__file__))

# Evaluation mode, see module docstring and RESULTS.md:
#   "skip":      Bian's Appendix-A code as written (reproduces Figure 10.1
#                together with coefficient_figure).
#   "zero":      the literal printed (6.23): E_0(beta>0) is empty, so terms
#                with a log on a phantom slot vanish.  Still carries the
#                prod alpha_i! overcount of (6.18).
#   "corrected": "zero" plus removal of the prod alpha_i! prod alpha'_i!
#                overcount of (6.18) (each side of (6.18) counts every
#                prime-to-block assignment prod alpha_i! times).  This is
#                the mathematically correct evaluation of C(v,w); it is
#                validated independently in validate_pairs.py.
READING = "skip"


# ----------------------------------------------------------------------
# shared small combinatorics
# ----------------------------------------------------------------------

def compositions(n, maxpart=None):
    """Ordered tuples of positive integers summing to n (parts <= maxpart)."""
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for first in range(1, min(n, maxpart) + 1):
        for rest in compositions(n - first, maxpart):
            yield (first,) + rest


def weak_compositions(n, k):
    """Ordered tuples of k nonnegative integers summing to n (E_k(n))."""
    if k == 0:
        if n == 0:
            yield ()
        return
    if k == 1:
        yield (n,)
        return
    for first in range(n + 1):
        for rest in weak_compositions(n - first, k - 1):
            yield (first,) + rest


# ======================================================================
# 1. LITERAL PORT of Appendix A (oracle; exponentially slow)
# ======================================================================

def ref_cons4vec(alfa1, beta1, alfa2, beta2):
    """Direct port of cons4vec: the constant C(alpha,beta,alpha',beta')
    of (6.23), with Bian's skip convention for alpha_j = 0 blocks."""
    m1, m2 = sum(alfa1), sum(alfa2)
    if m1 != m2:
        return Fraction(0)
    m = m1
    cons1 = fact(m) * fact(m + sum(beta1) + m2 + sum(beta2) - 1)

    def full_list(alfa, beta):
        # all flat c vectors: for each j with alfa[j] != 0 (j = 0 always
        # included; alfa[0] >= 1 in every reachable call), a block in
        # E_{alfa[j]}(beta[j])
        blocks = []
        for j, (a, b) in enumerate(zip(alfa, beta)):
            if j > 0 and a == 0:
                continue  # Bian's skip convention
            blocks.append(list(weak_compositions(b, a)))
        out = []
        for choice in itertools.product(*blocks):
            flat = tuple(x for blk in choice for x in blk)
            out.append(flat)
        return out

    tclist = full_list(alfa1, beta1)
    tdlist = full_list(alfa2, beta2)
    cons2 = 1
    for x in itertools.chain(alfa1, beta1, alfa2, beta2):
        cons2 *= fact(x)
    conssum = Fraction(0)
    perms = list(itertools.permutations(range(m)))
    for c in tclist:
        for d in tdlist:
            cons3 = 1
            for x in itertools.chain(c, d):
                cons3 *= fact(x)
            for sig in perms:
                # inversepermvec(sig, c)[i] = c[siginv[i]]
                siginv = [0] * m
                for i, s in enumerate(sig):
                    siginv[s] = i
                for tau in perms:
                    tauinv = [0] * m
                    for i, s in enumerate(tau):
                        tauinv[s] = i
                    cons4 = 1
                    for i in range(m):
                        cons4 *= fact(c[siginv[i]] + d[tauinv[i]] + 1)
                    conssum += Fraction(cons2 * cons4, cons3)
    return conssum / cons1


def ref_component_refinements(u, is_last):
    """All (alpha_block, btilde_block, weight) triples for one component,
    by direct enumeration of compositions and E-matrices (and f if last).
    weight = prod beta_i! / prod E_entries!  (consbeta * conse)."""
    V = (u + 1) // 2
    out = []
    for r in compositions(u):
        rp = r + (0,) * (u - len(r))
        alph = rp[0::2]                     # length V
        bet = list(rp[1::2]) + [0] * (V - len(rp[1::2]))
        rowsets = []
        for i in range(1, V + 1):
            rows = []
            for e in weak_compositions(bet[i - 1], i):
                rows.append(tuple(e) + (0,) * (V - i))
            rowsets.append(rows)
        for rows in itertools.product(*rowsets):
            wt = Fraction(1)
            for i in range(V):
                wt *= fact(bet[i])
            for row in rows:
                for x in row:
                    wt /= fact(x)
            base = [sum(row[j] for row in rows) for j in range(V)]
            if is_last:
                for fpos in range(V):
                    bt = list(base)
                    bt[fpos] += 1
                    out.append((alph, tuple(bt), wt))
            else:
                out.append((alph, tuple(base), wt))
    return out


def ref_C(v, w):
    """Direct port of sumgen/cons2vec: C(v,w) of eq. (7.8)."""
    lv, lw = len(v), len(w)
    nv, nw = sum(v), sum(w)
    if min(nv, nw) < max(lv, lw):
        return Fraction(0)   # theta(v,w) = 0

    def side_terms(vec):
        # all (flat alpha, flat btilde, weight) for one side
        per_comp = []
        for p, u in enumerate(vec):
            per_comp.append(ref_component_refinements(u, p == len(vec) - 1))
        out = []
        for choice in itertools.product(*per_comp):
            alpha = tuple(x for (a, b, wt) in choice for x in a)
            btld = tuple(x for (a, b, wt) in choice for x in b)
            wt = Fraction(1)
            for (a, b, w0) in choice:
                wt *= w0
            out.append((alpha, btld, wt))
        return out

    sv = side_terms(v)
    sw = side_terms(w)
    total = Fraction(0)
    for (a1, b1, w1) in sv:
        for (a2, b2, w2) in sw:
            if sum(a1) != sum(a2):
                continue
            total += w1 * w2 * ref_cons4vec(a1, b1, a2, b2)
    return total * (-1) ** (nv + nw)


def ref_consi(n, l, k, kapa):
    """consikapa: sum of C(v,w) over v of dim l, w of dim k, heights <= kapa,
    |v| + |w| = n."""
    total = Fraction(0)
    for m in range(l, n - k + 1):
        for v in compositions(m, min(m, kapa)):
            if len(v) != l:
                continue
            for w in compositions(n - m, min(n - m, kapa)):
                if len(w) != k:
                    continue
                total += ref_C(v, w)
    return total


def ref_finalconsikapa(n, kapa):
    """finalconsikapa: full double sum over 1 <= l, k with l + k <= n - 1."""
    total = Fraction(0)
    for l in range(1, n - 1):
        for k in range(1, n - l):
            total += (-1) ** (l + k) * ref_consi(n - 1, l, k, kapa)
    return Fraction(2) ** (n - 1) * total


def ref_cinfiopkapa(n, kapa):
    """cdiagkapa + coffdiagkapa, with Bian's exact loop bounds
    (including the j <= floor((n-i)/2) bound of coffdiagkapa)."""
    diag = Fraction(0)
    for i in range(1, (n - 1) // 2 + 1):
        diag += ref_consi(n - 1, i, i, kapa)
    diag *= Fraction(2) ** (n - 1)
    off = Fraction(0)
    for i in range(1, (n - 2) // 2 + 1):
        for j in range(i + 1, (n - i) // 2 + 1):
            off += (-1) ** (i + j) * ref_consi(n - 1, i, j, kapa)
    off *= Fraction(2) ** n
    return diag + off


# ======================================================================
# 2. FAST ENGINE
# ======================================================================
#
# A "signature" is the canonical form of one side of the inner constant:
# the sorted tuple of (alpha_j, btilde_j) pairs, with (0,0) pairs dropped.
# Side weights are integers (the E-sums aggregate to multinomials).

_prof_cache = {}


def prof_component(u, is_last):
    """dict: signature piece -> integer weight, for one component of value u.

    Enumerates compositions r of u; alpha = odd-position parts, beta =
    even-position parts; aggregates the E-matrix sum of (7.8) into the
    coefficient of x^btilde in prod_i (x_1+...+x_i)^{beta_i}
    (times (x_1+...+x_V) if is_last, for the unit vector f)."""
    key = (u, is_last, READING)
    if key in _prof_cache:
        return _prof_cache[key]
    V = (u + 1) // 2
    out = {}
    for r in compositions(u):
        rp = r + (0,) * (u - len(r))
        alph = rp[0::2]
        bet = list(rp[1::2]) + [0] * (V - len(rp[1::2]))
        poly = {(0,) * V: 1}
        for i in range(1, V + 1):
            for _ in range(bet[i - 1]):
                newp = defaultdict(int)
                for mono, cf in poly.items():
                    for j in range(i):
                        m2 = mono[:j] + (mono[j] + 1,) + mono[j + 1:]
                        newp[m2] += cf
                poly = newp
        if is_last:
            newp = defaultdict(int)
            for mono, cf in poly.items():
                for j in range(V):
                    m2 = mono[:j] + (mono[j] + 1,) + mono[j + 1:]
                    newp[m2] += cf
            poly = newp
        for mono, cf in poly.items():
            pairs = tuple(sorted(
                (alph[j], mono[j]) for j in range(V)
                if not (alph[j] == 0 and mono[j] == 0)))
            if READING in ("zero", "corrected") and \
                    any(a == 0 for (a, b) in pairs):
                continue
            out[pairs] = out.get(pairs, 0) + cf
    _prof_cache[key] = out
    return out


def _merge(d1, d2):
    """Convolution of two signature dicts (multiset union, weights multiply)."""
    out = defaultdict(int)
    for s1, w1 in d1.items():
        for s2, w2 in d2.items():
            out[tuple(sorted(s1 + s2))] += w1 * w2
    return dict(out)


_prefix_cache = {}


def prefix_agg(kapa, m, l):
    """Signature dict aggregated over ordered l-tuples of components
    (parts >= 1, <= kapa) with total m.  These are the first l components
    of a vector v (no f)."""
    kapa = min(kapa, m - l + 1) if l > 0 else 0
    key = (kapa, m, l, READING)
    if key in _prefix_cache:
        return _prefix_cache[key]
    if l == 0:
        res = {(): 1} if m == 0 else {}
    else:
        acc = defaultdict(int)
        for u in range(1, min(kapa, m - (l - 1)) + 1):
            sub = prefix_agg(kapa, m - u, l - 1)
            if not sub:
                continue
            pc = prof_component(u, False)
            for s1, w1 in sub.items():
                for s2, w2 in pc.items():
                    acc[tuple(sorted(s1 + s2))] += w1 * w2
        res = dict(acc)
    _prefix_cache[key] = res
    return res


_side_cache = {}


def side_agg(kapa, m, l):
    """Signature dict aggregated over all v of dimension l, norm m, height
    <= kapa; the last component carries the f vector."""
    kapa = min(kapa, m - l + 1)
    key = (kapa, m, l, READING)
    if key in _side_cache:
        return _side_cache[key]
    acc = defaultdict(int)
    for u in range(1, min(kapa, m - (l - 1)) + 1):
        pre = prefix_agg(kapa, m - u, l - 1)
        if not pre:
            continue
        pl = prof_component(u, True)
        for s1, w1 in pre.items():
            for s2, w2 in pl.items():
                acc[tuple(sorted(s1 + s2))] += w1 * w2
    res = dict(acc)
    _side_cache[key] = res
    return res


_ss_cache = {}


def side_signed(kapa, m, lmax):
    """sum_{l=1}^{lmax} (-1)^l side_agg(kapa, m, l), bucketed by |alpha|:
    dict malpha -> list of (sig, weight)."""
    kapa = min(kapa, m)
    key = (kapa, m, min(lmax, m), READING)
    if key in _ss_cache:
        return _ss_cache[key]
    acc = defaultdict(int)
    for l in range(1, min(lmax, m) + 1):
        sgn = -1 if l % 2 else 1
        for s, w in side_agg(kapa, m, l).items():
            acc[s] += sgn * w
    buckets = defaultdict(list)
    for s, w in acc.items():
        if w:
            buckets[sum(a for a, b in s)].append((s, w))
    res = dict(buckets)
    _ss_cache[key] = res
    return res


# ---- inner constant C(alpha,beta,alpha',beta') from signatures ----------

_ppow_cache = {}
_PMAX = 40  # truncation degree for P(y,z); raised automatically if needed


def _p_pow(n, cmax, dmax):
    """dict (c,d) -> coefficient of y^c z^d in P(y,z)^n, where
    P(y,z) = sum_{c,d>=0} ((c+d+1)!/(c! d!)) y^c z^d."""
    key = (n, cmax, dmax)
    if key in _ppow_cache:
        return _ppow_cache[key]
    if n == 0:
        res = {(0, 0): 1}
    elif n == 1:
        res = {}
        for c in range(cmax + 1):
            for d in range(dmax + 1):
                res[(c, d)] = fact(c + d + 1) // (fact(c) * fact(d))
    else:
        half = _p_pow(n // 2, cmax, dmax)
        other = _p_pow(n - n // 2, cmax, dmax)
        res = defaultdict(int)
        for (c1, d1), v1 in half.items():
            for (c2, d2), v2 in other.items():
                if c1 + c2 <= cmax and d1 + d2 <= dmax:
                    res[(c1 + c2, d1 + d2)] += v1 * v2
        res = dict(res)
    _ppow_cache[key] = res
    return res


def _s_sum(vblocks, wblocks, btot):
    """S = sum over c,d (block-constrained) of perm[(c_j+d_k+1)!/(c_j! d_k!)].

    vblocks, wblocks: tuples of (a, b) with a >= 1; sum of a equal on both
    sides.  Exact DP: process v-blocks; state = per-w-block (slots left,
    budget left); transitions distribute a v-block's a edges and its
    c-budget b across w-blocks, drawing d-budget, with coefficient
    binom-multinomial * coeff of P^n."""
    cmax = dmax = max(btot, 1)
    state0 = tuple(wblocks)
    states = {state0: 1}
    for (a, b) in vblocks:
        new = defaultdict(int)
        for st, wt in states.items():
            W = len(st)

            # depth-first distribution over w-blocks
            def rec(j, arem, brem, stl, acc):
                if j == W:
                    if arem == 0 and brem == 0:
                        new[tuple(stl)] += wt * acc
                    return
                s_j, r_j = st[j]
                # remaining capacity check
                cap = sum(st[t][0] for t in range(j, W))
                if cap < arem:
                    return
                for n_j in range(0, min(arem, s_j) + 1):
                    if n_j == 0:
                        rec(j + 1, arem, brem, stl + [(s_j, r_j)], acc)
                        continue
                    mult = comb(arem, n_j)
                    pn = _p_pow(n_j, cmax, dmax)
                    for cpart in range(0, brem + 1):
                        for dpart in range(0, r_j + 1):
                            cf = pn.get((cpart, dpart), 0)
                            if cf:
                                rec(j + 1, arem - n_j, brem - cpart,
                                    stl + [(s_j - n_j, r_j - dpart)],
                                    acc * mult * cf)
            rec(0, a, b, [], 1)
        states = new
        if not states:
            return 0
    end = tuple((0, 0) for _ in wblocks)
    total = states.get(end, 0)
    for (a, b) in wblocks:
        total *= fact(a)
    return total


_c4_cache = {}


def cons4_sig(sigv, sigw):
    """The inner constant C(alpha,beta,alpha',beta') of (6.23) from the two
    side signatures.  Uses the m!*permanent collapse and the block DP."""
    if sigv > sigw:
        sigv, sigw = sigw, sigv
    corrected = (READING == "corrected")
    key = (sigv, sigw, corrected)
    val = _c4_cache.get(key)
    if val is not None:
        return val
    m = sum(a for a, b in sigv)
    btv = sum(b for a, b in sigv)
    btw = sum(b for a, b in sigw)
    f0 = 1
    for a, b in itertools.chain(sigv, sigw):
        f0 *= fact(b) if corrected else fact(a) * fact(b)
    denom = fact(2 * m + btv + btw - 1)
    vb = tuple((a, b) for a, b in sigv if a > 0)
    wb = tuple((a, b) for a, b in sigw if a > 0)
    s = _s_sum(vb, wb, max(btv, btw))
    val = Fraction(f0 * s, denom)
    _c4_cache[key] = val
    return val


def _pair_total(bucketsv, bucketsw):
    total = Fraction(0)
    for ma, itemsv in bucketsv.items():
        itemsw = bucketsw.get(ma)
        if not itemsw:
            continue
        for sv, wv in itemsv:
            for sw, ww in itemsw:
                c4 = cons4_sig(sv, sw)
                if c4:
                    total += wv * ww * c4
    return total


def coefficient(i, kapa):
    """C_{kappa,i} exactly.  i >= 3 from eq. (10.1) (l,k >= 1 part);
    i = 1, 2 are the universal constants of Lemma 12."""
    if i == 1:
        return Fraction(1)
    if i == 2:
        return Fraction(-4)
    n = i - 1
    total = Fraction(0)
    for m in range(1, n // 2 + 1):
        mw = n - m
        j0 = m  # = min(m, n-m); theta caps both dimensions at j0
        bv = side_signed(kapa, m, j0)
        bw = side_signed(kapa, mw, j0)
        contrib = _pair_total(bv, bw)
        total += contrib * (1 if m == mw else 2)
    sign = -1 if n % 2 else 1
    return Fraction(2) ** (i - 1) * sign * total


def diagonal(i):
    """The stable value C_{(i-2),i} = C_{kappa,i} for all kappa >= i-2."""
    return coefficient(i, i - 2 if i > 2 else 1)


def C_pair(v, w):
    """C(v,w) for one specific pair, via the signature machinery (respects
    the READING flag).  theta is applied as in cons2vec."""
    lv, lw = len(v), len(w)
    nv, nw = sum(v), sum(w)
    if min(nv, nw) < max(lv, lw):
        return Fraction(0)

    def side(vec):
        d = {(): 1}
        for p, u in enumerate(vec):
            d = _merge(d, prof_component(u, p == len(vec) - 1))
        return d

    total = _pair_total(_bucket(side(v)), _bucket(side(w)))
    return total * (-1) ** (nv + nw)


# ---- the assembly Bian's ctablefull actually used (cinfiopkapa) --------

def _bucket(d):
    buckets = defaultdict(list)
    for s, w in d.items():
        if w:
            buckets[sum(a for a, b in s)].append((s, w))
    return dict(buckets)


_consi_cache = {}


def consi_fast(n, l, k, kapa):
    """consikapa(n, l, k, kapa): sum of theta(v,w) C(v,w) over v of dim l,
    w of dim k, |v|+|w| = n, heights <= kapa.  Fast signature version."""
    kapa = min(kapa, n)
    key = (n, l, k, kapa, READING)
    if key in _consi_cache:
        return _consi_cache[key]
    total = Fraction(0)
    for m in range(l, n - k + 1):
        if min(m, n - m) < max(l, k):
            continue  # theta = 0
        bv = _bucket(side_agg(kapa, m, l))
        bw = _bucket(side_agg(kapa, n - m, k))
        total += _pair_total(bv, bw)
    sign = -1 if n % 2 else 1
    total *= sign  # the (-1)^{|v|+|w|} factor inside C(v,w)
    _consi_cache[key] = total
    return total


def coefficient_figure(i, kapa):
    """C_{kappa,i} as computed by the thesis code that generated Figure
    10.1: cinfiopkapa(i,kapa) = cdiagkapa + coffdiagkapa, with Bian's
    off-diagonal loop bound j <= floor((i-l)/2), which for i >= 7 and
    kappa >= 2 drops nonzero (l,k) pairs that eq. (10.1) includes.
    i = 1, 2 as in coefficient()."""
    if i == 1:
        return Fraction(1)
    if i == 2:
        return Fraction(-4)
    diag = Fraction(0)
    for l in range(1, (i - 1) // 2 + 1):
        diag += consi_fast(i - 1, l, l, kapa)
    diag *= Fraction(2) ** (i - 1)
    off = Fraction(0)
    for l in range(1, (i - 2) // 2 + 1):
        for k in range(l + 1, (i - l) // 2 + 1):
            off += (-1) ** (l + k) * consi_fast(i - 1, l, k, kapa)
    off *= Fraction(2) ** i
    return diag + off


def diagonal_figure(i):
    return coefficient_figure(i, i - 2 if i > 2 else 1)


# ======================================================================
# validation grid (Figure 10.1 of the thesis, OCR-recovered; the kappa=1
# row is independently pinned by Farmer-Gonek's closed form)
# ======================================================================

F = Fraction
GRID = {
    1: [F(1), F(-4), F(4), F(0), F(4, 3), F(0), F(16, 45), F(0),
        F(8, 105), F(0), F(64, 4725)],
    2: [F(1), F(-4), F(4), F(-16), F(28), F(16), F(544, 45), F(-512, 45),
        F(-104, 63), F(-416, 945), F(6688, 1575)],
    3: [F(1), F(-4), F(4), F(-16), F(332, 5), F(-448, 3), F(81296, 315),
        F(75512, 315), F(17104, 2835), F(-219808, 2025), F(1350848, 10395)],
    4: [F(1), F(-4), F(4), F(-16), F(332, 5), F(-224), F(189584, 315),
        F(-382024, 315), F(1414256, 945), F(28355392, 14175),
        F(-4107904, 17325)],
    5: [None, None, None, None, F(332, 5), F(-224), F(241424, 315),
        F(-628984, 315), F(13985488, 2835), F(-130365376, 14175),
        F(230016448, 17325)],
    6: [None, None, None, None, None, None, F(241424, 315),
        F(-729784, 315), F(2636464, 405), F(-33067072, 2025),
        F(19849664, 525)],
    7: [None, None, None, None, None, None, None, None,
        F(2912944, 405), F(-40013632, 2025), F(557267264, 10395)],
    8: [None, None, None, None, None, None, None, None, None,
        F(-42709312, 2025), F(628230464, 10395)],
    9: [None, None, None, None, None, None, None, None, None, None,
        F(657260864, 10395)],
}


def farmer_gonek_row(imax):
    """kappa = 1 closed form: |a| - 4 a^2 + sum_k ((k-1)!/(2k)!) (2|a|)^{2k+1}."""
    row = {1: F(1), 2: F(-4)}
    for i in range(3, imax + 1):
        if i % 2 == 1:
            k = (i - 1) // 2
            row[i] = Fraction(fact(k - 1) * 2 ** i, fact(2 * k))
        else:
            row[i] = F(0)
    return row


# ======================================================================
# drivers
# ======================================================================

def selftest(verbose=True):
    """Cross-check the fast engine against the literal port on small cases,
    and both against hand-checked values."""
    ok = True

    def chk(name, got, want):
        nonlocal ok
        good = got == want
        if not good:
            ok = False
        if verbose:
            print(f"  {'ok ' if good else 'FAIL'} {name}: {got}"
                  + ("" if good else f" (want {want})"))

    # inner constant, hand-checked values
    chk("cons4vec((1),(1);(1),(1))",
        ref_cons4vec((1,), (1,), (1,), (1,)), F(1))
    chk("cons4vec((1),(1);(1),(2))",
        ref_cons4vec((1,), (1,), (1,), (2,)), F(1))

    # fast cons4 vs literal cons4 on assorted signatures
    cases = [
        (((1, 1),), ((1, 1),)),
        (((1, 1),), ((1, 2),)),
        (((2, 1),), ((1, 1), (1, 0))),
        (((2, 0), (1, 2)), ((1, 1), (2, 1))),
        (((1, 0), (1, 1), (1, 1)), ((3, 2),)),
        (((0, 1), (3, 0)), ((1, 1), (2, 0))),
        (((2, 2),), ((1, 0), (1, 2))),
    ]
    for sigv, sigw in cases:
        a1 = tuple(a for a, b in sigv)
        b1 = tuple(b for a, b in sigv)
        a2 = tuple(a for a, b in sigw)
        b2 = tuple(b for a, b in sigw)
        if sum(a1) != sum(a2):
            continue
        # literal port needs alpha[0] != 0; reorder so a nonzero leads
        def lead(a, b):
            idx = sorted(range(len(a)), key=lambda j: -a[j])
            return tuple(a[j] for j in idx), tuple(b[j] for j in idx)
        a1o, b1o = lead(a1, b1)
        a2o, b2o = lead(a2, b2)
        chk(f"cons4 {sigv} vs {sigw}",
            cons4_sig(tuple(sorted(zip(a1, b1))), tuple(sorted(zip(a2, b2)))),
            ref_cons4vec(a1o, b1o, a2o, b2o))

    # C(v,w) fast-vs-literal through full coefficient assembly
    for (i, kapa) in [(3, 1), (4, 1), (4, 2), (5, 1), (5, 2), (5, 3),
                      (6, 1), (6, 2), (6, 3), (7, 2)]:
        chk(f"C_(kappa={kapa}, i={i}) engine vs literal finalconsikapa",
            coefficient(i, kapa), ref_finalconsikapa(i, kapa))

    # grid spot checks
    chk("C_(1,5) = 4/3", coefficient(5, 1), F(4, 3))
    chk("C_(2,5) = 28", coefficient(5, 2), F(28))
    chk("C_(3,5) = 332/5", coefficient(5, 3), F(332, 5))

    # corrected-mode spot checks (see validate_pairs.py / closed_form.py
    # for the full battery)
    global READING
    saved = READING
    try:
        READING = "corrected"
        chk("corrected C((2),(2)) = 4/3", C_pair((2,), (2,)), F(4, 3))
        chk("corrected C((3),(1)) = 1", C_pair((3,), (1,)), F(1))
        chk("corrected C((3),(3)) = 9/5", C_pair((3,), (3,)), F(9, 5))
        chk("corrected C_(2,5) = 52/3 "
            "(= 16*(4/3 - 2/6 + 1/12))", coefficient(5, 2), F(52, 3))
        chk("corrected C_(1,7) = FG 16/45", coefficient(7, 1), F(16, 45))
    finally:
        READING = saved
    return ok


def grid_check(imax=11, kmax=9):
    """Recompute the full Figure 10.1 grid with BOTH assemblies; report
    agreement cell by cell.  Returns mismatches of the figure assembly
    (coefficient_figure) against the OCR grid, which is the reproduction
    claim; differences between the two assemblies are reported separately."""
    mism_fig = []
    mism_101 = []
    diffs = []
    t0 = time.time()
    for kapa in range(1, kmax + 1):
        row = []
        for i in range(1, imax + 1):
            cf = coefficient_figure(i, kapa)
            c1 = coefficient(i, kapa)
            row.append(cf)
            if cf != c1:
                diffs.append((kapa, i, cf, c1))
            want = None
            if kapa in GRID and i <= len(GRID[kapa]):
                want = GRID[kapa][i - 1]
            if want is not None:
                if cf != want:
                    mism_fig.append((kapa, i, cf, want))
                if c1 != want:
                    mism_101.append((kapa, i, c1, want))
        print(f"kappa={kapa}: " + ", ".join(str(x) for x in row)
              + f"   [{time.time()-t0:.1f}s]")
    # Lemma 12 stabilisation: row kappa >= i-2 equals the diagonal
    for i in range(3, imax + 1):
        d = diagonal(i)
        for kapa in range(max(1, i - 2), kmax + 1):
            c = coefficient(i, kapa)
            if c != d:
                mism_fig.append(("diag", i, c, d))
    fg = farmer_gonek_row(imax)
    for i in range(1, imax + 1):
        for c, tag in [(coefficient(i, 1), "FG vs (10.1)"),
                       (coefficient_figure(i, 1), "FG vs figure")]:
            if c != fg[i]:
                mism_fig.append((tag, i, c, fg[i]))
    print(f"\nfigure assembly (cinfiopkapa) vs OCR grid: "
          f"{'ALL CELLS MATCH' if not mism_fig else mism_fig}")
    print(f"eq (10.1) assembly vs OCR grid: "
          f"{len(mism_101)} mismatching cells "
          f"{[(k, i) for (k, i, a, b) in mism_101]}")
    print(f"cells where the two assemblies differ: "
          f"{[(k, i) for (k, i, a, b) in diffs]}")
    for (k, i, cf, c1) in diffs:
        print(f"  kappa={k} i={i}: figure={cf}  (10.1)={c1}  "
              f"delta={c1 - cf}")
    return mism_fig


CKPT = os.path.join(HERE, "coefficients.json")


def load_ckpt():
    """Checkpoint schema: top-level key per evaluation mode ("skip",
    "corrected", ...); under it rows / rows_figure / diagonal /
    diagonal_figure / timing."""
    if os.path.exists(CKPT):
        with open(CKPT) as f:
            data = json.load(f)
        if "rows" in data:  # migrate old flat (skip-mode) schema
            data = {data.get("reading", "skip"):
                    {k: v for k, v in data.items() if k != "reading"}}
        return data
    return {}


def save_ckpt(data):
    tmp = CKPT + ".tmp"
    with open(tmp, "w") as f:
        json.dump(data, f, indent=1, sort_keys=True)
    os.replace(tmp, CKPT)


def extend(imax, kappas=(1, 2, 3, 4, 5, 6), imin=1):
    """Extend the table to i = imax for the given kappa rows plus the stable
    diagonal, in BOTH assemblies, checkpointing to coefficients.json level
    by level.  rows/diagonal = eq (10.1) full double sum;
    rows_figure/diagonal_figure = the thesis-code assembly (cinfiopkapa)."""
    alldata = load_ckpt()
    data = alldata.setdefault(READING, {})
    for k in ("rows", "rows_figure", "diagonal", "diagonal_figure",
              "timing"):
        data.setdefault(k, {})
    for i in range(imin, imax + 1):
        t0 = time.time()
        d = diagonal(i)  # computes the most expensive column first
        data["diagonal"][str(i)] = str(d)
        df = diagonal_figure(i)
        data["diagonal_figure"][str(i)] = str(df)
        for kapa in kappas:
            data["rows"].setdefault(str(kapa), {})[str(i)] = \
                str(coefficient(i, kapa))
            data["rows_figure"].setdefault(str(kapa), {})[str(i)] = \
                str(coefficient_figure(i, kapa))
        dt = time.time() - t0
        data["timing"][str(i)] = round(dt, 2)
        save_ckpt(alldata)
        print(f"i={i:2d}  diag={d}  diag_fig={df}  "
              f"[{dt:.1f}s, c4 cache {len(_c4_cache)}]", flush=True)
    return alldata


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--grid", action="store_true")
    ap.add_argument("--grid-imax", type=int, default=11)
    ap.add_argument("--extend", type=int, metavar="IMAX")
    ap.add_argument("--imin", type=int, default=1)
    ap.add_argument("--reading", choices=["skip", "zero", "corrected"],
                    default="skip")
    args = ap.parse_args()
    global READING
    READING = args.reading
    if args.selftest:
        ok = selftest()
        print("selftest:", "PASS" if ok else "FAIL")
        sys.exit(0 if ok else 1)
    if args.grid:
        mism = grid_check(imax=args.grid_imax)
        sys.exit(1 if mism else 0)
    if args.extend:
        extend(args.extend, imin=args.imin)


if __name__ == "__main__":
    main()
