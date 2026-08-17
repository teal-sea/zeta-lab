"""Optimized inner sum for extending the corrected C_{kappa,i} tables.

This module patches bian_engine with a faster _s_sum. The mathematics is
unchanged: _s_sum computes the block-constrained sum

    S = (col factors) * sum over c,d of perm[(c_j + d_k + 1)!/(c_j! d_k!)]

by the same dynamic program over v-blocks, with exact reorganisations:

1. CANONICAL STATES. The DP state is the per-w-block vector of
   (slots left, budget left). Transitions distribute one v-block's slots
   and budget over the w-blocks, symmetrically in block position, and
   the acceptance condition (all zeros) is symmetric too, so the future
   of a state depends only on the MULTISET of (s, r) values. States are
   stored sorted; states that are permutations of one another merge.
   This is exact: the transition enumerates assignments to the
   (distinguishable) columns of the sorted tuple with the correct
   multiplicities, which is what the permanent requires.

2. RUN-GROUPED TRANSITIONS. Within a sorted state, equal (s, r) columns
   form runs of multiplicity mu. Distributing a v-block (a, b) over a
   run is enumerated by outcome counts rather than per position: an
   assignment giving outcome o to m_o columns arises in
   mu!/(prod_o m_o! (mu - sum m_o)!) ordered ways (accumulated as a
   product of binomials), the slot multinomial chain contributes
   a!/prod_o (n_o!)^{m_o} (the sequential product of binomials with the
   final remainder zero), and each outcome carries its P^{n_o}
   coefficient. This reproduces the per-position sum exactly with
   exponentially fewer branches.

3. DEAD-STATE PRUNING. Exhausted (0,0) columns are dropped; a column
   with slots 0 but budget > 0 can never drain (budget only travels on
   slot edges), so such states are discarded; a state whose remaining
   slot total differs from the remaining v-slot total cannot reach
   acceptance and is discarded.

Correctness gate: _s_sum_fast is checked against the stock _s_sum on
every signature pair arising in the corrected tables at small i, and the
full corrected rows/diagonal are recomputed and compared entry by entry
with coefficients.json (see selfcheck()). Run this module directly to
execute the gate.
"""

import os
import sys
from fractions import Fraction
from math import comb, factorial as fact

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import bian_engine as be

_STOCK_S_SUM = be._s_sum
_STOCK_PROF = be.prof_component


def _group_runs(st):
    """Sorted state tuple -> list of ((s, r), multiplicity)."""
    runs = []
    for val in st:
        if runs and runs[-1][0] == val:
            runs[-1] = (val, runs[-1][1] + 1)
        else:
            runs.append((val, 1))
    return runs


def _run_options(val, mu, amax, bmax, cmax, dmax):
    """All ways to hit one run of mu identical (s, r) columns with at
    most amax slots and bmax c-budget in total.

    Returns a list of (slots_used, budget_used, num, den, repl):
    num = prod_o comb-chain * w_o^{m_o} (integer), den = prod_o (n_o!)^{m_o},
    repl = tuple of (newvalue, count) for the non-identity columns.
    Includes the empty option (0, 0, 1, 1, ())."""
    s, r = val
    outs = []
    for n in range(1, min(s, amax) + 1):
        pn = be._p_pow(n, cmax, dmax)
        nf = fact(n)
        for c in range(0, bmax + 1):
            for d in range(0, r + 1):
                w = pn.get((c, d), 0)
                if w:
                    outs.append((n, c, d, w, nf, (s - n, r - d)))
    results = []

    def rec(idx, left_mu, aused, bused, num, den, repl):
        results.append((aused, bused, num, den, tuple(repl)))
        for j in range(idx, len(outs)):
            n, c, d, w, nf, newval = outs[j]
            wm = w
            nfm = nf
            for m in range(1, left_mu + 1):
                if aused + m * n > amax or bused + m * c > bmax:
                    break
                rec(j + 1, left_mu - m, aused + m * n, bused + m * c,
                    num * comb(left_mu, m) * wm,
                    den * nfm,
                    repl + [(newval, m)])
                wm *= w
                nfm *= nf
        return

    rec(0, mu, 0, 0, 1, 1, [])
    return results


def _s_sum_fast(vblocks, wblocks, btot):
    """Drop-in replacement for bian_engine._s_sum (exact, integer)."""
    cmax = dmax = max(btot, 1)
    wslots = sum(a for a, b in wblocks)
    vslots = sum(a for a, b in vblocks)
    if wslots != vslots:
        return 0
    state0 = tuple(sorted((a, b) for a, b in wblocks))
    # process larger v-blocks first: keeps intermediate state sets small
    vseq = sorted(vblocks, reverse=True)
    states = {state0: 1}
    remaining = vslots
    for (a, b) in vseq:
        remaining -= a
        new = {}
        for st, wt in states.items():
            runs = _group_runs(st)
            R = len(runs)
            opts = [_run_options(val, mu, a, b, cmax, dmax)
                    for val, mu in runs]
            sufcap = [0] * (R + 1)
            for ri in range(R - 1, -1, -1):
                (s, r), mu = runs[ri]
                sufcap[ri] = sufcap[ri + 1] + s * mu

            def rec(ri, arem, brem, num, den, acc):
                if ri == R:
                    if arem == 0 and brem == 0:
                        q, rem = divmod(num * fact(a), den)
                        if rem:
                            raise ArithmeticError("non-integer weight")
                        flat = []
                        for v2, m2 in acc:
                            if v2 != (0, 0):
                                if v2[0] == 0:      # dead: budget stranded
                                    return
                                flat.extend([v2] * m2)
                        key = tuple(sorted(flat))
                        new[key] = new.get(key, 0) + q * wt
                    return
                if sufcap[ri] < arem:
                    return
                val, mu = runs[ri]
                for (aused, bused, onum, oden, repl) in opts[ri]:
                    if aused > arem or bused > brem:
                        continue
                    ident = mu - sum(m for _v, m in repl)
                    add = list(repl)
                    if ident:
                        add.append((val, ident))
                    rec(ri + 1, arem - aused, brem - bused,
                        num * onum, den * oden, acc + add)

            rec(0, a, b, 1, 1, [])
        # prune states whose slot total cannot match the remaining v-slots
        states = {st: v for st, v in new.items()
                  if sum(s for s, r in st) == remaining}
        if not states:
            return 0
    total = states.get((), 0)
    for (a, b) in wblocks:
        total *= fact(a)
    return total


_bet_cache = {}


def _bet_poly(bet):
    """Expansion of prod_{i=1..len(bet)} (x_1+...+x_i)^{bet[i-1]} as a
    dict monomial-tuple (length len(bet)) -> integer coefficient."""
    if bet in _bet_cache:
        return _bet_cache[bet]
    J = len(bet)
    if J == 0:
        res = {(): 1}
    else:
        prev = _bet_poly(bet[:-1])
        # extend monomials by one position, then multiply (x_1+..+x_J)^b
        poly = {mono + (0,): cf for mono, cf in prev.items()}
        for _ in range(bet[-1]):
            newp = {}
            for mono, cf in poly.items():
                for j in range(J):
                    m2 = mono[:j] + (mono[j] + 1,) + mono[j + 1:]
                    newp[m2] = newp.get(m2, 0) + cf
            poly = newp
        res = poly
    _bet_cache[bet] = res
    return res


_prof_fast_cache = {}


def prof_component_fast(u, is_last):
    """Exact replacement for bian_engine.prof_component in the "zero"
    and "corrected" readings.

    In those readings every signature pair with alpha = 0 is dropped, so
    monomials supported on padding positions (positions past the
    composition's own support, where alpha = 0) never survive.  The
    expansion is therefore restricted to the J = len(alph) real
    positions: the is_last factor (x_1+...+x_V) truncates to
    (x_1+...+x_J) exactly, and the beta-expansion
    prod_i (x_1+...+x_i)^{beta_i} involves only positions <= len(bet)
    <= J.  Beta-expansions are memoized across compositions and across
    u (they do not depend on alph)."""
    if be.READING not in ("zero", "corrected"):
        return _STOCK_PROF(u, is_last)
    key = (u, is_last)
    if key in _prof_fast_cache:
        return _prof_fast_cache[key]
    out = {}
    for r in be.compositions(u):
        alph = r[0::2]
        bet = r[1::2]
        J = len(alph)
        poly = _bet_poly(bet)
        # pad monomials to J positions
        pad = J - len(bet)
        items = [(mono + (0,) * pad, cf) for mono, cf in poly.items()]
        if is_last:
            newp = {}
            for mono, cf in items:
                for j in range(J):
                    m2 = mono[:j] + (mono[j] + 1,) + mono[j + 1:]
                    newp[m2] = newp.get(m2, 0) + cf
            items = newp.items()
        for mono, cf in items:
            pairs = tuple(sorted(zip(alph, mono)))
            out[pairs] = out.get(pairs, 0) + cf
    _prof_fast_cache[key] = out
    return out


def install():
    """Patch bian_engine to use the fast inner sum and the fast
    component profiler (the latter is exact only for the zero/corrected
    readings and falls through to the stock version otherwise)."""
    be._s_sum = _s_sum_fast
    be.prof_component = prof_component_fast


def selfcheck(imax=14, kappas=(2, 3), do_diag=True, verbose=True):
    """Correctness gate: fast vs stock _s_sum on live signature pairs,
    plus full recomputation of the corrected tables up to imax against
    coefficients.json. Returns True iff everything matches."""
    import json
    import random
    ok = True

    # 0. fast vs stock prof_component in corrected mode
    be.READING = "corrected"
    be._prof_cache.clear()
    bad0 = 0
    for u in range(1, 14):
        for last in (False, True):
            if prof_component_fast(u, last) != _STOCK_PROF(u, last):
                bad0 += 1
                if verbose:
                    print(f"MISMATCH prof_component u={u} last={last}")
    if verbose:
        print(f"gate 0: fast vs stock prof_component, corrected, "
              f"u <= 13 both is_last: "
              f"{'all agree' if not bad0 else f'{bad0} BAD'}")
    ok &= (bad0 == 0)

    # 1. direct equivalence on the signature pairs the tables actually use
    seen = []
    orig_cons4 = be.cons4_sig

    def spy(sigv, sigw):
        if sigv > sigw:
            sigv, sigw = sigw, sigv
        seen.append((sigv, sigw))
        return orig_cons4(sigv, sigw)

    be.cons4_sig = spy
    try:
        for i in range(3, 12):
            for k in kappas:
                be.coefficient(i, k)
            if do_diag:
                be.diagonal(i)
    finally:
        be.cons4_sig = orig_cons4
    uniq = sorted(set(seen))
    random.seed(7)
    sample = uniq if len(uniq) <= 4000 else random.sample(uniq, 4000)
    bad = 0
    for sigv, sigw in sample:
        btv = sum(b for a, b in sigv)
        btw = sum(b for a, b in sigw)
        vb = tuple((a, b) for a, b in sigv if a > 0)
        wb = tuple((a, b) for a, b in sigw if a > 0)
        bt = max(btv, btw)
        if _STOCK_S_SUM(vb, wb, bt) != _s_sum_fast(vb, wb, bt):
            bad += 1
            if verbose:
                print("MISMATCH _s_sum:", sigv, sigw)
    if verbose:
        print(f"gate 1: fast vs stock _s_sum on {len(sample)} live "
              f"signature pairs: {'all agree' if not bad else f'{bad} BAD'}")
    ok &= (bad == 0)

    # 2. full corrected tables vs the committed checkpoint
    install()
    be._c4_cache.clear()
    be._consi_cache.clear()
    ck = json.load(open(os.path.join(HERE, "coefficients.json")))
    rows = ck["corrected"]["rows"]
    diag = ck["corrected"]["diagonal"]
    nchk = 0
    allok = True
    for i in range(1, imax + 1):
        for k in kappas:
            got = be.coefficient(i, k)
            want = Fraction(rows[str(k)][str(i)])
            if got != want:
                allok = False
                if verbose:
                    print(f"MISMATCH row kappa={k} i={i}: {got} != {want}")
            nchk += 1
        if do_diag:
            got = be.diagonal(i)
            want = Fraction(diag[str(i)])
            if got != want:
                allok = False
                if verbose:
                    print(f"MISMATCH diagonal i={i}: {got} != {want}")
            nchk += 1
    if verbose:
        print(f"gate 2: recomputed {nchk} corrected table entries "
              f"(kappa in {kappas}, diagonal={do_diag}, i <= {imax}) "
              f"against coefficients.json: "
              f"{'all agree' if allok else 'FAIL'}")
    ok &= allok
    return ok


if __name__ == "__main__":
    good = selfcheck()
    print("selfcheck:", "PASS" if good else "FAIL")
    sys.exit(0 if good else 1)
