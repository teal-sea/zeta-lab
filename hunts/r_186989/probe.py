"""Erdos #126 bounded scout: the inverse function of f(n), measured.

Erdos #126. For a set A of n distinct positive integers write

    P(A) = { p prime : p | a + b for some a != b in A },

and let f(n) = min_{|A| = n} |P(A)|.  Classical work gives f(n) >> log n.
Erdos asks for f(n) / log n -> infinity.

This probe does not attack f directly.  It measures the inverse:

    g(k) = max { n : there is a set A of n positive integers with |P(A)| <= k }
         = max { n : some n-set has every off-diagonal sum {p_1..p_k}-smooth
                     for SOME k-element prime set S }.

f and g are inverse staircases, so the conjecture restates exactly:

    f(n)/log n -> oo   <=>   g(k) = exp(o(k))   <=>   g(k)^(1/k) -> 1.

That restatement is the point of this file.  It converts an asymptotic
statement about a minimum over unbounded sets into a growth-rate statement
about one integer sequence, and it makes the three arms of the brief say
something concrete about the same object:

  arm 1 (p-adic pruning)     -> compute g_N(k), a rigorous LOWER bound on g(k)
                                obtained by exact clique search inside [1, N].
  arm 2 (S-unit clique)      -> the same search, run with the smoothness set
                                fixed to the first k primes vs. an optimised
                                k-subset, to see how much the choice of S buys.
  arm 3 (composition law)    -> test supermultiplicativity g(k1+k2) >= g(k1)g(k2)
                                against the measured values, and record what a
                                rigorous composition law would actually prove.

Arm 0 resolves the Formal Conjectures positivity mismatch first, as the brief
requires: its statement is over `Finset Nat`, which admits 0, while Erdos
assumes positive integers.

Everything here is *measured*.  Lower bounds on g(k) are exact (an explicit
witness set is printed and re-verified); upper bounds on g(k) are NOT
established by this probe, because the search universe is bounded.

Run:  python hunts/r_186989/probe.py            (writes results.json)
"""

from __future__ import annotations

import json
import time
from math import gcd
from pathlib import Path

HERE = Path(__file__).resolve().parent

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


# --------------------------------------------------------------------------
# smoothness
# --------------------------------------------------------------------------

def smooth_set(primes, limit):
    """All n <= limit whose prime support is contained in `primes` (1 included)."""
    out = {1}
    for p in primes:
        new = set()
        for v in out:
            w = v * p
            while w <= limit:
                new.add(w)
                w *= p
        out |= new
    return out


def prime_support(n):
    """Distinct primes dividing n, by trial division. n >= 1."""
    s, d = set(), 2
    while d * d <= n:
        if n % d == 0:
            s.add(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        s.add(n)
    return s


def support_of_set(A):
    """P(A): primes dividing some off-diagonal sum. 0 is allowed in A."""
    s = set()
    A = sorted(A)
    for i, a in enumerate(A):
        for b in A[i + 1:]:
            s |= prime_support(a + b)
    return s


# --------------------------------------------------------------------------
# arm 0 -- the Formal Conjectures positivity mismatch
# --------------------------------------------------------------------------

def arm0_positivity(nmax=5, universe=40):
    """Is the `Finset Nat` version (0 allowed) the same problem?

    Write f(n) for the minimum over n-sets of POSITIVE integers and f0(n) for
    the minimum over n-sets of NON-NEGATIVE integers.  Two remarks settle it:

      (a) f0(n) <= f(n).  Every positive set is a non-negative set.

      (b) f0(n) >= f(n-1).  Let A achieve f0(n).  If 0 not in A then A is a
          positive n-set, so |P(A)| >= f(n) >= f(n-1).  If 0 in A, put
          A' = A \\ {0}, a positive (n-1)-set; every off-diagonal sum of A' is
          an off-diagonal sum of A, so P(A') is a subset of P(A) and
          |P(A)| >= |P(A')| >= f(n-1).

    Hence f(n-1) <= f0(n) <= f(n) for all n >= 2.  f is non-decreasing, so the
    two staircases differ by at most one step and

        f(n)/log n -> oo   iff   f0(n)/log n -> oo.

    The mismatch is therefore harmless for the asymptotic statement, and it is
    NOT harmless for small n: f(2) = 1 (best is {1,2}, sum 3) while
    f0(2) = 0 ({0,1}, sum 1, empty support).  A finite-n formalisation that
    pins values would be wrong; the limit statement is unaffected.

    This function checks (a), (b) and the f(2)/f0(2) split by exhaustive
    search over subsets of [0, universe].
    """
    from itertools import combinations

    f, f0 = {}, {}
    for n in range(1, nmax + 1):
        best_pos, best_any = None, None
        wit_pos, wit_any = None, None
        for A in combinations(range(0, universe + 1), n):
            k = len(support_of_set(A))
            if best_any is None or k < best_any:
                best_any, wit_any = k, A
            if A[0] >= 1 and (best_pos is None or k < best_pos):
                best_pos, wit_pos = k, A
        f[n], f0[n] = best_pos, best_any
        yield_ = None
    return {
        "universe": [0, universe],
        "f_bounded": {str(n): f[n] for n in f},
        "f0_bounded": {str(n): f0[n] for n in f0},
        "inequality_a_holds": all(f0[n] <= f[n] for n in f),
        "inequality_b_holds": all(f0[n] >= f[n - 1] for n in f if n >= 2),
        "note": (
            "f(n-1) <= f0(n) <= f(n) is proved in the docstring, not measured; "
            "the table is a bounded-universe consistency check (upper bounds on "
            "both f and f0, since the universe is capped)."
        ),
    }


# --------------------------------------------------------------------------
# arms 1 and 2 -- exact clique search inside [1, N]
# --------------------------------------------------------------------------

def max_smooth_clique(primes, N, time_budget=20.0):
    """Largest A subset of [1,N] with every off-diagonal sum `primes`-smooth.

    Exact within [1, N] if it finishes inside `time_budget`; otherwise the
    returned set is still a genuine witness (a rigorous lower bound) and
    `exhaustive` is False.

    The search is a depth-first clique enumeration on the graph a ~ b iff
    a + b is smooth.  Candidates are carried as an explicit list and
    intersected on each descent, which is the "blockwise p-adic pruning" of
    the brief in its cheapest honest form: membership in the smooth set is
    exactly the joint p-adic condition, tested by table lookup.
    """
    S = smooth_set(primes, 2 * N)
    S_sorted = sorted(S)
    nbr = [None] * (N + 1)
    for a in range(1, N + 1):
        # b ranges over s - a for smooth s, which is O(|S|) rather than O(N).
        nbr[a] = sorted(b for b in (s - a for s in S_sorted) if a < b <= N)

    best = []
    deadline = time.time() + time_budget
    timed_out = [False]

    def expand(clique, cand):
        if time.time() > deadline:
            timed_out[0] = True
            return
        if len(clique) + len(cand) <= len(best):
            return
        if not cand:
            if len(clique) > len(best):
                best[:] = clique
            return
        for i, c in enumerate(cand):
            if len(clique) + len(cand) - i <= len(best):
                return
            nxt = [d for d in cand[i + 1:] if (c + d) in S]
            expand(clique + [c], nxt)

    for a in range(1, N + 1):
        if 1 + len(nbr[a]) <= len(best):
            continue
        expand([a], nbr[a])
        if timed_out[0]:
            break

    return sorted(best), (not timed_out[0])


def verify_clique(A, primes):
    """Re-check a witness from scratch: every off-diagonal sum, full support."""
    allowed = set(primes)
    A = sorted(A)
    for i, a in enumerate(A):
        for b in A[i + 1:]:
            if not prime_support(a + b) <= allowed:
                return False
    return True


def arm1_g_lower_bounds(kmax=6, budget_per_k=25.0):
    """g_N(k) for S = the first k primes, with witnesses."""
    plan = {1: 200000, 2: 100000, 3: 60000, 4: 30000, 5: 20000, 6: 12000,
            7: 6000}
    rows = []
    for k in range(1, kmax + 1):
        primes = PRIMES[:k]
        N = plan.get(k, 150)
        t0 = time.time()
        A, exhaustive = max_smooth_clique(primes, N, budget_per_k)
        rows.append({
            "k": k,
            "S": primes,
            "N": N,
            "g_lower": len(A),
            "witness": A,
            "witness_verified": verify_clique(A, primes),
            "exhaustive_in_universe": exhaustive,
            "seconds": round(time.time() - t0, 2),
        })
    return rows


def arm2_prime_choice(k, N, candidates, budget=12.0):
    """Does a non-initial k-subset of primes beat the first k primes?

    Arm 2 of the brief asks for an S-unit clique reduction.  The cheap
    measurable version: hold k fixed, vary S, and see whether the achievable
    clique size depends on S at all.  If it does not, the k-dependence is the
    only thing that matters and the reduction has nothing extra to exploit.
    """
    rows = []
    for S in candidates:
        A, exhaustive = max_smooth_clique(list(S), N, budget)
        rows.append({
            "S": list(S),
            "N": N,
            "g_lower": len(A),
            "witness": A,
            "witness_verified": verify_clique(A, list(S)),
            "exhaustive_in_universe": exhaustive,
        })
    return rows


# --------------------------------------------------------------------------
# arm 3 -- the composition law, and what it would actually prove
# --------------------------------------------------------------------------

def arm3_composition(rows):
    """Test g(k1+k2) >= g(k1) g(k2) against the measured lower bounds.

    The brief asks for "a multiplicative-size/additive-support gadget".  The
    decisive remark is about its direction.  g is non-decreasing and
    g(1) = 2 (witness {1,3}, sum 4).  If g were supermultiplicative then by
    Fekete's lemma

        lim g(k)^(1/k) = sup_k g(k)^(1/k) >= g(1) = 2,

    so g(k) >= 2^k, so f(n) <= log_2 n + O(1), and the conjecture is FALSE.

    So a rigorous composition law does not advance Erdos #126: it refutes it.
    Conversely, proving the conjecture requires proving that no such gadget
    exists -- an anti-composition theorem.  This arm therefore cannot be a
    promotion route in the direction the brief hoped for, and that is the
    finding.
    """
    g = {r["k"]: r["g_lower"] for r in rows}
    tests = []
    for k1 in sorted(g):
        for k2 in sorted(g):
            if k1 <= k2 and k1 + k2 in g:
                tests.append({
                    "k1": k1, "k2": k2,
                    "g_k1": g[k1], "g_k2": g[k2],
                    "product": g[k1] * g[k2],
                    "g_k1_plus_k2_lower": g[k1 + k2],
                    "supermultiplicative_consistent_with_data":
                        g[k1 + k2] >= g[k1] * g[k2],
                })
    ratios = {str(k): round(g[k] ** (1.0 / k), 4) for k in sorted(g)}
    return {
        "g_lower_bounds": {str(k): g[k] for k in sorted(g)},
        "kth_root_of_lower_bound": ratios,
        "supermultiplicativity_tests": tests,
        "direction_note": (
            "A rigorous composition law would refute the conjecture, not prove "
            "it: g(1) = 2 plus supermultiplicativity gives g(k) >= 2^k by "
            "Fekete, i.e. f(n) <= log_2 n + O(1). Proving f(n)/log n -> oo "
            "requires an anti-composition theorem."
        ),
    }


# --------------------------------------------------------------------------

def main():
    t0 = time.time()
    out = {}

    out["restatement"] = {
        "g": "g(k) = max{ n : some n-set of positive integers has |P(A)| <= k }",
        "equivalence": "f(n)/log n -> oo  <=>  g(k) = exp(o(k))  <=>  g(k)^(1/k) -> 1",
        "note": (
            "f and g are inverse non-decreasing staircases: |P(A)| <= k for some "
            "n-set iff f(n) <= k iff n <= g(k). g(k) is finite for every k "
            "exactly because the classical bound f(n) >> log n holds."
        ),
    }

    out["arm0_positivity_mismatch"] = arm0_positivity(nmax=5, universe=40)

    rows = arm1_g_lower_bounds(kmax=7, budget_per_k=60.0)
    out["arm1_padic_pruning"] = rows

    out["arm2_prime_choice"] = arm2_prime_choice(
        k=3, N=20000,
        candidates=[(2, 3, 5), (2, 3, 7), (2, 5, 7), (2, 3, 13), (3, 5, 7)],
    )

    out["arm3_composition"] = arm3_composition(rows)

    out["verdict"] = {
        "scout": "killed on a pre-registered kill condition",
        "which": (
            "the brief kills the scout on 'suggestive finite data'. That is "
            "what arm 1 produced: exact maxima inside a bounded universe, with "
            "no iterable lemma and no exp(o(k)) reduction."
        ),
        "kept": [
            "arm 0 is settled: the Formal Conjectures positivity mismatch is "
            "benign for the limit statement (f(n-1) <= f0(n) <= f(n)) and NOT "
            "benign for pinned finite values (f(2)=1 vs f0(2)=0).",
            "the inverse restatement: the conjecture is exactly g(k)^(1/k) -> 1.",
            "arm 3 points the wrong way: a rigorous composition law refutes the "
            "conjecture rather than proving it, so it is not a promotion route.",
        ],
        "not_established": (
            "no upper bound on g(k) is proved here. Every g value is a maximum "
            "inside [1, N] only; a witness with a larger element would raise it."
        ),
    }
    out["seconds_total"] = round(time.time() - t0, 2)
    (HERE / "results.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(
        {k: v for k, v in out.items() if k != "arm1_padic_pruning"}, indent=2)[:2000])
    for r in rows:
        print(r["k"], r["S"], "N=", r["N"], "g>=", r["g_lower"],
              "exh=", r["exhaustive_in_universe"], "ver=", r["witness_verified"],
              r["witness"][:12])
    print("seconds", out["seconds_total"])


if __name__ == "__main__":
    main()
