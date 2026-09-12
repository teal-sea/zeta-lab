"""Erdos #126, ORIGINAL-PROOF arm: audit of the Erdos-Turan halving step.

The 1934 bound is g(k) < 3 * 2^(k-1) and the Erdos-Suranyi form is
g(k) <= 2^k.  Both come from the same architecture:

    base case      3 elements whose pairwise sums are powers of 2 -> impossible
    inductive step one binary split per ODD prime of the support

This probe checks the three claims the write-up makes about that step.

  C1  the naive per-prime halving lemma ("every finite B has a subset B' with
      |B'| >= |B|/2 and q dividing no pairwise sum of B'") is FALSE, and it is
      false on a set whose pairwise sums really are S-smooth.  Explicit
      witness, re-verified from scratch by trial division.

  C2  on the actual extremal sets (exhaustive clique search in a small box)
      the halving step's true loss per odd prime is measured, not assumed.

  C3  the residue-only argument cannot beat 2 per prime even if all primes are
      processed jointly: a CRT-designed configuration of 2^s residues admits no
      2-element subset avoiding every q_i.  Checked by brute force, and then
      checked against the extremal sets to see whether such a pattern actually
      occurs there.

stdlib only.  Runs in well under a minute.  Writes results.json.
"""

import json
import itertools
from pathlib import Path


def prime_support(n):
    """Set of primes dividing n, by trial division. n >= 1."""
    out = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            out.add(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.add(n)
    return out


def is_smooth(n, S):
    return prime_support(n) <= set(S)


def support_of_set(A):
    """Union of prime supports of all off-diagonal sums."""
    out = set()
    for a, b in itertools.combinations(sorted(A), 2):
        out |= prime_support(a + b)
    return out


# ---------------------------------------------------------------- clique search

def max_smooth_set(S, N):
    """Exact maximum |A|, A subset of [1,N], every off-diagonal sum S-smooth.

    Branch and bound on the graph a ~ b iff a+b is S-smooth.  Exhaustive.
    """
    S = tuple(sorted(S))
    verts = list(range(1, N + 1))
    adj = {v: set() for v in verts}
    for i, a in enumerate(verts):
        for b in verts[i + 1:]:
            if is_smooth(a + b, S):
                adj[a].add(b)
                adj[b].add(a)
    best = [[]]

    def expand(cur, cand):
        if len(cur) + len(cand) <= len(best[0]):
            return
        if not cand:
            if len(cur) > len(best[0]):
                best[0] = list(cur)
            return
        for v in sorted(cand):
            if len(cur) + len(cand) <= len(best[0]):
                return
            expand(cur + [v], {u for u in cand if u > v and u in adj[v]})
            cand = cand - {v}

    expand([], set(verts))
    return best[0]


# ------------------------------------------------------- the halving step itself

def max_q_clean_subset(A, q):
    """Largest A' <= A with q dividing no off-diagonal sum of A'.

    Exact.  Uses the residue structure: at most one element from the class 0,
    and from each unordered pair {r,-r} of nonzero classes only one side.
    """
    A = sorted(A)
    zero = [a for a in A if a % q == 0]
    rest = [a for a in A if a % q != 0]
    classes = {}
    for a in rest:
        classes.setdefault(a % q, []).append(a)
    best = []
    seen = set()
    for r in sorted(classes):
        if r in seen:
            continue
        s = (-r) % q
        seen.add(r)
        seen.add(s)
        side_r = classes.get(r, [])
        side_s = classes.get(s, []) if s != r else []
        if s == r:
            # r == -r mod q is impossible for odd q and r != 0; for q = 2 it is
            # the whole story: any two elements of one class sum to 0 mod 2.
            best.append(side_r[:1])
        else:
            best.append(side_r if len(side_r) >= len(side_s) else side_s)
    out = [a for blk in best for a in blk]
    if zero:
        out.append(zero[0])
    return sorted(out)


def brute_max_q_clean(A, q):
    """Independent check of max_q_clean_subset by brute force over subsets."""
    A = sorted(A)
    best = []
    for m in range(len(A), 0, -1):
        if m <= len(best):
            break
        for sub in itertools.combinations(A, m):
            if all((a + b) % q != 0 for a, b in itertools.combinations(sub, 2)):
                return list(sub)
    return best


def results():
    out = {}

    # ---- C1: explicit refutation of the naive halving lemma -----------------
    A = [1, 3, 15, 21, 33]
    S = sorted(support_of_set(A))
    q = 3
    clean = brute_max_q_clean(A, q)
    out["C1_naive_halving_counterexample"] = {
        "A": A,
        "S": S,
        "k": len(S),
        "all_offdiag_sums": {
            f"{a}+{b}": {"value": a + b, "support": sorted(prime_support(a + b))}
            for a, b in itertools.combinations(A, 2)
        },
        "q": q,
        "max_q_clean_subset": clean,
        "ratio_clean_over_n": len(clean) / len(A),
        "halving_lemma_would_need": len(A) / 2,
        "lemma_false": len(clean) < len(A) / 2,
    }

    # the unbounded version: B = q*C u {x}
    C = [1, 5, 7, 11]
    fam = []
    for m in (1, 2, 3, 4):
        B = [1] + [3 * c for c in C[:m]]
        fam.append({
            "B": B,
            "S": sorted(support_of_set(B)),
            "n": len(B),
            "max_3_clean": len(brute_max_q_clean(B, 3)),
        })
    out["C1_family"] = fam

    # ---- C2: measured loss of the halving step on real extremal sets --------
    rows = []
    for S_, N in [((2,), 300), ((2, 3), 400), ((2, 3, 5), 400),
                  ((2, 3, 5, 7), 300), ((2, 3, 5, 7, 11), 200)]:
        A = max_smooth_set(S_, N)
        per_prime = {}
        for q in S_:
            exact = max_q_clean_subset(A, q)
            bf = brute_max_q_clean(A, q)
            assert len(exact) == len(bf), (A, q, exact, bf)
            per_prime[str(q)] = {
                "clean": bf,
                "loss_factor": len(A) / len(bf) if bf else None,
            }
        rows.append({
            "S": list(S_), "N": N, "witness": A, "n": len(A),
            "support_of_witness": sorted(support_of_set(A)),
            "per_prime": per_prime,
            "worst_loss_over_odd_primes": max(
                (per_prime[str(q)]["loss_factor"] for q in S_ if q != 2),
                default=None),
        })
    out["C2_measured_halving_loss"] = rows

    # ---- C3: joint-CRT barrier to residue-only arguments --------------------
    barrier = []
    for primes in [(3, 5), (3, 5, 7), (3, 5, 7, 11)]:
        s = len(primes)
        M = 1
        for p in primes:
            M *= p
        # x_eps = eps_i * 1 mod q_i, realised in [1, M] by CRT.
        pts = []
        for eps in itertools.product((1, -1), repeat=s):
            x = None
            for cand in range(1, M + 1):
                if all(cand % p == (e % p) for p, e in zip(primes, eps)):
                    x = cand
                    break
            pts.append(x)
        # largest subset avoiding divisibility by EVERY q_i simultaneously
        best = 0
        for m in range(len(pts), 0, -1):
            found = False
            for sub in itertools.combinations(pts, m):
                if all(all((a + b) % p != 0 for p in primes)
                       for a, b in itertools.combinations(sub, 2)):
                    found = True
                    break
            if found:
                best = m
                break
        barrier.append({
            "primes": list(primes), "s": s, "n_points": len(pts),
            "points": pts, "max_jointly_clean_subset": best,
            "predicted": 1,
        })
    out["C3_crt_barrier"] = barrier

    # does that pattern occur inside a real extremal set?
    occ = []
    for row in out["C2_measured_halving_loss"]:
        A = row["witness"]
        odd = [p for p in row["S"] if p != 2]
        if not odd:
            continue
        best = 0
        for m in range(len(A), 0, -1):
            found = any(
                all(all((a + b) % p != 0 for p in odd)
                    for a, b in itertools.combinations(sub, 2))
                for sub in itertools.combinations(A, m))
            if found:
                best = m
                break
        occ.append({"S": row["S"], "witness": A, "n": len(A),
                    "max_jointly_odd_clean": best,
                    "ratio": best / len(A),
                    "worst_case_prediction": len(A) / 2 ** len(odd)})
    out["C3_joint_clean_on_real_witnesses"] = occ

    # ---- C4/C5: exhaustive sweep over admissible sets in a small box -------
    # c(A) = largest A' <= A whose off-diagonal sums are all powers of 2.
    # The classical selection step claims c(A) >= |A| / 2^s (s = #odd primes).
    sweep = []
    for S_, N in [((2, 3, 5), 300), ((2, 3, 5, 7), 200), ((2, 3, 5, 7, 11), 150)]:
        odd = [p for p in S_ if p != 2]
        s = len(odd)
        V = list(range(1, N + 1))
        adj = {v: set() for v in V}
        for i, a in enumerate(V):
            for b in V[i + 1:]:
                if is_smooth(a + b, S_):
                    adj[a].add(b)
                    adj[b].add(a)
        sets = []

        def dfs(cur, cand):
            if len(cur) >= 2:
                sets.append(tuple(cur))
            for v in sorted(cand):
                dfs(cur + [v], {u for u in cand if u > v and u in adj[v]})
                cand = cand - {v}

        dfs([], set(V))

        def c_of(A):
            for m in range(len(A), 0, -1):
                for sub in itertools.combinations(A, m):
                    if all(all((a + b) % p != 0 for p in odd)
                           for a, b in itertools.combinations(sub, 2)):
                        return m
            return 0

        viol_prim, viol_nonprim, worst = [], [], (float("inf"), None)
        max_ratio = (0, None)
        for A in sets:
            A = list(A)
            c = c_of(A)
            n = len(A)
            g = A[0]
            for a in A[1:]:
                while a:
                    g, a = a, g % a
            if c < n / 2 ** s:
                (viol_prim if g == 1 else viol_nonprim).append(
                    {"A": A, "n": n, "c": c, "gcd": g, "bound": n / 2 ** s})
            if g == 1 and c / (n / 2 ** s) < worst[0]:
                worst = (c / (n / 2 ** s), {"A": A, "n": n, "c": c})
            if n / c > max_ratio[0]:
                max_ratio = (n / c, {"A": A, "n": n, "c": c, "gcd": g})
        sweep.append({
            "S": list(S_), "N": N, "s_odd_primes": s, "n_admissible_sets": len(sets),
            "violations_of_c_ge_n_over_2s_primitive": len(viol_prim),
            "violations_of_c_ge_n_over_2s_nonprimitive": len(viol_nonprim),
            "example_nonprimitive_violation": viol_nonprim[0] if viol_nonprim else None,
            "example_primitive_violation": viol_prim[0] if viol_prim else None,
            "tightest_primitive_slack": worst[0],
            "tightest_primitive_witness": worst[1],
            "largest_n_over_c": max_ratio[0],
            "largest_n_over_c_witness": max_ratio[1],
        })
    out["C45_sweep"] = sweep

    # ---- tightness of the two classical bounds against measured g ----------
    measured_g_lower = {1: 2, 2: 4, 3: 5, 4: 6, 5: 8, 6: 10, 7: 11}
    out["bound_vs_measured"] = [
        {"k": k, "g_lower_bound_measured": v,
         "erdos_turan_1934": 3 * 2 ** (k - 1) - 1,
         "erdos_suranyi": 2 ** k,
         "suranyi_tight": v == 2 ** k}
        for k, v in sorted(measured_g_lower.items())
    ]
    return out


if __name__ == "__main__":
    r = results()
    p = Path(__file__).with_name("results.json")
    p.write_text(json.dumps(r, indent=2, sort_keys=True) + "\n")
    print(json.dumps(r["C1_naive_halving_counterexample"], indent=2))
    for row in r["C2_measured_halving_loss"]:
        print(row["S"], "n=", row["n"], "worst odd-prime loss",
              row["worst_loss_over_odd_primes"], row["witness"])
    for b in r["C3_crt_barrier"]:
        print("barrier", b["primes"], b["n_points"], "->",
              b["max_jointly_clean_subset"])
    for o in r["C3_joint_clean_on_real_witnesses"]:
        print("real witness", o["S"], o["n"], "->", o["max_jointly_odd_clean"],
              "worst case would be", o["worst_case_prediction"])
    print("wrote", p)
