"""Graph/Ramsey arm for Erdos #126 (support run d0f0aefb).

Stdlib only.  Run:  python3 hunts/support_d0f0aefb/probe.py
Writes results.json next to this file.

Nothing here is evidence for or against RH (docs/08).
"""

import itertools
import json
import os
from math import gcd

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]


# ---------------------------------------------------------------- basics


def smooth_support(m, S):
    """Return (is_S_smooth, {p: v_p(m)}) for m > 0."""
    val = {}
    r = m
    for p in S:
        e = 0
        while r % p == 0:
            r //= p
            e += 1
        if e:
            val[p] = e
    return r == 1, val


def is_good(A, S):
    """Every off-diagonal sum has prime support inside S."""
    return all(smooth_support(a + b, S)[0] for a, b in itertools.combinations(sorted(A), 2))


def vp(a, p):
    t = 0
    while a % p == 0:
        a //= p
        t += 1
    return t


# ---------------------------------------------------------------- graphs


def graph_p(A, p):
    """G_p: edge {a,b} iff p | a+b.  Returns adjacency dict."""
    adj = {a: set() for a in A}
    for a, b in itertools.combinations(A, 2):
        if (a + b) % p == 0:
            adj[a].add(b)
            adj[b].add(a)
    return adj


def components(adj):
    seen, comps = set(), []
    for v in adj:
        if v in seen:
            continue
        stack, comp = [v], []
        seen.add(v)
        while stack:
            u = stack.pop()
            comp.append(u)
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        comps.append(sorted(comp))
    return comps


def classify_component(adj, comp):
    """'clique', 'complete-bipartite', 'isolated', or 'OTHER'."""
    n = len(comp)
    if n == 1:
        return "isolated"
    edges = sum(len(adj[v] & set(comp)) for v in comp) // 2
    if edges == n * (n - 1) // 2:
        return "clique"
    # 2-colour; connected component of a complete bipartite graph is bipartite
    colour = {comp[0]: 0}
    stack = [comp[0]]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in colour:
                colour[w] = 1 - colour[u]
                stack.append(w)
            elif colour[w] == colour[u]:
                return "OTHER"
    X = [v for v in comp if colour[v] == 0]
    Y = [v for v in comp if colour[v] == 1]
    return "complete-bipartite" if edges == len(X) * len(Y) else "OTHER"


def chromatic_number(adj):
    """Exact chi by increasing-k backtracking.  Small graphs only."""
    V = sorted(adj, key=lambda v: -len(adj[v]))
    n = len(V)
    if n == 0:
        return 0
    for k in range(1, n + 1):
        colour = {}

        def bt(i):
            if i == n:
                return True
            v = V[i]
            used = {colour[w] for w in adj[v] if w in colour}
            top = min(k, max(colour.values(), default=-1) + 2)
            for c in range(top):
                if c not in used:
                    colour[v] = c
                    if bt(i + 1):
                        return True
                    del colour[v]
            return False

        if bt(0):
            return k
    return n


def independence_number(adj):
    V = sorted(adj)
    best = 0
    for r in range(len(V), 0, -1):
        if r <= best:
            break
        for sub in itertools.combinations(V, r):
            ss = set(sub)
            if all(not (adj[v] & ss) for v in sub):
                return r
    return best


# ---------------------------------------------------------------- witnesses

WITNESSES = [
    (1, [2], [1, 3]),
    (2, [2, 3], [1, 5, 7, 11]),
    (3, [2, 3, 5], [1, 3, 7, 17, 47]),
    (4, [2, 3, 5, 7], [1, 2, 3, 5, 7, 13]),
    (5, [2, 3, 5, 7, 11], [1, 2, 5, 9, 13, 19, 23, 31]),
    (6, [2, 3, 5, 7, 11, 13], [1, 2, 3, 5, 7, 9, 13, 19, 23, 47]),
    (7, [2, 3, 5, 7, 11, 13, 17], [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49]),
]


def audit_witnesses():
    out = []
    for k, S, A in WITNESSES:
        rec = {
            "k": k,
            "S": S,
            "A": A,
            "n": len(A),
            "good": is_good(A, S),
            "gcd": 0,
            "per_prime": {},
        }
        g = 0
        for a in A:
            g = gcd(g, a)
        rec["gcd"] = g
        prod_chi = 1
        for p in S:
            adj = graph_p(A, p)
            comps = components(adj)
            kinds = [classify_component(adj, c) for c in comps]
            chi = chromatic_number(adj)
            T = len({vp(a, p) for a in A})
            prod_chi *= chi
            rec["per_prime"][str(p)] = {
                "components": [{"vertices": c, "kind": kd} for c, kd in zip(comps, kinds)],
                "chi": chi,
                "alpha": independence_number(adj),
                "T_p": T,
                # chi <= 2 T_p is claimed for ODD p only; p = 2 is exceptional
                "chi_le_2T_odd_p": (chi <= 2 * T) if p != 2 else None,
                "chi_eq_max_parity_class": (
                    chi == max(sum(1 for a in A if a % 2 == 0),
                               sum(1 for a in A if a % 2 == 1))
                    if p == 2 else None
                ),
                "structure_ok": all(kd != "OTHER" for kd in kinds),
                "n_multiples_of_p": sum(1 for a in A if a % p == 0),
            }
        rec["product_of_chi"] = prod_chi
        rec["product_bound_vacuous"] = prod_chi >= len(A)
        rec["max_chi"] = max(rec["per_prime"][str(p)]["chi"] for p in S)
        # union of the G_p must cover K_n
        covered = all(
            any((a + b) % p == 0 for p in S) for a, b in itertools.combinations(A, 2)
        )
        rec["cover_holds"] = covered
        out.append(rec)
    return out


# ------------------------------------------- realizable obstruction (cover)


def residue_cover_family(n):
    """{1} u {2(3j+1)} : every pair is covered by some p in {2,3}, gcd = 1,
    and the size is unbounded.  These sums are NOT all {2,3}-smooth: the point
    is exactly that the cover condition alone does not see that."""
    A = [1] + [2 * (3 * j + 1) for j in range(n - 1)]
    S = [2, 3]
    covered = all(
        any((a + b) % p == 0 for p in S) for a, b in itertools.combinations(A, 2)
    )
    g = 0
    for a in A:
        g = gcd(g, a)
    return {"n": len(A), "S": S, "A_head": A[:8], "cover_holds": covered, "gcd": g,
            "actually_good": is_good(A, S)}


# ------------------------------------------- refuting the "|A| <= p-1" thread


def p_not_in_S_witness():
    """r_186989 thread: 'prove |A| <= p-1 when p not in S'.  False for odd p.
    {1,4,124} with S={2,5}: 3 not in S, |A| = 3 > p-1 = 2."""
    A, S, p = [1, 4, 124], [2, 5], 3
    return {
        "A": A,
        "S": S,
        "p_absent": p,
        "sums": {f"{a}+{b}": a + b for a, b in itertools.combinations(A, 2)},
        "good": is_good(A, S),
        "p_divides_no_sum": all((a + b) % p for a, b in itertools.combinations(A, 2)),
        "claim_bound": p - 1,
        "actual": len(A),
        "thread_refuted": is_good(A, S) and len(A) > p - 1,
        "residues_mod_p": sorted({a % p for a in A}),
    }


def parity_bound_check(limit=400):
    """2 not in S  =>  |A| <= 2.  Brute-force confirmation for S={3,5,7}."""
    S = [3, 5, 7]
    ok = [a for a in range(1, limit) for b in range(a + 1, limit)
          if smooth_support(a + b, S)[0]]
    triples = []
    cand = sorted({x for a in range(1, limit) for b in range(a + 1, limit)
                   if smooth_support(a + b, S)[0] for x in (a, b)})
    for t in itertools.combinations(cand[:60], 3):
        if is_good(t, S):
            triples.append(t)
    return {"S": S, "limit": limit, "pairs_found": len(ok) > 0,
            "triples_found": triples[:5], "bound_holds_in_range": not triples}


# ------------------------------------------- coprime sub-problem: |A| <= 2^k


def max_coprime_set(S, N):
    """max |A|, A c [1,N], all a coprime to prod S, all pairwise sums S-smooth.
    Branch and bound over the smooth-sum graph."""
    P = 1
    for p in S:
        P *= p
    V = [a for a in range(1, N + 1) if gcd(a, P) == 1]
    adjacent = {a: set() for a in V}
    for a, b in itertools.combinations(V, 2):
        if smooth_support(a + b, S)[0]:
            adjacent[a].add(b)
            adjacent[b].add(a)
    best = [[]]

    def expand(cur, cand):
        if len(cur) > len(best[0]):
            best[0] = list(cur)
        if len(cur) + len(cand) <= len(best[0]):
            return
        cand = list(cand)
        while cand:
            v = cand.pop(0)
            if len(cur) + 1 + len(cand) <= len(best[0]):
                return
            expand(cur + [v], [w for w in cand if w in adjacent[v]])

    expand([], V)
    return best[0]


def coprime_table():
    rows = []
    for k, N in [(1, 3000), (2, 3000), (3, 2000), (4, 1500)]:
        S = PRIMES[:k]
        A = max_coprime_set(S, N)
        rows.append({"k": k, "S": S, "N": N, "max_size": len(A), "witness": A,
                     "theorem_bound_2^k": 2 ** k, "holds": len(A) <= 2 ** k})
    return rows


# ------------------------------------------- the S-unit reduction, checked


def s_unit_triples(A, S):
    """Lemma R.  With a1,a2,a3 fixed and c = a2+a3, c' = a1+a3,
    s_i = a1+a_i, t_i = a2+a_i, the identity s_i + c = t_i + c' gives
        X + Y + Z = 1,  X = s_i/t_i,  Y = c/t_i,  Z = -c'/t_i,
    all S-units, no vanishing subsum, and i |-> (X,Y,Z) injective."""
    from fractions import Fraction

    A = sorted(A)
    if len(A) < 4:
        return {"applicable": False}
    a1, a2, a3 = A[0], A[1], A[2]
    c, cp = a2 + a3, a1 + a3
    out, seen = [], set()
    ok = True
    for ai in A[3:]:
        s, t = a1 + ai, a2 + ai
        X, Y, Z = Fraction(s, t), Fraction(c, t), -Fraction(cp, t)
        unit = all(smooth_support(abs(v.numerator), S)[0]
                   and smooth_support(v.denominator, S)[0] for v in (X, Y, Z))
        ok &= unit and X + Y + Z == 1 and X + Y != 0 and X + Z != 0 and Y + Z != 0
        key = (X, Y, Z)
        ok &= key not in seen
        seen.add(key)
        out.append({"a_i": ai, "X": str(X), "Y": str(Y), "Z": str(Z),
                    "s_unit": unit})
    return {"applicable": True, "a1": a1, "a2": a2, "a3": a3, "c": c, "c_prime": cp,
            "solutions": out, "count": len(out), "n_minus_3": len(A) - 3,
            "all_checks_pass": ok}


# ---------------------------------------------------------------- main

def main():
    res = {
        "arm": "graph-ramsey",
        "run_id": "d0f0aefb-a1ab-4db0-b98a-fbbd895d2cb4",
        "witness_audit": audit_witnesses(),
        "residue_cover_unbounded": [residue_cover_family(n) for n in (5, 20, 60)],
        "p_not_in_S_thread": p_not_in_S_witness(),
        "parity_bound": parity_bound_check(),
        "coprime_subproblem": coprime_table(),
        "s_unit_reduction": [
            dict(k=k, S=S, **s_unit_triples(A, S)) for k, S, A in WITNESSES
        ],
        "claims": [
            {"id": "P", "grade": "proved",
             "statement": "2 not in S implies |A| <= 2.",
             "checked_by": "parity_bound"},
            {"id": "T1", "grade": "proved",
             "statement": "G_p is the disjoint union of G_p|V_0 and a complete "
                          "multipartite join of the level sets V_t, t>=1; for odd p "
                          "each G_p|V_t is a disjoint union of complete bipartite "
                          "graphs, for p=2 each is a clique. chi(G_p) <= 2 T_p for "
                          "odd p.",
             "checked_by": "witness_audit[*].per_prime"},
            {"id": "T2", "grade": "proved",
             "statement": "If every a in A is coprime to prod S then |A| <= 2^k. "
                          "Sharper than the Erdos-Turan 3*2^(k-1) on that sub-family.",
             "checked_by": "coprime_subproblem"},
            {"id": "T3", "grade": "proved",
             "statement": "For every n there is A with |A|=n, gcd(A)=1, and k=2 "
                          "primes whose graphs G_p cover K_n. Hence no bound on n "
                          "follows from the cover structure alone.",
             "checked_by": "residue_cover_unbounded"},
            {"id": "T4", "grade": "proved",
             "statement": "g(k) <= 3 + N_3(k), N_3 = max number of nondegenerate "
                          "solutions of x+y+z=1 in S-units of Q with |S|=k. "
                          "One-directional: N_3(k)=exp(o(k)) implies Erdos #126; "
                          "not conversely.",
             "checked_by": "s_unit_reduction"},
            {"id": "R1", "grade": "refutation",
             "statement": "r_186989 loose thread '|A| <= p-1 when p not in S' is "
                          "false for odd p. Witness {1,4,124}, S={2,5}, p=3.",
             "checked_by": "p_not_in_S_thread"},
        ],
    }
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results.json"), "w") as fh:
        json.dump(res, fh, indent=2, sort_keys=True)

    for rec in res["witness_audit"]:
        print(f"k={rec['k']} n={rec['n']} good={rec['good']} cover={rec['cover_holds']} "
              f"gcd={rec['gcd']} max_chi={rec['max_chi']} prod_chi={rec['product_of_chi']} "
              f"vacuous={rec['product_bound_vacuous']} "
              f"struct_ok={all(v['structure_ok'] for v in rec['per_prime'].values())} "
              f"chi<=2T(odd p)={all(v['chi_le_2T_odd_p'] for v in rec['per_prime'].values() if v['chi_le_2T_odd_p'] is not None)} "
              f"chi2=maxparity={rec['per_prime']['2']['chi_eq_max_parity_class'] if '2' in rec['per_prime'] else 'n/a'} "
              f"T={ {p: v['T_p'] for p, v in rec['per_prime'].items()} }")
    print("cover-unbounded:", [(r["n"], r["cover_holds"], r["gcd"], r["actually_good"])
                               for r in res["residue_cover_unbounded"]])
    print("p-not-in-S thread:", res["p_not_in_S_thread"])
    print("parity:", res["parity_bound"]["bound_holds_in_range"],
          res["parity_bound"]["triples_found"])
    for r in res["coprime_subproblem"]:
        print("coprime", r["k"], r["max_size"], "<=", r["theorem_bound_2^k"], r["witness"])


if __name__ == "__main__":
    main()
