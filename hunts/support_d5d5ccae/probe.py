"""S-unit arm for Erdos #126 (support run d5d5ccae). Stdlib only, ~1 min.

What it measures
----------------
The reduction lemma in RESULTS.md says: if A is a set whose pairwise sums are
all S-smooth, then for ANY two base elements a > b of A the map

    x |-> (a + x, b + x)

is injective from A \\ {a, b} into the solution set of the two-variable
S-unit equation  U - W = d,  d = a - b,  U, W positive S-smooth.

So |A| <= 2 + N_S(d) for every pair, hence |A| <= 2 + min over pairs.

This probe computes N_S(d) exactly inside a box [1, X] (so: a LOWER bound on
the true N_S(d)), for S = first k primes, and compares it against

  * Lehmer's published Stormer counts for d = 1 (external oracle), and
  * the classical Erdos-Suranyi ceiling g(k) <= 2^k, and
  * the witnesses measured by hunt r_186989.

Writes results.json.
"""

import json
from itertools import combinations

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23]

# Lehmer (1964) / Stormer: number of pairs of consecutive integers both
# composed only of the first k primes, k = 1..9.  External reference values.
LEHMER_CONSECUTIVE = {1: 1, 2: 4, 3: 10, 4: 23, 5: 40, 6: 68, 7: 108, 8: 167, 9: 241}

# Witnesses measured by hunt r_186989 (exhaustive inside its own box).
WITNESSES = {
    1: [1, 3],
    2: [1, 5, 7, 11],
    3: [1, 3, 7, 17, 47],
    4: [1, 2, 3, 5, 7, 13],
    5: [1, 2, 5, 9, 13, 19, 23, 31],
    6: [1, 2, 3, 5, 7, 9, 13, 19, 23, 47],
    7: [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49],
}


def smooth_numbers(primes, limit):
    """All n <= limit with no prime factor outside `primes`, sorted."""
    out = [1]
    for p in primes:
        nxt = []
        for v in out:
            w = v
            while w <= limit:
                nxt.append(w)
                if w > limit // p:
                    break
                w *= p
        out = nxt
    out.sort()
    return out


def is_smooth(n, primes):
    for p in primes:
        while n % p == 0:
            n //= p
    return n == 1


def count_diff(smooth_set, smooth_sorted, d, limit):
    """#{(U, W) : U - W = d, both S-smooth, U <= limit}."""
    c = 0
    for w in smooth_sorted:
        if w + d > limit:
            break
        if w + d in smooth_set:
            c += 1
    return c


def main():
    X = 10 ** 14
    report = {
        "box": X,
        "note": "counts are exact inside [1, X], hence LOWER bounds on the true N_S(d)",
        "per_k": [],
    }

    for k in range(1, 9):
        S = PRIMES[:k]
        sm = smooth_numbers(S, X)
        smset = set(sm)

        consec = count_diff(smset, sm, 1, X)

        # N_S(d) for a spread of small d.
        nd = {d: count_diff(smset, sm, d, X) for d in range(1, 41)}
        dmax = max(nd, key=lambda d: nd[d])

        row = {
            "k": k,
            "S": S,
            "num_smooth_in_box": len(sm),
            "N_S(1)_measured": consec,
            "N_S(1)_lehmer": LEHMER_CONSECUTIVE.get(k),
            "N_S(1)_matches_lehmer": consec == LEHMER_CONSECUTIVE.get(k),
            "N_S(d)_d_1_to_40": nd,
            "argmax_d_le_40": dmax,
            "max_N_S(d)_d_le_40": nd[dmax],
            "erdos_suranyi_ceiling_2^k": 2 ** k,
            "evertse_ceiling_2+3*7^(2k+3)": 2 + 3 * 7 ** (2 * k + 3),
        }

        if k in WITNESSES:
            A = WITNESSES[k]
            # sanity: re-verify the witness from scratch
            ok = all(is_smooth(a + b, S) for a, b in combinations(A, 2))
            diffs = sorted({a - b for a, b in combinations(A, 2)})
            per_pair = {d: count_diff(smset, sm, d, X) for d in diffs}
            best = min(per_pair, key=lambda d: per_pair[d])
            row["witness"] = {
                "A": A,
                "reverified_all_pair_sums_smooth": ok,
                "|A|": len(A),
                "|A|-2": len(A) - 2,
                "N_S(d)_over_witness_differences": per_pair,
                "best_base_pair_difference": best,
                "reduction_bound_2+min_N_S(d)": 2 + per_pair[best],
                "slack_vs_|A|": 2 + per_pair[best] - len(A),
            }

        report["per_k"].append(row)
        print(
            f"k={k:2d} smooth={len(sm):7d} N(1)={consec:4d} "
            f"(Lehmer {LEHMER_CONSECUTIVE.get(k)}) maxN(d<=40)={nd[dmax]:5d} at d={dmax:2d} "
            f"2^k={2**k}"
            + (
                f"  witness |A|={len(WITNESSES[k])} bound={2 + report['per_k'][-1]['witness']['N_S(d)_over_witness_differences'][report['per_k'][-1]['witness']['best_base_pair_difference']]}"
                if k in WITNESSES
                else ""
            )
        )

    with open(__file__.rsplit("/", 1)[0] + "/results.json", "w") as f:
        json.dump(report, f, indent=2)
    print("wrote results.json")


if __name__ == "__main__":
    main()
