"""Digest raw.json / raw2.json / raw3.json into results.json."""
import json

D = "hunts/support_60982bf6/"
raw = json.load(open(D + "raw.json"))["subsets_by_k"]
raw2 = json.load(open(D + "raw2.json"))
raw3 = json.load(open(D + "raw3.json"))

sweep = {}
for k, rows in raw.items():
    mx = max(r["g_N"] for r in rows)
    sweep[k] = {
        "box_N": rows[0]["N"],
        "n_subsets": len(rows),
        "max_g_N": mx,
        "maximizers": [r["S"] for r in rows if r["g_N"] == mx],
        "first_k_primes_is_maximal": [2, 3, 5, 7, 11][: int(k)]
        in [r["S"] for r in rows if r["g_N"] == mx],
        "two_not_in_S_all_equal_2": all(
            r["g_N"] == 2 for r in rows if 2 not in r["S"]
        ),
        "range_over_S_with_2_in_S": [
            min(r["g_N"] for r in rows if 2 in r["S"]),
            max(r["g_N"] for r in rows if 2 in r["S"]),
        ],
    }

G = {tuple(r["S"]): r["g_N"] for rows in raw.values() for r in rows}
P = [2, 3, 5, 7, 11, 13, 17, 19, 23]
viol = []
for S, g in G.items():
    for i, p in enumerate(S):
        for q in P:
            if q > p and q not in S:
                T = tuple(sorted(S[:i] + S[i + 1:] + (q,)))
                if T in G and G[T] > g:
                    viol.append({"S_small": list(S), "g": g,
                                 "S_large": list(T), "g_larger": G[T]})

out = {
    "problem": "Erdos #126; g(S) = max |A| with all off-diagonal sums S-smooth",
    "arm": "exact-theorem-mining (support_60982bf6)",
    "direction_of_bounds": "every g_N is a LOWER bound on g; box-exhaustive only",
    "not_evidence_for_RH": True,
    "sweep_over_all_S": sweep,
    "normalization_lemma": {
        "statement": ("gcd(A) is S-smooth; A/gcd(A) is S-admissible; mA is "
                      "S-admissible for S-smooth m. So the admissible sets are "
                      "exactly the S-smooth dilates of primitive ones."),
        "status": "proved",
        "checks": raw2["normalization_checks"],
    },
    "refutation_mod_p_pigeonhole": {
        "named_lemma": ("hunts/r_186989 loose thread 3: |A| <= p-1 when p not "
                        "in S, by pigeonhole on residues mod p"),
        "status": "refuted",
        "reason": ("for odd p and r != 0 mod p, r+r != 0 mod p, so arbitrarily "
                   "many elements of A may share one nonzero class; the "
                   "pigeonhole bounds the number of occupied classes, not |A|. "
                   "p=2 is the unique prime with 2r=0 for every r."),
        "counterexamples": raw3["mod_p_counterexamples"],
    },
    "refutation_prime_size_monotonicity": {
        "named_lemma": ("replacing a prime of S by a larger one cannot "
                        "increase g(S)"),
        "status": "refuted, box-conditional",
        "flagship": {"S_small": [2, 3, 11], "g_N": G[(2, 3, 11)],
                     "S_large": [2, 3, 13], "g_N_larger": G[(2, 3, 13)],
                     "box_for_upper_half": 20000},
        "n_violations_in_sweep": len(viol),
        "violations": viol,
    },
    "conjecture_bounded_height": {
        "statement": ("h(S) = min{max A : A is S-admissible, |A| = g(S)} is "
                      "bounded by some B(k) uniformly over all S with |S| = k "
                      "and 2 in S"),
        "status": ("conjectural; consistent with every S measured, verified for "
                   "none (the measured quantity is h inside a box)"),
        "why_it_matters": ("if true with explicit B, g(S) for fixed S becomes a "
                           "finite computation; g(k) additionally needs a bound "
                           "on which primes may appear in a maximizing S, which "
                           "this run did not obtain"),
        "explicit_forms_killed_by_this_run": [
            {"form": "2^(k+2)", "killed_by": "h({2,3,5}) = 47 > 32"},
            {"form": "2^(k+3)", "killed_by": "h({2,3,7,13}) = 159 > 128"},
        ],
        "heights": raw3["heights"],
    },
    "height_ladder": raw2["height_ladder"],
}
json.dump(out, open(D + "results.json", "w"), indent=1)
print("wrote results.json;", len(viol), "monotonicity violations")
