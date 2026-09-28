"""
Independent check of ENDPOINT_SHARP.md's third revision, section 4 only
(the two substitutions: input (DF) and the separate sieve level D_1).
Written from scratch for this review; does not reuse endpoint_sharp_probe.py,
endpoint_sharp_mertens_probe.py, review_a0075_mertens_check.py, or
review_a0075_character_check.py.

Three independent checks, each printed and saved to
results_review2_sharp_section4_probe.json:

(1) The sieve level D_1 = floor(N^(1/2)): recompute s_1 = log D_1 / log Z
    and the fundamental-lemma hypothesis D_1 >= Z^10 directly from N and Z,
    with no use of the document's own asymptotic formulas, and locate the
    exact crossover in log N.

(2) The DF "frozen at x" remark (section 4, paragraph after (D')): a
    concrete numerical family of (x, y, beta) showing the frozen-term/
    y-term difference is NOT O(x e^{-delta sqrt(log x)}) once 1-beta is
    taken much smaller than delta/sqrt(log x) (rather than comparable to
    it), with log(x/y) held fixed.

(3) The four inequalities of the "Small y" paragraph, evaluated at
    concrete N rather than taken on asymptotic faith.
"""
import json
import mpmath as mp

mp.mp.dps = 60


def check_level(ell):
    ell = mp.mpf(ell)
    sqrt_ell = mp.sqrt(ell)
    Z = mp.e ** sqrt_ell
    N = mp.e ** ell
    D1 = mp.floor(N ** mp.mpf('0.5'))
    s1 = mp.log(D1) / mp.log(Z)
    hyp_holds = mp.log(D1) >= 10 * mp.log(Z)
    return {
        "logN": float(ell),
        "s1": float(s1),
        "s1_formula_sqrt_ell_over_2": float(sqrt_ell / 2),
        "hypothesis_D1_ge_Z10_holds": bool(hyp_holds),
    }


def check_df_remark(logx, delta, mu, L):
    """diff = |eta_{x,a}*y - chi(a) y^beta/beta| (magnitude, chi(a)=1)
    versus bound = x * exp(-delta*sqrt(log x)), with 1-beta = mu/log(x)
    (much smaller than the allowed c0/sqrt(log x) ceiling) and
    log(x/y) = L fixed."""
    logx = mp.mpf(logx)
    sqrt_logx = mp.sqrt(logx)
    x = mp.e ** logx
    eps = mu / logx
    beta = 1 - eps
    y = x * mp.e ** (-L)
    diff = y * x ** (beta - 1) * abs((x / y) ** (1 - beta) - 1) / beta
    bound = x * mp.e ** (-delta * sqrt_logx)
    return {
        "logx": float(logx),
        "one_minus_beta": float(eps),
        "diff": mp.nstr(diff, 8),
        "bound": mp.nstr(bound, 8),
        "diff_over_bound": mp.nstr(diff / bound, 8),
    }


def check_small_y(ell, sigma):
    ell = mp.mpf(ell)
    sigma = mp.mpf(sigma)
    sqrt_ell = mp.sqrt(ell)
    Z = mp.e ** sqrt_ell
    N = mp.e ** ell
    R = mp.floor(mp.e ** (sigma * sqrt_ell))
    logy = ell / 2
    sqrt_logy = mp.sqrt(logy)
    e_sqrt_logy = mp.e ** sqrt_logy
    ineq1 = e_sqrt_logy >= R
    ineq2 = e_sqrt_logy <= Z
    y = mp.e ** logy
    R_sqrty = R * mp.sqrt(y) * (mp.log(y)) ** 3
    Nexp = N * mp.e ** (-sqrt_ell)
    ineq_R = R_sqrty <= Nexp
    return {
        "logN": float(ell),
        "R": mp.nstr(R, 6),
        "e_sqrt_logy_ge_R": bool(ineq1),
        "e_sqrt_logy_le_Z": bool(ineq2),
        "R_sqrty_logy3": mp.nstr(R_sqrty, 6),
        "N_exp_minus_sqrt_ell": mp.nstr(Nexp, 6),
        "R_sqrty_le_N_exp_minus_sqrt_ell": bool(ineq_R),
    }


results = {}

print("=== (1) Sieve level D_1, hypothesis D_1 >= Z^10 ===")
results["level_D1"] = []
for ell in [100, 399, 400, 401, 1000, 10000]:
    r = check_level(ell)
    print(r)
    results["level_D1"].append(r)

print()
print("=== (2) DF frozen-at-x remark: diff/bound with 1-beta = mu/log(x), L fixed ===")
delta, mu, L = mp.mpf('0.5'), mp.mpf('1'), mp.mpf('3')
print(f"delta={delta}, mu={mu} (1-beta=mu/log x), L=log(x/y)={L}")
results["df_remark"] = {"delta": float(delta), "mu": float(mu), "L": float(L), "rows": []}
for logx in [100, 1000, 10000, 100000, 1000000, 10000000]:
    r = check_df_remark(logx, delta, mu, L)
    print(r)
    results["df_remark"]["rows"].append(r)

print()
print("=== (3) Small-y inequalities at logy = logN/2 ===")
results["small_y"] = []
for ell in [1000, 10000, 100000]:
    r = check_small_y(ell, mp.mpf('0.05'))
    print(r)
    results["small_y"].append(r)

with open("results_review2_sharp_section4_probe.json", "w") as f:
    json.dump(results, f, indent=2)
print("\nWrote results_review2_sharp_section4_probe.json")
