"""
Finite check supporting ENDPOINT_HALF.md.

Question: with Z = exp((log N)^kappa) replacing ENDPOINT_BOUND.md's
Z = exp((log N)^{1/10}), and the *fixed* Bonferroni cutoff m = 2*ceil(sqrt(log N))
exactly as printed in ENDPOINT_BOUND.md Section 2, does D_0 = Z^m stay N^{o(1)}
(needed so the term N^2 D_0 sqrt(Z) in equation (18) stays below N^3), or does it
become a genuine power of N?

This is a one-thread, fixed-cutoff numerical illustration of an elementary
asymptotic claim (log D_0 / log N = 2*ceil(sqrt(ell))*ell^kappa/ell -> 2*ell^{kappa-1/2}),
not a proof by itself. The proof is the algebra in ENDPOINT_HALF.md; this
script only checks the arithmetic at finite N and records it exactly.

It also checks the companion claim: for ANY choice of m (not just the fixed
2*ceil(sqrt(ell))), the minimal m for which the Bonferroni truncation error
N*H_Z^{m+1}/(m+1)! actually decays forces m/H_Z > e in the limit ell -> infinity
at kappa = 1/2 exactly (since H_Z ~ ell^kappa = ell^{1/2} there is no room to
send m/H_Z -> infinity while keeping m*log(Z) = o(ell)); this is checked by
directly evaluating, at finite N, the smallest integer m for which
H_Z^{m+1}/(m+1)! < 1, and comparing m/H_Z against e and log(D_0)/log(N)
against 1.
"""
import json
import mpmath as mp

mp.mp.dps = 60


def bonferroni_exponent(kappa, N, m_mult=2):
    """A(N) = log(D_0)/log(N) for the FIXED cutoff m = m_mult*ceil(sqrt(ell))."""
    ell = mp.log(N)
    logZ = ell ** kappa
    m = m_mult * mp.ceil(mp.sqrt(ell))
    logD0 = m * logZ
    return float(logD0 / ell), float(m), float(logZ)


def minimal_decaying_m(kappa, N):
    """Smallest integer m with H_Z^{m+1}/(m+1)! < 1, i.e. where the raw
    Bonferroni-error ratio first drops below 1 (necessary, not sufficient,
    for genuine decay as N grows)."""
    ell = mp.log(N)
    H_Z = 1 + ell ** kappa
    m = 1
    while True:
        val = H_Z ** (m + 1) / mp.factorial(m + 1)
        if val < 1:
            return m, float(H_Z)
        m += 1
        if m > 10 ** 7:
            return None, float(H_Z)


results = {"fixed_cutoff_table": [], "minimal_m_table": []}

Ns = [mp.mpf(10) ** p for p in (20, 100, 1000, 10000)]
kappas = [mp.mpf(x) for x in ("0.10", "0.30", "0.45", "0.49", "0.50", "0.60")]

for kappa in kappas:
    for N in Ns:
        A, m, logZ = bonferroni_exponent(kappa, N)
        results["fixed_cutoff_table"].append(
            {"kappa": float(kappa), "log10_N": float(mp.log10(N)),
             "m": m, "logZ": logZ, "A=log(D0)/log(N)": A}
        )

# Companion check at moderate N (factorial growth makes this expensive at huge N):
for kappa in kappas:
    N = mp.mpf(10) ** 60
    m_min, H_Z = minimal_decaying_m(kappa, N)
    ell = mp.log(N)
    logZ = ell ** kappa
    if m_min is not None:
        logD0 = m_min * logZ
        A = float(logD0 / ell)
        ratio = float(m_min / H_Z)
    else:
        A = None
        ratio = None
    results["minimal_m_table"].append(
        {"kappa": float(kappa), "log10_N": 60, "m_min": m_min,
         "H_Z": H_Z, "m_min/H_Z": ratio, "A_at_m_min": A}
    )

with open("hunts/prime_pair_error/artifacts/endpoint_half/result.json", "w") as f:
    json.dump(results, f, indent=2)

for row in results["fixed_cutoff_table"]:
    print(row)
print()
for row in results["minimal_m_table"]:
    print(row)
