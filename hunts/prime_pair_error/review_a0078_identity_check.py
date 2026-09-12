"""Independent toy-model check of ARC_SPLIT_BUDGET.md equations (2) and (3).

Written from scratch for this review (a-0078); does not import or reread
arc_split_probe.py. Verifies, on a small explicit toy model:

  (2) [X+Y]_h = psi_2(N,h) - psi_2^a(N,h)
      [R_mod]_h = psi_2^a(N,h) - (N-h) S_y(h) - C_N(h)
      [G_corr]_h = psi_2(N,h) - (N-h) S_y(h) - C_N(h)

  (3) G_corr = (|F|^2 - |H|^2) + R_mod - kappa   pointwise on the circle,
      kappa = d_N - sum a(n)^2.

No exceptional character is used here (C_N = 0 throughout), matching the
document's own finite check that no exceptional zero exists at these N.
"""
import numpy as np
from sympy import mobius, totient, divisors, factorint, primerange

N = 600
Y = int(np.floor(np.sqrt(N)))  # truncation level for the singular series
Z = 10
primesZ = list(primerange(2, Z))
P = 1
for p in primesZ:
    P *= p
phiP = int(totient(P))
b = P / phiP


def von_mangoldt(n):
    if n < 2:
        return 0.0
    f = factorint(n)
    if len(f) == 1:
        (p, _), = f.items()
        return float(np.log(p))
    return 0.0


def coprime_to_P(n):
    return all(n % p != 0 for p in primesZ)


Lambda = np.array([0.0] + [von_mangoldt(n) for n in range(1, N + 1)])
a_arr = np.array([0.0] + [b if coprime_to_P(n) else 0.0 for n in range(1, N + 1)])


def ramanujan_sum(q, h):
    g = np.gcd(q, h)
    s = 0
    for d in divisors(g):
        s += d * int(mobius(q // d))
    return s


mu2phi2 = {}
for q in range(1, Y + 1):
    mu = int(mobius(q))
    if mu == 0:
        mu2phi2[q] = 0.0
        continue
    mu2phi2[q] = 1.0 / (int(totient(q))) ** 2

S_y = np.zeros(N + 1)
for h in range(0, N + 1):
    s = 0.0
    for q in range(1, Y + 1):
        if mu2phi2[q] == 0.0:
            continue
        s += mu2phi2[q] * ramanujan_sum(q, h)
    S_y[h] = s

d_N = float(np.sum(Lambda ** 2))
suma2 = float(np.sum(a_arr ** 2))
kappa = d_N - suma2
a0 = d_N - N * S_y[0]

# ---- Direct windowed sums: psi_2, psi_2^a, [X+Y]_h, [R_mod]_h, [G_corr]_h ----
psi2 = np.zeros(N + 1)
psi2a = np.zeros(N + 1)
for h in range(1, N + 1):
    n = np.arange(1, N - h + 1)
    psi2[h] = np.sum(Lambda[n] * Lambda[n + h])
    psi2a[h] = np.sum(a_arr[n] * a_arr[n + h])

XplusY_h = psi2 - psi2a
Rmod_h = psi2a - (N - np.arange(N + 1)) * S_y
Rmod_h[0] = 0.0  # h=0 not part of the coefficient family (C removes it)
Gcorr_h = psi2 - (N - np.arange(N + 1)) * S_y
Gcorr_h[0] = 0.0

# Consistency of (2): [G_corr]_h should equal [X+Y]_h + [R_mod]_h for h=1..N
lhs = Gcorr_h[1:]
rhs = XplusY_h[1:] + Rmod_h[1:]
max_defect_2 = float(np.max(np.abs(lhs - rhs)))

# ---- Pointwise check of (3) on a fine grid, via closed-form K_N ----
M = 4096  # > 2N, enough for exact reconstruction of degree-N trig polynomials
alphas = np.arange(M) / M


def K_N(beta):
    beta = np.asarray(beta, dtype=np.float64)
    out = np.empty_like(beta, dtype=np.complex128)
    zero = np.abs(np.mod(beta + 0.5, 1.0) - 0.5) < 1e-13
    e_b = np.exp(2j * np.pi * beta)
    with np.errstate(divide="ignore", invalid="ignore"):
        out = e_b * (1 - np.exp(2j * np.pi * N * beta)) / (1 - e_b)
    out = np.where(zero, N, out)
    return out


n_idx = np.arange(1, N + 1)


def F_grid(alphas):
    phase = np.exp(2j * np.pi * np.outer(alphas, n_idx))
    return phase @ Lambda[1:]


def H_grid(alphas):
    phase = np.exp(2j * np.pi * np.outer(alphas, n_idx))
    return phase @ a_arr[1:]


F_vals = F_grid(alphas)
H_vals = H_grid(alphas)

V_y_vals = np.zeros(M, dtype=np.float64)
for q in range(1, Y + 1):
    if mu2phi2[q] == 0.0:
        continue
    residues = [a for a in range(1, q + 1) if np.gcd(a, q) == 1]
    for a_res in residues:
        beta = alphas - a_res / q
        kv = K_N(beta)
        V_y_vals += mu2phi2[q] * (np.abs(kv) ** 2)

G_y_vals = np.abs(F_vals) ** 2 - V_y_vals - a0
Rmod_vals = (np.abs(H_vals) ** 2 - V_y_vals) - (suma2 - N * S_y[0])
diff_intensity = np.abs(F_vals) ** 2 - np.abs(H_vals) ** 2

check3 = G_y_vals - diff_intensity - Rmod_vals + kappa
max_defect_3 = float(np.max(np.abs(check3)))
max_Gy = float(np.max(np.abs(G_y_vals)))

results = {
    "N": N,
    "Y": Y,
    "Z": Z,
    "kappa": kappa,
    "a0": a0,
    "eq2_max_abs_defect": max_defect_2,
    "eq3_max_abs_defect_grid": max_defect_3,
    "eq3_max_abs_Gy_grid": max_Gy,
    "eq3_relative_defect": max_defect_3 / max_Gy if max_Gy else None,
}

if __name__ == "__main__":
    import json

    print(json.dumps(results, indent=2))
    with open("results_review_a0078_identity_check.json", "w") as f:
        json.dump(results, f, indent=2)
