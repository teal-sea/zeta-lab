"""Matrix-size estimate N ~ e*L*T#/2, T# = 2*pi*e^(S+0.5), for three envelope
constants S: Zhu's A_L, the separable out-of-band constant (Fejer degree 16),
and the comb-operator floor. Float64 probe (measured grade)."""
import math
from comb_operator import lam_max, A_L
from separable import primes_upto, prime_block

BETA = 0.5


def main():
    L0 = 1.19
    ps0 = primes_upto(math.exp(2 * L0))
    print("Fejer-degree tradeoff at L=1.19:",
          {D: round(sum(prime_block(p, L0, D)[2] for p in ps0), 4) for D in (4, 8, 16, 32, 64, None)})
    print(f"{'L':>6} {'N_zhu':>9} {'N_sep':>7} {'N_opt':>6} {'N_res':>6}")
    for L in (0.8, 1.0625, 1.19, 1.2825, 1.4, 1.6):
        ps = primes_upto(math.exp(2 * L))
        S = {"zhu": A_L(L), "sep": sum(prime_block(p, L, 16)[2] for p in ps), "opt": lam_max(L, 1200)}
        N = {k: math.e * L * 2 * math.pi * math.exp(v + BETA) / 2 for k, v in S.items()}
        n_res = math.e * L * 2 * math.pi * math.exp(2 * L) / 2
        print(f"{L:6.4f} {N['zhu']:9.3g} {N['sep']:7.0f} {N['opt']:6.0f} {n_res:6.0f}")


if __name__ == "__main__":
    main()
