# Fresh release opportunities, 2026-10-08

Read-only survey by `fresh_opportunities`. No repository edits, remote jobs, paid compute, or external messages. Only a subsecond local integer-count sweep. Local Zeta Lab snapshot is stale; parent owns authoritative Ghost state and collision checks. Read `/Users/thomas/AGENTS.md`, repository `CLAUDE.md`, `ROADMAP.md`, `ALIGNMENT.md`, the existing rogue-frontier portfolio, and mathbox literature-check instructions.

## Recommendation

Run a bounded **DFT finite-network parameter audit** now; keep **constructive odd-degree finite-field splitting** as the higher-value algorithmic route; reserve **two-generation prime-factor laws** as the deeper analytic route. These are materially different mechanisms. The DFT signal is a possible improvement to a released construction, not practical FFT software or a claimed breakthrough. Do not automatically replace an already promising Ghost class-group route with the speculative third item.

The actual fresh release is [openai/math](https://github.com/openai/math), October 6 collection, with subsequent October 7 manuscripts. It has mixed verification status. The catalogue is a discovery index, not proof. I extracted primary manuscript source via the GitHub connector after web PDF loading failed. Mutable `main` reads are pinned below by file blob SHA, not by a collection commit SHA. No source-cache ingestion was performed.

## 1. Smaller finite Fourier network: immediate positive discriminator

Source: [An explicit power saving for the exact discrete Fourier transform, September 25](https://github.com/openai/math/tree/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/build). Introduction blob `22171e11e7c43a367b823725514c7f424527217d`; network blob `991c7706b7a03f45fbf3ba22bfb4372bf111fb4a`. Read introduction and network through the finite-network interface, plus beginning of indexing. Not a full proof audit.

The construction fixes h=100. Its formulas are:

```
v = choose(h,3)
d = choose(h-3,3) + 3(h-3)
m = h^3
W = 2v^3 + 3v^2(vd+h+1)
P = next power of two >= W
Delta = 2v^2(v-3h(h+1))
theta = log(m-Delta/P)/log(m)
```

A 179-case integer sweep, h=22,...,200, found its best exponent at h=24:

| Quantity | h=24 candidate | h=100 published |
|---|---:|---:|
| m | 13824 | 1000000 |
| W | 34666942577344 | 1873807244643542670000 |
| P | 35184372088832 | 2361183241434822606848 |
| Delta | 1835266048 | 6871402692000000 |
| 1-theta, floating only | 3.957610023859113e-10 | 2.106438430040181e-13 |

That is roughly 1879 times the exponent saving and roughly 54 million times fewer physical roles. It still uses an absurdly large finite construction. The source's full runtime is O(n(log n)^theta(log log n)^(4-theta)); an advertised pure-log exponent must be strictly weaker than 1-theta to absorb the loglog factor.

**Exact target:** prove the finite-interface lemma uniformly for integer h>=22, and transport it through the unchanged batching/compiler/synchronization arguments. The strict-saving inequality is exactly (h-1)(h-2)>18(h+1), satisfied at h>=22. The residual proof uses coordinate vectors outside supports of size at most six, apparently compatible with h=24. This observation is not yet a theorem: inspect every fixed constant and any hidden h-specific restriction downstream.

**First discriminator:** independently rederive all wire counts and nondegenerate residual labels at h=24, especially stage-two reversed scheduling and restoration of arbitrary auxiliary data. Then enclose theta with Arb. Do not allocate the arrays. Falsification should try missing ordered edges, alternating binary residual forms, non-restored auxiliary roles, and scalar-preparation costs.

**Shareable threshold:** a proved parameterized finite-network theorem plus an exact count checker and independent proof audit; better still replace the triple family with a smaller combinatorial design. A floating optimum alone is not shareable mathematics. This is a new-proof/parameter-extension candidate whose novelty has not been established. Finite bounded scans do not prove global optimality.

Reproduce the bounded observation:

```python
from math import comb, log, log1p
rows = []
for h in range(22,201):
    v = comb(h,3)
    d = comb(h-3,3) + 3*(h-3)
    W = 2*v**3 + 3*v*v*(v*d+h+1)
    P = 1 << (W-1).bit_length()
    Delta = 2*v*v*(v-3*h*(h+1))
    gap = -log1p(-Delta/(P*h**3))/log(h**3)
    rows.append((gap,h,W,P,Delta))
print(max(rows))
```

## 2. Useful deterministic splitter, not another primality corollary

Source: [Deterministic Polynomial Factorization over Prime Fields, October 4](https://github.com/openai/math/tree/main/preprints/Deterministic-Polynomial-Factorization-over-Prime-Fields-October-4-2026/build). Introduction blob `24bb00b878eac7882bfb3cbb862acf1903cf2693`, extracted completely. The released theorem claims exponent 10^12, relying on a companion uniform Hecke zero-free theorem, not just zeta 7/8.

The isolated algebraic reduction accepts auxiliary primes ell_q for each prime q<=n, with ell_q=1 mod12q and p^((ell_q-1)/q)!=1 mod ell_q. Its complexity is polynomial in their numerical sizes E, not log E. This is a clean interface for a constructive algorithm independent of the new analytic theorem once certificates for ell_q are supplied.

**Question:** can the odd-degree separator be specialized into a genuinely usable, certificate-producing algorithm for q=3 or 5? The source identifies its substantive step as division of ramification divisor classes on Y^q=F(X), bounded extension fields, and an infinity-divisor lattice obstruction. This uses existing exact finite-field, algebraic-curve and independent-PARI habits rather than generic theorem mining.

**First discriminator:** reproduce one totally split cubic/quintic over a small prime by the paper's geometric mechanism with unknown roots represented by a quotient algebra. Require no hidden polynomial-factorization oracle. Compare output to independently chosen known roots. Audit norm-equation and divisor-division subroutines before increasing p. Kill or narrow the route if it requires most of the full enormous construction even at q=3.

**Shareable threshold:** a simplified odd-degree separator theorem with explicit operation count and exact executable witnesses; demonstrate a real advantage in some defined deterministic regime. Simply implementing the already-known even-degree tournament splitter with a quadratic nonresidue is not new: the source explicitly credits Ronyai 1988. The full factorization claim itself is upstream, not ours. Novelty remains unverified.

## 3. Prime-factor laws at two generations

Source: [The Poisson–Dirichlet Law for Prime Predecessors, September 24](https://github.com/openai/math/tree/main/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build), introduction blob `79950676c100e2d2d9252cc5465707a0d8f6c891`, extracted completely. It proves a claimed one-generation law and expressly says recursive independence for Pratt trees is additional. [Ford–Konyagin–Luca, Prime chains and Pratt trees, 2010](https://arxiv.org/abs/0904.0473) is prior art, including the branching-random-walk model.

**Question:** prove a fixed-depth joint law, or a useful weighted two-generation marginal, for q|p-1 and r|q-1. This addresses certificate-tree geometry rather than restating a distribution of the largest factor of p-1.

**First discriminator:** extract the exact marked Type-II/endpoint contracts and test whether they survive nested divisibility constraints. In parallel, exact small prime-tree data should test conditional second-generation distributions after controlling q size; naive pooled independence is not an adequate null. A failure of the proof transfer is only a method obstruction, never a counterexample to the joint-law conjecture.

**Shareable threshold:** a proved finite-depth law or quantitative estimate sufficient for a rigorous certificate-generation complexity statement. Ordinary one-level Dickman smoothness is already in the release. No assertion about full Pratt-tree height follows from one-generation convergence. Rank this below existing local opportunities until the transfer survives its first audit.

## Search boundary and blockers

Primary searches covered the release catalogue, exact source introductions and named dependency structure. Bounded backward prior-art search located Ford–Konyagin–Luca and verified the release's explicit distinctions from classical factorization and transform results. Some general search queries returned irrelevant results; those are not evidence of absence. No comprehensive MathSciNet/zbMATH or forward-citation search, no independent novelty reviewer, no complete source dependency replay. Therefore none of the proposed extensions is labeled apparently new. The parent should use Ghost's current literature ledger and current owners before launch.

Practical Fourier stability is an interesting *different* problem, but the new paper explicitly excludes finite precision; bounded-coefficient and well-conditioned lower bounds must be respected. Do not market the h=24 signal as a stable fast FFT. Similarly, the class-number h<=1500 collection remains conditional and must be compared against Cremona–Sutherland 2023 rather than presented as the first even-class-number classification.
