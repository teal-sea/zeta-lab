# Independent audit: parameterized exact DFT network

## Claim and primary verdict

For each fixed integer h>=22, use the manuscript's triple-indexed network
with v=binom(h,3), m=h^3, d=binom(h-3,3)+3(h-3),
W=2v^3+3v^2(vd+h+1), Delta=2v^2(v-3h(h+1)), and P the least
power of two >=W. The asserted tensor-transform exponent is
theta=log_m(m-Delta/P). The all-length complex DFT consequence at h=24 is
O(n(log n)^(1-38/10^11)) exact field and logarithmic-word address operations,
given the specified root of unity of computable order <1024n^3.

**Primary verdict: conditional on a named input.** The parameter extension
and exact exponent arithmetic pass this independent written-proof audit.
The all-length consequence is conditional on the pinned manuscript's
uniform local compiler (`loc:compiler`), synchronized transform
(`prop:tensor-fourier`), and all-length/root transport being valid in their
stated exact arithmetic model. Their interfaces and the relevant proofs
were inspected, and no new h-dependent obligation or contradiction was found.
This pass is not a complete independent verification, implementation, or
formalization of that entire upstream algorithm.

There is no identified missing implication inside the parameter extension.
In particular, h need not be even, h=22 is included, all initial auxiliary
values are arbitrary, and h is fixed before the input length varies.

## Revision and scope

Audited source: OpenAI, *An explicit power saving for the exact discrete
Fourier transform*, September 25, 2026; supplied pinned collection commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
The source question was applicability of the exact-width compiler and
transport to a changed tensor exponent, not novelty of the whole algorithm.
The local TeX snapshots were read; this audit did not independently fetch
the repository commit. SHA256 values for the four actual snapshots are
recorded in `check-results.json`. Source authentication thus uses the supplied
revision provenance, while theorem extraction and parameter application were
checked separately. The source's source-internal `motif` and `exactfourier`
bibliographic leaves were not used as substitutes for their reproduced proofs.

Author proof reviewed: `routes/dft/PROOF.md`, SHA256
`632eff2fe4535372f6e09a22482ae48afff71e061bfca1fdb6ac58539a865523`.
Producer checker inspected: `routes/dft/verify.py`, SHA256
`87ded97dfcb8a3ba752dd4f59263506be233934bb6ae18a17efb2ac3d4593122`.
`RESULTS.md` was not present at audit time; this verdict attaches to the
actual proof and source leaves above, not a future summary.

## Dependency graph

1. Triple incidence identity RG+JV=I [internal algebra].
2. Eight-row update and its inverse restore arbitrary auxiliary values
   [internal algebra; separate finite exact check].
3. Three coordinate stages give (X,Y)->(-Y,X) [internal algebra; independently
   executed for h=3 and h=4, including 48 distinct invocations at h=4].
4. Gate labels are nondegenerate and nested, with listed residuals
   [internal binary bilinear algebra reconstructed from `net:labels`].
5. Residuals have orthonormal bases [internal proof, h>6]; their dimensions
   yield s=Wm-Delta [internal count].
6. Walsh-conjugate frame identities convert these residuals into directional
   copies of C and restore all physical-role interfaces [internal algebra].
7. Padding to P and exact recursive batching yield lambda=m-Delta/P,
   t(k)<=A_h+lambda t(floor(k/m)) [internal cost/rounding argument, using
   the explicitly described prefix traversal].
8. Tensor bound -> all-length DFT bound [named upstream compiler and
   transport inputs; interface application checked].
9. Exact rational inequalities give theta<1-39/10^11 at h=24; absorbing
   the fixed loglog power gives exponent 1-38/10^11 [internal analysis
   plus independently recomputed rational certificate].

## Obligation matrix

| Obligation | Status | Decisive check |
|---|---|---|
| Ordered side wires and adjacency count | Passed | For fixed S, intersection 0 gives binom(h-3,3), intersection 2 gives 3(h-3); both orientations are separate storage. |
| Scalar coefficients and inverse chronology | Passed | RG coefficient is (intersection-1)/2; JV cancels only 0 and 2. Inverting stage 2 reverses rows as well as signs. |
| Repeated coordinate products | Passed | Each invocation is coordinatewise addition on its complete varying-index list; disjoint invocations within each stage therefore implement the same global bank shear. |
| Arbitrary auxiliary restoration | Passed | Initial JA+Rc is subtracted before dependent additions and final restoration; no zero-register assumption. |
| Nondegenerate labels | Passed | Norm-one triple lines and their orthogonal complements split nondegenerately; tensor products preserve nondegeneracy. |
| Orthonormal residual bases | Passed | Supports <=6 leave a coordinate unit for h>6. Tensor supports 3^j<h^j leave units in nonzero B and Q-perp. Nonalternating nondegenerate binary forms admit the stated plane-absorption basis. |
| Edge residual and direction count | Passed | Only center row 3->4 decreases, by h, once for each of 3v^2(h+1) wires; losses cost twice. |
| Terminal phase and whole-array interface | Passed | u has odd weight 27; q_(u-perp)-q_u=wt(x)+2[u dot x] mod4, so only a known translation remains. |
| Power-of-two physical padding | Passed | Each added role pays m directions, leaving Delta unchanged; replacing P by W without padding would not justify exact batching. |
| Floors, thresholds and recursive descent | Passed | K=m(a+1), k>=K implies f>=a+1 and k-f>=a; f<k. Spectator r<m costs only an h-dependent constant per entry. |
| Scalar/table/address costs | Passed within model | Gates, bases and tables are fixed for fixed h. Prefix traversal visits O(2^k) nodes without an f multiplier. Table construction is charged as a fixed constant. |
| Upstream all-length algorithm correctness | Conditional | Relevant raw proofs inspected; not fully reimplemented or formalized in this audit. |
| Exact h=24 exponent | Passed | Independent rational series bound ln(13824)<477/50 and epsilon>(39/10^11)(477/50). |
| Practical or bit-complexity improvement | Out of scope | Unrestricted exact complex values; enormous fixed tables and constants. |
| Novelty/global optimality of h=24 | Not addressed | This is a parameter improvement of the cited construction; no priority conclusion. |

## Critical derivations and attempted falsification

The residual table is stable under changing h: for a side edge 2->5,
t_X is a norm-one vector orthogonal to t_Y, so t_Y-perp splits as
<t_X> orthogonal-sum <t_X,t_Y>-perp. This is the delicate nesting;
an arbitrary adjacent-graph substitution would not suffice. Every tensor
factor in the other residuals is nondegenerate, and every nonzero factor
contains a unit vector under h>6. The plane-absorption formula is valid:
if w is unit and orthogonal to a symplectic plane p,q, the three vectors
w+p, w+q, w+p+q have diagonal Gram matrix I_3. No parity assumption is hidden.

The terminal signed dimension increase is Wm-2v^3. Converting signed
changes to absolute costs adds 6v^2(h+1)h. Thus Delta is exactly
2v^2(v-3h(h+1)), with the factor two on losses essential.
For h>=3 its sign is the sign of h^2-21h-16, whose integer transition
is between 21 and 22. Also 0<Delta<2v^3<=W<=P for h>=22, giving
m-1<lambda<m and hence 0<theta<1.

I independently wrote `check.py`, without importing the producer's
checker. It executes the complete three-stage scalar exchange at h=3
and h=4 with distinct nonzero rational auxiliary values in each invocation.
All auxiliary values return exactly, and all 64 entries per bank at h=4
have the claimed signed exchange. The mutant with a forward instead of
inverse middle stage fails. This tests a genuine chronological requirement,
not merely the RG+JV matrix identity. It does not test the huge h=24
framed algorithm by executing it.

The checker recomputes counts and batching boundary cases for h=7,...,128.
The universal statements depend on the written inequalities, not that range.
At h=24 it independently obtains:

- m=13824, W=34666942577344, P=35184372088832=2^45;
- Delta=1835266048;
- epsilon=Delta/(mP)=448063/118747255799808;
- a positive rational partial sum through degree 64 gives
  exp(477/50)>13824, hence ln(m)<477/50;
- epsilon>(39/10^11)(477/50), while the analogous 40/10^11 inequality
  fails for this bound, rejecting an unjustifiably stronger exponent.

Since -ln(1-epsilon)>epsilon,
1-theta=-ln(1-epsilon)/ln(m)>39/10^11. A fixed power of loglog n
is eventually bounded by (log n)^(1/10^11), so the stated pure-log
exponent follows. It is an eventual big-O estimate with a very large,
unspecified crossover. The first tensor recursion threshold at h=24 is
k=635904; even one input array there has 2^635904 entries. Nothing here
supports a feasible-speedup claim.

## Source leaves and reproducibility

- `routes/dft/sources/network.tex`: `net:scalar` (line 66), `net:labels`
  (253), `net:residuals` (275), `net:finite-interface` (370), `net:indexing`
  (422), `net:padding` (469), `net:tensor-bound` (480).
- `routes/dft/sources/local.tex`: `loc:compiler` (23). Its contract concerns
  C, arbitrary local width r and supplied roots; it has no h/m/P assumption.
- `routes/dft/sources/synchronization.tex`: `prop:tensor-fourier` (62).
  Replacing theta is valid because k<=ell and all sectors total width R.
- `routes/dft/sources/all-lengths.tex`: `eq:working-transform` (91),
  `eq:master-root` (112), `eq:root-size` (116), final estimates.
  The root order and polylogarithmic local preparation are unaffected.

Run from the task workspace:

```sh
zeta-research/.venv/bin/python audits/dft/check.py
```

The run completed successfully. Durable output: `check-results.json`.
Only files under `audits/dft` were written. No paid compute, large arrays,
Git changes, or remote model runs were needed.

## Strongest safe statement and next check

The finite-network parameter extension has survived an independent written
audit and independent finite exact checks. Assuming the cited compiler and
transport, it gives the claimed improved exact-arithmetic DFT exponent.
It is not kernel-checked and is not an empirical faster Fourier implementation.

The cheapest useful next check is a separate audit or formalization of the
upstream exact-width Toeplitz/replay compiler, which is shared by the original
theorem and this parameter improvement. Re-running larger scalar examples
does not resolve that dependency or establish novelty.
