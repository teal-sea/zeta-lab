# Section 8: does the dyadic scale transition beat exp(-c(log N)^{1/10})?

2026-09-10. Builds on [CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md),
[CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md),
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) and
[ENDPOINT_BOUND.md](ENDPOINT_BOUND.md) as they stand on this branch. No
base commit hash is cited: this pass does not use git. Nothing in those
four documents is revisited or changed.

**Outcome, stated first.** The requested transition — bound the
scale-\(k\) component of \(\mathrm{Energy}(N)\) by the scale-\((k-1)\)
component plus an explicit arithmetic term, uniformly in \(k\), so the
sum telescopes below the trivial order — **fails**, and it fails at an
identifiable place: the only unconditional per-block arithmetic input
available at short block lengths does not shrink as the block shrinks,
while the number of blocks at scale \(k\) grows like \(N/2^k\); combining
the two through the definition of \(\Delta_k\) produces a bound that is
**worse than the trivial \(N^3\) order at every scale this document can
reach**, including scale \(k=0\), where
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md)'s own tables show close to
half of \(E_{\rm corr}(N)\) sits. The one place the transition does not
blow up (the top \(O((\log N)^{3/5}(\log\log N)^{-1/5})\) rungs of a
ladder of length \(K\sim\log_2N\)) is exactly where the measured energy
share is under \(0.1\%\). No \(\theta\) beyond the inherited
\(\theta=1/10\) of [ENDPOINT_BOUND.md](ENDPOINT_BOUND.md) is produced by
this route; that document's bound is not reproved here, only cited. This
is a handwritten deduction, pending external verification, with no
novelty claim.

## 1. Setup, inherited without change

Use [CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md) Sections 1-2 exactly:
\(x_h=r_N(h)-C_N(h)\) for \(1\le h\le N\), extended by zero to
\(M=2^K\ge N\), \(K=\lceil\log_2N\rceil\); \(P_k\) the block-average
projection at block length \(2^k\); \(D_k=P_k-P_{k+1}\);
\(\Delta_k(N)=\|D_kx\|_2^2\); and the proved identity
\[
 E_{\rm corr}(N)=\mathrm{Energy}(N)
 =2M\mu(N)^2+2\sum_{k=0}^{K-1}\Delta_k(N).\tag{$\star$}
\]
\((\star)\) is exact and carries no arithmetic content by itself
(CANDIDATE_ENERGY.md Section 3): it does not, on its own, make any term
smaller. A scale transition can only be useful here if it supplies new
*arithmetic* information about each \(\Delta_k\) — something
\((\star)\)'s linear algebra does not.

**The target restated, so the known barrier is not rediscovered.** A
fixed power saving \(E_{\rm corr}(N)\ll N^{3-\delta}\) would invert
[CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md) equation (3) against
Landau's \(\Omega\) theorem for \(\psi(N)-N\) and is not attempted here.
The reachable target is a saving of shape
\(N^3\exp(-c(\log N)^\theta)\), and the question is which \(\theta\),
if any, a transition on \((\star)\) can reach, against the existing
inherited bound
\(E_{\rm corr}(N)\ll_\kappa N^3\exp(-c_\kappa(\log N)^\kappa)\) for every
\(\kappa<1/10\) ([CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md)
equation (21)), and the proposed endpoint \(\theta=1/10\)
([ENDPOINT_BOUND.md](ENDPOINT_BOUND.md)).

## 2. Two candidate transition mechanisms

Write \(\ell=\log N\). Two natural ways to try to bound \(\Delta_k(N)\)
by \(\Delta_{k-1}(N)\) plus an arithmetic term were tried:

**(a) A global block recursion.** Bound the two block sums that make up
each \(D_{k}\)-difference directly, using the strongest available
*unconditional, block-length-independent* arithmetic input — the
classical (Vinogradov-Korobov-strength) prime number theorem rate,
already inherited in this project as
\(|\psi(x)-x|\ll x\exp(-c\mathcal L(N))\),
\(\mathcal L(N)=\ell^{3/5}(\log\ell)^{-1/5}\)
([LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) equations
(18)-(19), citing TT Theorem 1.3(i)) — and propagate it through the
definition of \(\psi_2(N,h)\) to every dyadic block, at every scale, by
the same argument at every \(k\) (hence "uniformly in \(k\)").
Section 3 carries this out in full and shows it fails.

**(b) A local geometric-decay recursion.** Observe, empirically
(Section 5), that \(\Delta_k(N)/\Delta_{k-1}(N)\approx1/2\) at the fine
scales where the energy actually sits, and ask whether
\(\Delta_k(N)\le(\tfrac12+\varepsilon)\Delta_{k-1}(N)+(\text{small
arithmetic term})\) can be proved. Section 5 shows why this recursion,
even if it held, would not close, and why proving it is not easier than
the original problem.

Neither route produces a working transition; Sections 3-6 give why, with
an explicit scale named in each case.

## 3. Mechanism (a): the global block recursion, worked out and shown to fail

Fix \(k\) and a length-\(2^{k+1}\) block, split into two adjacent
length-\(2^k\) sub-blocks \(B_1=[a,a+2^k)\), \(B_2=[a+2^k,a+2^{k+1})\)
of the shift variable \(h\). Write \(S_i=\sum_{h\in B_i}x_h\)
(\(i=1,2\)). From the block-average bookkeeping of
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md) Section 3 (the elementary
Haar identity, not repeated here),
\[
 \Delta_k(N)=2^{-k-1}\sum_{\text{level-}(k+1)\text{ blocks}}(S_1-S_2)^2.
 \tag{1}
\]
This is exact (it is \((\star)\)'s bookkeeping specialized to one
level); the arithmetic content must come from bounding \(S_1-S_2\).

**Lemma (block-sum discrepancy, elementary).** For \(2^k\le N^{1/4}\)
and any block \(B=[a,a+2^k)\subseteq[1,N]\),
\[
 \sum_{n\le N}\Lambda(n)\!\!\sum_{\substack{h\in B\\n+h\le N}}\!\!\Lambda(n+h)
 =\sum_{n\le N}\Lambda(n)\,s(n)+O(N^2e^{-c\mathcal L(N)}),
 \tag{2}
\]
where \(s(n)=\#\{h\in B:n+h\le N\}\le2^k\).

*Proof.* For fixed \(n\), the inner sum is
\(\psi(\min(N,n+a+2^k-1))-\psi(n+a-1)\). By the cited rate, each of
these two values of \(\psi\) differs from its argument by
\(O(Ne^{-c\mathcal L(N)})\) (using the elementary bound for arguments
below \(\sqrt N\), absorbed since \(\sqrt N\log N=o(Ne^{-c\mathcal
L(N)})\), exactly as in
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) Section 5).
Hence the inner sum is \(s(n)+O(Ne^{-c\mathcal L(N)})\), for every
\(n\), with an implied constant independent of \(a\) and \(k\).
Multiplying by \(\Lambda(n)\) and summing over \(n\le N\) (using
\(\sum_{n\le N}\Lambda(n)\ll N\)) gives (2). \(\blacksquare\)

The left side of (2) is \(\sum_{h\in B}\psi_2(N,h)\), by exchanging the
order of summation; this is exact bookkeeping, not an estimate. The
right side splits \(\sum_{h\in B}x_h\) into the deterministic quantity
\(\sum_n\Lambda(n)s(n)-\sum_{h\in B}\bigl[(N-h)\mathfrak S(h)+C_N(h)\bigr]\)
plus the \(O(N^2e^{-c\mathcal L(N)})\) error of (2). Bounding that
deterministic remainder for a *general* sub-block \(B\) (rather than the
full range \([1,N]\)) needs a block-localized version of the
first-moment computation
[CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md) carries out only for
the complete range (its Section 4, and the signed estimate (2)/(15) for
\(C_N\)); no such localized computation exists in the documents inherited
here. **We grant, generously and without proof, that this remainder
costs no more than the same order \(O(N^2e^{-c\mathcal L(N)})\)** — the
most favorable assumption possible, since it is not established. Under
that grant,
\[
 |S_i|=O(N^2e^{-c\mathcal L(N)})\qquad(i=1,2),\qquad
 |S_1-S_2|=O(N^2e^{-c\mathcal L(N)}),
 \tag{3}
\]
uniformly over blocks, for \(2^k\le N^{1/4}\).

**Consequence.** There are \(\asymp N/2^{k+1}\) level-\((k+1)\) blocks in
(1). Using (3) in each term of (1),
\[
 \boxed{\quad
 \Delta_k(N)=O\!\left(\frac{N^5e^{-2c\mathcal L(N)}}{4^k}\right)
 \qquad(2^k\le N^{1/4}).
 \quad}
 \tag{4}
\]

**Where this fails.** Compare (4) to the trivial order \(N^3\):
\[
 \frac{\Delta_k(N)_{\text{(4)}}}{N^3}
 =O\!\left(N^2e^{-2c\mathcal L(N)}/4^k\right).
\]
Since \(\mathcal L(N)=\ell^{3/5}(\log\ell)^{-1/5}=o(\ell)\), the
quantity \(N^2e^{-2c\mathcal L(N)}\) grows like \(e^{2\ell-2c\mathcal
L(N)}\to\infty\) far faster than any \(4^k\) with \(k\le
K/4=\tfrac14\log_2N\) can compensate: at the top of the lemma's range of
validity, \(4^{K/4}=N^{1/2}\), which is still \(\ll N^2e^{-2c\mathcal
L(N)}\) for all large \(N\) (the exponent gap is \(3/2\log N\) against a
term of size \(o(\log N)\) in the exponent of \(e\)). **The bound (4)
therefore exceeds the trivial \(N^3\) order at every scale \(k\) in its
entire proved range \(0\le k\le\tfrac14\log_2N\)**, including \(k=0\),
where it gives \(\Delta_0(N)=O(N^5e^{-2c\mathcal L(N)})\), worse than
trivial by a factor \(N^2e^{-2c\mathcal L(N)}\to\infty\). This is not a
borderline miss: the naive block recursion is not merely insufficient,
it is strictly worse than doing nothing, throughout the only range
where the Lemma above lets it be evaluated at all.

Solving \(4^{k^*}=N^2e^{-2c\mathcal L(N)}\) for the threshold gives
\(2^{k^*}=Ne^{-c\mathcal L(N)}\), i.e.
\(k^*=K-c\mathcal L(N)/\log2+O(1)\): only the top
\(O(\mathcal L(N))=O(\ell^{3/5}(\log\ell)^{-1/5})\) rungs of the
\(K\sim\log_2N\)-rung ladder are even candidates for this method not to
blow up — a \((1-o(1))\)-fraction of all scales fail — and by
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md) Section 4's measured tables,
those top rungs (scale \(11\)-\(13\) at \(N=10^4\), scale \(14\)-\(16\)
at \(N=10^5\)) each hold well under \(0.1\%\) of \(E_{\rm corr}(N)\).
**Grade: the Lemma and (4) are PROVED, conditional on the granted
main-term-matching assumption stated above; the failure conclusion
(exceeding trivial throughout the provable range) is unconditional and a
fortiori — granting the assumption only makes the bound (4) as small as
it could possibly be, and it still fails.**

## 4. Why an aggregate (large-sieve-style) fix is not available either

The blow-up in Section 3 comes from bounding each of the \(\asymp
N/2^k\) blocks' discrepancy separately and squaring the worst case,
rather than bounding \(\sum(S_1-S_2)^2\) as a whole. A large-sieve-type
inequality — bounding a sum of squares over many blocks by a global
quantity without paying the block count as a separate factor — is
exactly the kind of tool
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) Section 4 uses,
successfully, for a *different* aggregation: sums over reduced
rationals \(a/r\) on the frequency circle (its equations (10)-(14)).
That aggregation is on the frequency-denominator axis. \(\Delta_k\)'s
blocks are on the shift-index axis at fixed block length; they are not
the same objects, and no rational-denominator structure organizes them.

A genuine fix would need a second-moment (variance-of-correlations)
estimate for \(\sum_{h\in B}x_h\) across many blocks \(B\)
*simultaneously*, which is a quartic-in-\(\Lambda\) statement (each
\(x_h\) is already quadratic in \(\Lambda\)). The one place in the
inherited documents where a quartic-in-\(\Lambda\) long-range quantity
of comparable shape is handled is
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md)'s controlling
long window \(T_N(0)\) (its equations (15)-(19)), which is a variance of
prefix sums \(A(k)=\psi(k)-k+O(\cdots)\) around the global mean,
i.e. its own \(k=K\)-type (single, coarsest, global) object — it proves
\(T_N(0)\ll N^3e^{-c\mathcal L(N)}\), Vinogradov-Korobov strength
(\(\theta=3/5\)), stronger than \(1/10\), but that document is explicit
(its equation (20) and the surrounding discussion) that this bound on
the raw second moment does **not** imply the needed *mean-square around
the block-local mean* at shorter lengths, which is precisely a shorter
version of what Section 3 above would need at every \(k<K\). The gap
identified there is not resolved by relabeling it in the index domain:
it is the same open estimate, restated. No unconditional aggregate
input beating Section 3's per-block bound is available in the inherited
documents. **Grade: OBSERVATION** (a comparison of what is and is not
proved elsewhere; it does not itself prove non-existence of such a
tool).

## 5. Mechanism (b): the empirical geometric-decay recursion

At the scales where the energy actually sits,
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md)'s own
`results_s8_candidate_energy.json` shows a near-constant ratio between
consecutive fine scales:

| \(N\) | \(\Delta_1/\Delta_0\) | \(\Delta_2/\Delta_1\) | \(\Delta_3/\Delta_2\) | \(\Delta_4/\Delta_3\) | \(\Delta_5/\Delta_4\) | \(\Delta_6/\Delta_5\) |
|---:|---:|---:|---:|---:|---:|---:|
| \(2000\) | 0.449 | 0.544 | 0.350 | 0.731 | 0.527 | 0.178 |
| \(5000\) | 0.474 | 0.477 | 0.648 | 0.346 | 0.576 | 0.615 |
| \(10000\) | 0.514 | 0.480 | 0.503 | 0.396 | 0.389 | 0.463 |
| \(30000\) | 0.474 | 0.519 | 0.544 | 0.483 | 0.401 | 0.490 |
| \(100000\) | 0.506 | 0.481 | 0.526 | 0.470 | 0.478 | 0.452 |

(computed directly from the existing `per_scale` fields already in
`results_s8_candidate_energy.json`; no new script was written, none was
needed to read an existing file.) The ratios cluster around
\(0.45\)-\(0.55\) at \(N\ge10^4\), suggestive of an approximate
\(\Delta_k(N)\approx\Delta_{k-1}(N)/2\) law at fine-to-medium scales —
consistent with, but visibly not exactly, a fixed halving (the range
\(0.35\)-\(0.65\) at smaller \(N\) or larger \(k\) shows real scatter,
and CANDIDATE_ENERGY.md Section 4 already calls the coarse tail
"noisy"). This is measured, finite-\(N\) data, not a law derived from
any theorem here.

**Why this cannot be turned into the requested transition, even
granting the pattern.** Suppose, optimistically, that
\(\Delta_k(N)\le(\tfrac12+\varepsilon)\Delta_{k-1}(N)+R_k(N)\) could be
proved for some small remainder \(R_k\). Telescoping downward from
\(k=K-1\) to \(k=1\) gives \(\Delta_k(N)\lesssim2^{-(k)}\Delta_0(N)+
\sum R_j\)-type accumulation — i.e. **every scale's bound would still
be anchored to \(\Delta_0(N)\), the single finest scale**, exactly the
term [CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md)'s own "what this is
not" paragraph already identifies as "exactly as hard to bound... as
\(E_{\rm corr}(N)\) itself." A recursion running the other way (upward,
bounding \(\Delta_{k}\) in terms of \(\Delta_{k-1}\) starting from
\(k=1\)) has the same anchor at the bottom. Either direction, the base
case is the finest scale, and nothing above supplies a bound on
\(\Delta_0(N)\) beyond the global \(N^3e^{-c_\kappa\ell^\kappa}\),
\(\kappa<1/10\), already known without any scale decomposition. Proving
the ratio bound itself is no easier: \(\Delta_k\) and \(\Delta_{k-1}\)
differ only by which pairs of blocks are compared, both are
quartic-in-\(\Lambda\) quantities of the shift-block type Section 4
identified as unresolved, and there is no reduction here to something
weaker. **Grade: the ratio table is MEASURED (exact, for the five listed
\(N\)); the proposed recursion is neither proved nor reducible to a
weaker open statement — it is exactly as open as \(\Delta_0(N)\)
itself, which is exactly as open as \(E_{\rm corr}(N)\).**

## 6. Synthesis: the exact failure point and the resulting \(\theta\)

Reading the dyadic ladder from the coarse end (\(k=K-1\), closest to the
global mean \(\mu(N)\), where
[CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md)'s signed first-moment
estimate (equations (2), (15)-(16)) already gives good control) down
toward the fine end (\(k=0\), where
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md)'s tables put roughly half the
energy): **the transition fails immediately below the top
\(O(\ell^{3/5}(\log\ell)^{-1/5})\) rungs**, i.e. after descending only a
vanishing fraction of the \(K\sim\log_2N\) rungs available, by the exact
margin computed in Section 3 (equation (4) and the threshold
\(k^*=K-c\mathcal L(N)/\log2+O(1)\)). Below \(k^*\) the only tried
mechanism (a) is strictly worse than the trivial bound, and mechanism
(b) never leaves the status of an empirical pattern requiring a proof as
hard as \(\Delta_0(N)\) itself (Section 5). No mechanism reaches the
scales carrying the energy.

\[
 \boxed{\quad
 \text{The scale transition on }(\star)\text{ yields no }\theta.\quad
 \text{It neither reaches nor beats }\theta=1/10.
 \quad}
\]

The only bound available for \(E_{\rm corr}(N)=\mathrm{Energy}(N)\) at
the end of this attempt is the one already established without any
scale decomposition:
\(E_{\rm corr}(N)\ll_\kappa N^3\exp(-c_\kappa(\log N)^\kappa)\) for every
\(\kappa<1/10\) ([CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md)
equation (21)), and the separately proposed
\(\theta=1/10\) endpoint of [ENDPOINT_BOUND.md](ENDPOINT_BOUND.md),
neither of which this document reproves, weakens, or improves. The
exact identity \((\star)\) is unaffected; it remains true and
arithmetically inert, exactly as characterized in
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md).

## 7. What is and is not claimed

Section 3's Lemma and the bound (4) are proved, conditional on one
explicitly granted (not proved) main-term-matching assumption; the
conclusion that this route fails throughout its provable range holds
regardless of that assumption's truth, since granting it is the most
favorable case. Section 4's comparison to
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) is a reading of
that document, not a new non-existence proof for every conceivable
aggregate estimate. Section 5's ratio table is exact, finite-\(N\)
measurement; the impossibility argument built on it is a reduction to
an already-identified open quantity (\(\Delta_0(N)\)), not a proof that
no future argument can succeed. No claim is made that the scale
transition is impossible in principle — only that the two mechanisms
tried here, built directly from the tools inherited from
[CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md),
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) and
[ENDPOINT_BOUND.md](ENDPOINT_BOUND.md), both fail, and fail at the
specific scales named above. This does not touch, weaken, or improve
the RH-sufficiency bridge, the exceptional lower bound, or the proposed
\(\theta=1/10\) endpoint; none of those are reproved or re-derived here.
