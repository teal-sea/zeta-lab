# Section 8: one candidate multiscale energy for \(E_{\rm corr}\)

2026-09-10. Builds on [CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md),
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) and
[EXCEPTIONAL_ENERGY.md](EXCEPTIONAL_ENERGY.md) as they stand on this
branch. No specific base commit hash is cited: this pass does not use
git. Nothing in those three documents is revisited or changed.

**Outcome.** There is a multiscale arithmetic energy \(\mathrm{Energy}(N)\),
built from a dyadic (Haar/martingale) block-average telescoping of the
corrected residual vector, for which
\[
 E_{\rm corr}(N)=\mathrm{Energy}(N)\qquad\text{for every }N,               \tag{$\star$}
\]
an exact identity, proved below by elementary linear algebra (orthogonal
projections, no arithmetic input). Equality is the strongest possible
case of the requested domination \(E_{\rm corr}(N)\le\mathrm{Energy}(N)\).
It holds unconditionally, for every \(N\), with no fitted constant.

**What this is not.** \((\star)\) is a lossless repackaging of the same
number into dyadic-scale pieces, not a new estimate for its size. It
supplies zero information toward the open target
\(E_{\rm corr}(N)\ll_\epsilon N^{2+\epsilon}\)
([CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md) eq 1), or toward any
weaker unconditional power saving. Every scale component below is exactly
as hard to bound, in total, as \(E_{\rm corr}(N)\) itself; the multiscale
split only says which part of that difficulty is concentrated where. This
is a handwritten deduction, pending external verification, with no
novelty claim.

## 1. Setup, inherited without change

Use [CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md) Section 1 exactly:
\(\psi_2(N,h)=\sum_{n=1}^{N-h}\Lambda(n)\Lambda(n+h)\),
\(r_N(h)=\psi_2(N,h)-(N-h)\mathfrak S(h)\), the endpoint is exactly
\(N-h\) (not smoothed), \(\Lambda\) includes every proper prime power
(no primes-only replacement), and \(C_N(h)\) is the exact correction of
that document's equation (5), built from whatever exceptional data
\(q,\chi,\beta\) apply at \(N\) (\(C_N\equiv0\) if none exist). Put
\[
 x_h:=r_N(h)-C_N(h)\quad(1\le h\le N),\qquad
 E_{\rm corr}(N)=2\sum_{h=1}^N x_h^2.
\]
This document does not touch \(r_N\), \(C_N\), \(\mathfrak S\), or the
cutoff \(N-h\); it only takes the vector \((x_h)_{h=1}^N\) as given and
decomposes the one number \(\sum_h x_h^2\) by scale. Whatever \(q,\chi,\beta\)
turn out to be at a given \(N\) is absorbed into \(x_h\) before this
decomposition starts, so the construction is correct for every choice of
exceptional data, unchanged as it varies with \(N\).

## 2. The multiscale energy

**Why block length, not \(h\)-range.** Section 8 suggests dyadic bands
\(2^k\le h<2^{k+1}\) of the shift itself. Partitioning \(\{1,\dots,N\}\)
into such bands and summing \(2\sum_{h\in\text{band}}x_h^2\) per band is a
valid but degenerate special case: the bands are disjoint index sets, so
no cross term between bands ever arises, and "retaining" them is vacuous.
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) already uses a
different, non-degenerate dyadic scale for this kind of problem: window
*length* \(s=2^k\) of a moving sum, not a band of index values (its
Section 2, eq 1). This document uses that same scale variable — dyadic
block length, applied at \(\theta=0\), i.e. in the index domain rather
than the frequency domain — because it is the one that produces a
genuine, non-block-diagonal quadratic form with cross terms that must be
computed rather than assumed away.

**Construction.** Let \(K=\lceil\log_2N\rceil\), \(M=2^K\ge N\). Extend
\(x_h:=0\) for \(N<h\le M\) (this changes no sum of squares: it only adds
zero terms, and it does not touch \(x_h\) for \(h\le N\), so the sharp
endpoint at \(h=N\) is untouched). For \(k=0,\dots,K\) partition
\(\{1,\dots,M\}\) into \(2^{K-k}\) contiguous blocks of length \(2^k\),
and let \(P_k\) be the linear map that replaces \(x\) by its average on
each such block:
\[
 (P_kx)_h=2^{-k}\!\!\sum_{h'\in B_k(h)}\!\!x_{h'},\qquad
 B_k(h)=\text{the length-}2^k\text{ block containing }h.
\]
\(P_0=\mathrm{id}\), and \(P_K\) replaces \(x\) by its global mean
\(\mu(N):=M^{-1}\sum_{h=1}^Mx_h\) everywhere. Define
\[
 D_k:=P_k-P_{k+1}\quad(0\le k\le K-1),\qquad
 \Delta_k(N):=\|D_kx\|_2^2=\sum_{h=1}^M\bigl((P_kx)_h-(P_{k+1}x)_h\bigr)^2.
\]
Each \(\Delta_k(N)\) is manifestly a nonnegative quadratic form in
\((x_h)\): it is \(x^\top D_kx\) for the symmetric matrix \(D_k\) proved
below to be an orthogonal projection, hence positive semidefinite. Define
\[
 \boxed{\quad
 \mathrm{Energy}(N):=2M\mu(N)^2+2\sum_{k=0}^{K-1}\Delta_k(N).
 \quad}
\]
The first term is the retained **mean/central mode**: \(\mu(N)\) is
exactly \(M^{-1}\) times the value at frequency 0 of the discrete Fourier
transform of \((x_h)\), i.e. the constant Fourier coefficient of the
corrected residual sequence, padded to length \(M\). No smoothing is
applied to reach it: it is the ordinary arithmetic mean.

## 3. Domination, proved exactly

**Lemma (projection algebra).** For \(0\le a,b\le K\), \(P_aP_b=P_bP_a=P_{\max(a,b)}\).

*Proof.* Each \(P_k\) is symmetric (its matrix entry between \(h,h'\) is
\(2^{-k}\) if they lie in the same length-\(2^k\) block, else \(0\), a
symmetric relation) and idempotent (\(P_k^2=P_k\): averaging a
block-constant vector again changes nothing), hence an orthogonal
projection, onto \(V_k:=\{y:y\text{ constant on each length-}2^k\text{ block}\}\).
If \(a\le b\) then \(V_b\subseteq V_a\) (constant on the coarser blocks of
size \(2^b\) implies constant on the finer sub-blocks of size \(2^a\) that
compose them). For nested-range orthogonal projections, \(P_aP_b=P_bP_a=P_b\)
whenever \(V_b\subseteq V_a\): \(P_by\in V_b\subseteq V_a\), so
\(P_a(P_by)=P_by\) (\(P_a\) is the identity on \(V_a\)); and, block by
block, if \(z=P_ax\) is already constant on each length-\(2^a\) block with
values \(c_1,\dots\), then averaging \(z\) further over each length-\(2^b\)
block (a union of \(2^{b-a}\) such sub-blocks, each occurring once) gives
the same numbers as averaging \(x\) directly over that length-\(2^b\)
block, i.e. \(P_b(P_ax)=P_bx\). Together this gives the stated identity for
\(a\le b\) (so \(\max(a,b)=b\)); the case \(a\ge b\) is symmetric. \(\blacksquare\)

**Corollary.** \(D_k=P_k-P_{k+1}\) is symmetric, idempotent
(\(D_k^2=P_k-P_kP_{k+1}-P_{k+1}P_k+P_{k+1}=P_k-P_{k+1}-P_{k+1}+P_{k+1}=D_k\)
by the Lemma with \(a=k,b=k+1\)), hence itself an orthogonal projection.
For \(k\ne k'\), say \(k<k'\) so \(k+1\le k'\),
\[
 D_kD_{k'}=P_kP_{k'}-P_kP_{k'+1}-P_{k+1}P_{k'}+P_{k+1}P_{k'+1}
 =P_{k'}-P_{k'+1}-P_{k'}+P_{k'+1}=0
\]
by four applications of the Lemma. Likewise \(P_KD_k=P_K(P_k-P_{k+1})=P_K-P_K=0\)
for \(k\le K-1\), using \(\max(K,k)=\max(K,k+1)=K\).

**Theorem (exact identity).**
\[
 \sum_{h=1}^Mx_h^2=\|P_Kx\|_2^2+\sum_{k=0}^{K-1}\|D_kx\|_2^2
 =M\mu(N)^2+\sum_{k=0}^{K-1}\Delta_k(N).
\]

*Proof.* \(\sum_{k=0}^{K-1}D_k=\sum_{k=0}^{K-1}(P_k-P_{k+1})=P_0-P_K\)
telescopes exactly, so \(x=P_0x=P_Kx+\sum_{k=0}^{K-1}D_kx\). Expand
\(\|x\|_2^2\) by bilinearity: every cross term
\(2\langle P_Kx,D_kx\rangle\) and \(2\langle D_kx,D_{k'}x\rangle\)
(\(k\ne k'\)) that appears is **exactly zero**, by the Corollary applied
to \(\langle u,Pv\rangle=\langle Pu,v\rangle=\langle Pu,Pv\rangle\) for
any orthogonal projection \(P\) (so \(\langle P_Kx,D_kx\rangle
=\langle P_KD_kx,x\rangle=0\), and similarly for the other cross term).
What remains is the Pythagorean sum \(\|P_Kx\|_2^2+\sum_k\|D_kx\|_2^2\).
Since \(P_Kx\equiv\mu(N)\) on all \(M\) coordinates, \(\|P_Kx\|_2^2=M\mu(N)^2\).
\(\blacksquare\)

Multiplying by 2 and using \(\sum_{h=1}^Mx_h^2=\sum_{h=1}^Nx_h^2\) (the
padding only adds zero terms) gives \((\star)\):
\(E_{\rm corr}(N)=\mathrm{Energy}(N)\), for every \(N\), unconditionally.
**Grade: PROVED.** The proof uses only that \(P_k\) are symmetric
idempotent linear maps on \(\mathbb R^M\); it assumes nothing about the
arithmetic content of \(x_h\) (not the prime number theorem, not a sieve
bound, not GRH, not the existence or non-existence of an exceptional
zero). It is exact for every finite \(N\), not asymptotic and not fitted.

**On the mandatory retained cross terms.** The proof above does not
assume the cross terms \(\langle P_Kx,D_kx\rangle\) and
\(\langle D_kx,D_{k'}x\rangle\) are small and discard them; it computes
them and shows each is *identically* zero, from the projection algebra
alone. This is the sense in which the cross terms between scales are
retained: they are present in the natural expansion of \(\|x\|_2^2\) and
are accounted for by a proof of exact vanishing, not by an estimate or an
omission. Section 5 contrasts this with
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md), where the
analogous cross terms are between genuinely different objects and have
not been shown to vanish or to be small.

## 4. Per-scale table at \(N=10^4\) and \(N=10^5\)

Computed by `s8_candidate_energy.py`, which builds \(x_h=r_N(h)-C_N(h)\)
by reusing `probe.py`'s `von_mangoldt`, `singular_series` and `psi2_fft`
(see Section 6 for why \(C_N\equiv0\) in this run), then evaluates the
identity of Section 3 directly (no shortcut, no fit). `dominates` and the
relative gap in `results_s8_candidate_energy.json` confirm \((\star)\) to
floating-point precision (\(|{\rm Energy}-E_{\rm corr}|/E_{\rm corr}\lesssim10^{-15}\)
at every row) at all five computed \(N\) (2000, 5000, 10000, 30000,
100000); the two required by this section are shown below.

\(N=10^4\) (\(K=14\) scales, \(E_{\rm corr}=1.045773\times10^9\)):

| component | block length | value | share |
|---|---:|---:|---:|
| mean (\(2M\mu^2\)) | — | \(2.612\times10^6\) | 0.25% |
| scale 0 | 1 | \(5.259\times10^8\) | 50.29% |
| scale 1 | 2 | \(2.701\times10^8\) | 25.83% |
| scale 2 | 4 | \(1.297\times10^8\) | 12.41% |
| scale 3 | 8 | \(6.527\times10^7\) | 6.24% |
| scale 4 | 16 | \(2.587\times10^7\) | 2.47% |
| scale 5 | 32 | \(1.007\times10^7\) | 0.96% |
| scale 6 | 64 | \(4.662\times10^6\) | 0.45% |
| scale 7 | 128 | \(4.287\times10^6\) | 0.41% |
| scale 8 | 256 | \(2.279\times10^6\) | 0.22% |
| scale 9 | 512 | \(1.087\times10^6\) | 0.10% |
| scale 10 | 1024 | \(2.200\times10^6\) | 0.21% |
| scale 11 | 2048 | \(3.617\times10^5\) | 0.03% |
| scale 12 | 4096 | \(2.603\times10^5\) | 0.02% |
| scale 13 | 8192 | \(1.104\times10^6\) | 0.11% |

\(N=10^5\) (\(K=17\) scales, \(E_{\rm corr}=2.234400\times10^{11}\)):

| component | block length | value | share |
|---|---:|---:|---:|
| mean (\(2M\mu^2\)) | — | \(4.252\times10^8\) | 0.19% |
| scale 0 | 1 | \(1.117\times10^{11}\) | 49.97% |
| scale 1 | 2 | \(5.653\times10^{10}\) | 25.30% |
| scale 2 | 4 | \(2.720\times10^{10}\) | 12.17% |
| scale 3 | 8 | \(1.430\times10^{10}\) | 6.40% |
| scale 4 | 16 | \(6.722\times10^9\) | 3.01% |
| scale 5 | 32 | \(3.216\times10^9\) | 1.44% |
| scale 6 | 64 | \(1.454\times10^9\) | 0.65% |
| scale 7 | 128 | \(6.579\times10^8\) | 0.29% |
| scale 8 | 256 | \(3.262\times10^8\) | 0.15% |
| scale 9 | 512 | \(1.889\times10^8\) | 0.08% |
| scale 10 | 1024 | \(1.510\times10^8\) | 0.07% |
| scale 11 | 2048 | \(1.518\times10^8\) | 0.07% |
| scale 12 | 4096 | \(1.903\times10^8\) | 0.09% |
| scale 13 | 8192 | \(8.091\times10^7\) | 0.04% |
| scale 14 | 16384 | \(5.511\times10^7\) | 0.02% |
| scale 15 | 32768 | \(8.624\times10^7\) | 0.04% |
| scale 16 | 65536 | \(5.133\times10^7\) | 0.02% |

**Grade: MEASURED (exact, for these five \(N\); not a theorem about the
scale profile in general).** The two tables show the same qualitative
shape: about half of \(E_{\rm corr}(N)\) sits in the finest scale (block
length 1, i.e. \(D_0x=x-P_1x\), adjacent-pair differences), and each
successive octave holds roughly half of what the previous one held, down
to a long, noisy tail of coarse scales each worth well under 1%, plus a
mean term at the ~0.2% level. This is the profile of a sequence whose
autocovariance decays quickly with lag — consistent with, but not a
proof of, an unconditional square-root-cancellation-type input for
\(x_h\); no such input is assumed or used in \((\star)\), and this
paragraph asserts nothing beyond what the two tables show at these five
\(N\).

## 5. Relation to LOCALIZED_MIXED_ENERGY.md

[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) also uses a dyadic
window-length scale, but on a different, Fourier-side object: its
\(T_s(\theta)\) (its eq 1) is an integral over frequency \(\theta\) of a
length-\(s\) window energy of \(W=F-H\), and its final budget (its eq 25)
bounds \(\sqrt{E_{\rm corr}}\) — not \(E_{\rm corr}\) itself — by
\(2\sqrt{\mathcal M}+\sqrt{\int|W|^4-D_w^2}+O(N^{3/2}e^{-c\ell^{1/10}})+O(N)\),
where \(\mathcal M=\int|H|^2|W|^2\) is bounded, in turn, by exactly such a
dyadic-\(s\) decomposition (its eqs 12-14, 19) of the *mixed energy*, a
quantity auxiliary to \(E_{\rm corr}\), not equal to it.

Three differences follow:

1. **Identity vs. majorant.** \((\star)\) here is an equality for
   \(E_{\rm corr}(N)\) itself. LOCALIZED_MIXED_ENERGY's eq 25 is a
   triangle-inequality upper bound on \(\sqrt{E_{\rm corr}}\) via a
   different quantity (\(\|G_{\rm corr}\|_2\)) that is only within
   \(O(N)\) of \(\sqrt{E_{\rm corr}}\) (its eq 24), and whose components
   \(X,Y,R_{\rm mod}\) are not orthogonal.
2. **The cross terms.** LOCALIZED_MIXED_ENERGY's eq 22 keeps
   \(2\,{\rm Re}\langle X,Y\rangle\) and \(2\,{\rm Re}\langle X+Y,R_{\rm mod}\rangle\)
   explicitly and states "No sign or cancellation estimate ... has been
   proved here"; its Section 6 identifies this, together with the
   unresolved long-window estimate (its eq 20), as exactly why its
   attempt does not close. This document's cross terms
   (\(\langle P_Kx,D_kx\rangle\), \(\langle D_kx,D_{k'}x\rangle\)) are
   *provably* zero (Section 3), because \(P_K\), \(D_k\) are orthogonal
   projections of the *same* vector \(x\) — an algebraic fact, not an
   arithmetic one. The price of this is that \((\star)\) carries no
   arithmetic content at all: unlike LOCALIZED_MIXED_ENERGY's eqs
   12-14 and 19, which do extract genuine (if insufficient) power
   savings from the prime number theorem and sieve estimates, \((\star)\)
   uses no fact about \(\Lambda\), \(\mathfrak S\), or \(C_N\) beyond
   their being some fixed real numbers.
3. **Scale variable.** Both use dyadic length scales, but
   LOCALIZED_MIXED_ENERGY's \(s\) is the length of a Fourier-side window
   integrated over all \(\theta\) and partitioned again by rational
   denominator; this document's \(2^k\) is a block length applied once,
   directly to the index-domain vector \(x_h\), with no frequency
   integral or denominator partition. They are not the same
   decomposition of the same object, and \((\star)\)'s scale profile
   (Section 4) is not a restatement of LOCALIZED_MIXED_ENERGY's eq 26
   budget in different notation.

**Grade of this section: the equality \((\star)\) is PROVED; the
comparison of proof strategies is a reading of both documents, not a new
estimate.** \((\star)\) does not shorten, weaken, or bypass the specific
gap LOCALIZED_MIXED_ENERGY.md identifies (its eq 20, and the cross terms
of its eq 22); that gap is about \(\mathcal M\), a quantity \((\star)\)
never introduces.

## 6. Relation to EXCEPTIONAL_ENERGY.md

[EXCEPTIONAL_ENERGY.md](EXCEPTIONAL_ENERGY.md) studies
\(\mathcal A_{\rm exc}(N):=2\sum_{h=1}^N|C_N(h)|^2\) (its eq 17→2, called
\(\mathcal A_{\rm exc}\) there for a specific exceptional \(q,\beta\)) and
proves a closed-form *lower* bound for it (its eq 2) by restricting to an
explicit shift set \(\mathcal H=\{h:N/4\le h\le N/2,\,2\mid h\}\) where the
two linear correction terms vanish (its Section 3). That is a bound on a
sub-sum over an explicit range of \(h\), not a decomposition by scale, and
it is a one-sided estimate, not an identity.

The construction of Section 2 above is generic in the input vector: it
applies verbatim with \(x_h:=C_N(h)\) in place of \(x_h:=r_N(h)-C_N(h)\),
giving the same exact identity \(\mathcal A_{\rm exc}(N)=\mathrm{Energy}_C(N)\)
for the correction energy alone, with its own mean term and its own
\(K\) scale details built from \(C_N\). That identity is not evaluated
numerically here (Section 7 explains why: no exceptional zero is assumed
to exist, so \(C_N\equiv0\) and \(\mathcal A_{\rm exc}=0\) identically in
every run below). Qualitatively, EXCEPTIONAL_ENERGY's shift set
\(\mathcal H\) sits inside the middle third of \([1,N]\); in a dyadic
block-average decomposition of \(C_N\), that band overlaps every scale
from \(k=0\) up to \(k\approx K-2\) (a set of that width is not
block-constant at any one scale), so its contribution is spread across
\(\mathrm{Energy}_C\)'s scale components rather than isolated in one. This
is a positional remark, not a proven correspondence between
EXCEPTIONAL_ENERGY's lower bound (eq 2) and any specific \(\Delta_k\) of
\(\mathrm{Energy}_C\).

**Grade: the generic applicability of Section 2's construction to
\(C_N\) alone is PROVED (it is the same theorem with a different input
vector); the qualitative remark about \(\mathcal H\) is an OBSERVATION,
not a derived bound.** Nothing here strengthens, weakens, or numerically
checks EXCEPTIONAL_ENERGY.md's eq 2 or eq 3.

## 7. Why the numerics use \(E_{\rm corr}=E\)

At every \(N\) evaluated (2000, 5000, 10000, 30000, 100000), this attempt
does not assume, construct, or borrow a concrete odd/4-part/8-part
exceptional conductor \(q<Z\) with an associated real zero \(\beta\); none
is known to exist unconditionally. By
[CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md) Section 1, "If no such
zero exists, set \(C_N(h)=0\) for every \(h\)", which is the only
correction value available here without inventing exceptional data that
would not itself be a proof of anything. With \(C_N\equiv0\),
\(x_h=r_N(h)\) exactly, and
\[
 E_{\rm corr}(N)=2\sum_{h=1}^Nr_N(h)^2=E(N),
\]
the original CHHL quantity of `probe.py`. `s8_candidate_energy.py`
therefore builds \(x_h\) via `probe.py`'s `von_mangoldt`,
`singular_series`, and `psi2_fft`, and cross-checks its own
\(E_{\rm corr}\) against `probe.py`'s `E_of_N` at every row
(`check_matches_probe_E_of_N_relerr` in the JSON output, at floating-point
precision throughout). **Grade: this reduction is exact and forced by the
definitions, not a simplifying choice**; it is the reason "computing
\(E_{\rm corr}\) directly by reusing probe.py's routes" is possible at
all without a separate implementation of \(C_N(h)\).

## 8. Section 8's constraints, checked one by one

- **Retains the mean/central mode.** The \(2M\mu(N)^2\) term is exactly
  this; see Section 2.
- **Retains the cross terms between scales.** Computed and shown to be
  exactly zero, not assumed or dropped; see Section 3's closing remark.
- **The changing correction data (\(q,\chi,\beta\) may vary with \(N\)).**
  \(\mathrm{Energy}(N)\) is built from \(x_h=r_N(h)-C_N(h)\) as given at
  each \(N\), for whatever exceptional data apply there (Section 1); the
  proof of \((\star)\) uses no property of \(C_N\) beyond it being some
  fixed real sequence, so nothing breaks if \(q,\chi,\beta\) change from
  one \(N\) to the next.
- **Sharp endpoint \(N-h\); no smoothing of the endpoint.** Inherited
  unchanged from \(r_N(h)=\psi_2(N,h)-(N-h)\mathfrak S(h)\) (Section 1);
  the padding used to reach a power of 2 only appends zero coordinates
  strictly beyond \(h=N\) and never modifies \(x_h\) for \(h\le N\).
- **No primes-only replacement.** \(\Lambda\) includes proper prime
  powers throughout, exactly as in `probe.py`'s `von_mangoldt` and in
  CORRECTED_RH_BRIDGE.md; no restriction to `lam_p`/`theta_2`-type
  primes-only sequences is used anywhere in this document or script.

All five hold. **The candidate satisfies Section 8's constraints and
proves exact domination unconditionally; the open item this document does
not touch is the actual size of \(E_{\rm corr}(N)\), which the identity
leaves exactly as large as it was.**
