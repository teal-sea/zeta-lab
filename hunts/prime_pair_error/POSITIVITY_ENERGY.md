# Section 8: a positivity-based multiscale energy for \(E_{\rm corr}\), checked against the Davenport-Heilbronn battery

2026-09-10. Builds on [CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md),
[SIEGEL_UNIFORMITY.md](SIEGEL_UNIFORMITY.md) and
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) as they stand on this
branch, and directly answers the question
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md)/[CHALLENGE.md](CHALLENGE.md) left
open: a multiscale \(\mathrm{Energy}(N)\ge E_{\rm corr}(N)\) whose per-scale
proofs use the arithmetic content of \(\Lambda\), \(\mathfrak S\), \(C_N\),
not just linear algebra on an arbitrary real vector. Nothing in the three
inherited documents is revisited or reproved; this document's job is to
**assemble** their already-proved per-scale estimates into the exact box
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md) Section 2 was asked for, **name**
the one arithmetic fact each scale consumes, and **run the Davenport-Heilbronn
battery against that fact directly**, per [CHALLENGE.md](CHALLENGE.md)'s own
standing rule.

**Outcome.** \(\mathrm{Energy}(N)\), defined below from
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md)'s own eq. (25)-(26),
dominates \(E_{\rm corr}(N)\) (Section 2) and splits into a retained
mean/central mode plus dyadic scales with retained cross terms (Section 3),
exactly as [CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md) Section 8 requires.
Unlike that candidate, every scale's *proof*, not just its numeric value,
requires an arithmetic hypothesis about \(\Lambda\) (Section 4): the
mean/central mode needs \(\Lambda(n)\ge0\) (Euler-product positivity, the
input to the classical zero-free region), and every other scale needs
\(\Lambda\)'s multiplicativity (Vaughan/Siegel-Walfisz). Section 5 runs
`zeta/epstein.py`'s Davenport-Heilbronn interface against exactly that
positivity hypothesis, reusing the module's own `claim_euler_product_positivity`
and `claim_multiplicativity` unmodified, and both **fail** for the DH sequence
-- reverified independently here (own \(O(n_{\max}\log n_{\max})\)
divisor-sieve recursion, agreeing with `zeta.epstein`'s own reference
implementation to \(1.5\times10^{-16}\) relative error at \(n_{\max}=200\)),
not merely re-quoted from the module's docstring. Section 5 then derives,
from the pinned off-line zero \(\rho\), the standard (cited, not re-derived)
consequence that the mean-mode step's conclusion is not just unproved but
**false** for the DH analogue, and supports it with a robust numerical fact
(Section 5.3) that does not depend on that harder asymptotic statement.
This candidate does not survive the battery, which is the intended outcome:
it is the first energy in this hunt whose domination proof has an
identifiable step that a real, functional-equation-respecting, off-line-zero
rival cannot supply. Section 6 states plainly what this does and does not
change about the total order of \(E_{\rm corr}(N)\): **nothing**. No fixed
power saving is claimed anywhere in this document.

This is a handwritten deduction, pending external verification, with no
novelty claim: essentially all of the size estimates below are reused, by
citation, from the three inherited documents; what is new is the packaging,
the per-scale attribution, and the battery run.

## 1. Setup, inherited without change

Exactly [CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md) Section 1 and
[SIEGEL_UNIFORMITY.md](SIEGEL_UNIFORMITY.md) eq. (5):
\(\psi_2(N,h)=\sum_{n=1}^{N-h}\Lambda(n)\Lambda(n+h)\),
\(r_N(h)=\psi_2(N,h)-(N-h)\mathfrak S(h)\), \(x_h:=r_N(h)-C_N(h)\),
\(E_{\rm corr}(N)=2\sum_{h=1}^Nx_h^2\), endpoint exactly \(N-h\), \(\Lambda\)
including every proper prime power, \(C_N\equiv0\) when no exceptional zero
exists at that \(N\). This document does not touch any of these definitions.

Also inherited, unchanged, from [LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md)
Section 1: \(\ell=\log N\), \(Z=\exp(\ell^{1/10})\), \(P=\prod_{p<Z}p\),
\(b_Z=P/\phi(P)\), \(\nu(n)=b_Z1_{(n,P)=1}\),
\(a(n)=\nu(n)(1-1_{\rm exc}\chi(n)n^{\beta-1})\), \(w_n=\Lambda(n)-a(n)\),
\(F=\sum\Lambda(n)e(n\alpha)\), \(H=\sum a(n)e(n\alpha)\), \(W=F-H\),
\(D_w=\sum|w_n|^2\), and the centered polynomials
\(X=\mathcal C(2\operatorname{Re}(\overline HW))\), \(Y=\mathcal C(|W|^2)\),
\(R_{\rm mod}=\mathcal C(|H|^2-V_y)-\widehat C_N\), with
\(G_{\rm corr}=X+Y+R_{\rm mod}\) and
\(|\sqrt{E_{\rm corr}}-\|G_{\rm corr}\|_2|\ll N\) (that document's eq. 24).

## 2. \(\mathrm{Energy}(N)\), assembled from already-proved pieces

[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) eq. (25) already proves,
unconditionally,
\[
 \sqrt{E_{\rm corr}(N)}\le
 2\sqrt{\mathcal M}+\sqrt{\textstyle\int|W|^4-D_w^2}
 +CN^{3/2}e^{-c\ell^{1/10}}+C'N,
                                                               \tag{1}
\]
where \(\mathcal M=\int|H|^2|W|^2\) (its eq. 9). Define
\[
 \boxed{\quad
 \mathrm{Energy}(N):=
 \Bigl(2\sqrt{\mathcal M}+\sqrt{\textstyle\int|W|^4-D_w^2}
   +CN^{3/2}e^{-c\ell^{1/10}}+C'N\Bigr)^2.
 \quad}
                                                               \tag{2}
\]
Squaring (1) gives \(E_{\rm corr}(N)\le\mathrm{Energy}(N)\) directly: this is
not an identity, and Section 4 shows exactly why it cannot degenerate into one
the way [CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md)'s did.

The same document's eq. (26) already decomposes \(\mathcal M\) into named,
disjoint-by-construction pieces:
\[
 \mathcal M\ll_\kappa
 \underbrace{N^{14/5+o(1)}}_{\Delta_{\rm denom}}
 +\underbrace{N^{11/5+o(1)}}_{\Delta_{\rm short}}
 +\underbrace{N^3e^{-c\mathcal L(N)}}_{\Delta_{\rm mean}}
 +\underbrace{N^3e^{-c_\kappa\ell^\kappa}+N^3e^{-c\ell^{9/10}}}_{\Delta_{\rm fallback}},
                                                               \tag{3}
\]
\(\mathcal L(N)=\ell^{3/5}(\log\ell)^{-1/5}\) (its eq. (19)'s exponent,
Vinogradov-Korobov, stronger than plain de la Vallée-Poussin
\(\ell^{1/2}\)). Explicitly:

- \(\Delta_{\rm denom}\): the dyadic-denominator sum
  \(\mathcal A_{\ge R}\) (eq. 12), summed over reduced fractions with
  denominator in dyadic blocks \([D,2D)\) via the rational-sampling lemma
  (eq. 10-11).
- \(\Delta_{\rm short}\): the short-window sum \(\mathcal A_{s\le L_0}\)
  (eq. 14), summed over dyadic window lengths \(s=2^k\le N^{3/5}\).
- \(\Delta_{\rm mean}\): the **mean/central mode**, the single \(s=N\),
  \(r=1\), \(\theta=0\) window \(T_N(0)\) (eq. 15), evaluated exactly via
  \(A(k)=\sum_{n\le k}(\Lambda(n)-a(n))\) and bounded (eq. 19) by the
  classical prime number theorem.
- \(\Delta_{\rm fallback}\): every remaining window, bounded by the
  inherited uniform Fourier estimate (end of Section 5 there).

This is a genuine multiscale telescoping in the sense
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) Section 4 states: the
windows are partitioned first by length \(s\le L_0\), then by denominator
\(r\ge R\), "to avoid double counting." \(\mathrm{Energy}(N)\) as boxed in
(2) is the Section-8-requested shape with the mean/central mode
(\(\Delta_{\rm mean}\)) retained as its own named term, matching
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md) Section 2's box exactly in role,
not in method.

## 3. Why this does not collapse to an identity, and where the cross terms are

[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md)'s construction decomposed the
residual vector \((x_h)\) itself by an orthogonal projection of
\(\mathbb R^M\); that is why it was exact for *every* real vector and carried
no arithmetic content ([CHALLENGE.md](CHALLENGE.md) attack 3). \((2)\) does
not do this. It bounds \(E_{\rm corr}\) through a *different*, auxiliary
object -- \(F,H,W\), functions of the frequency \(\alpha\), related to
\((x_h)\) only through the specific, arithmetic identity that
\(\psi_2(N,h)\) is an autocorrelation of \(\Lambda\) (Parseval/Plancherel for
the product \(|F|^2\), CORRECTED_RH_BRIDGE.md Section 1 and
SIEGEL_UNIFORMITY.md Section 1). Decomposing \(\mathcal M\) or \(\int|W|^4\)
by dyadic scale of \(s\) or \(r\) is therefore not a rearrangement of the
entries of \((x_h)\) by any orthogonal map; each piece's *size* genuinely
depends on what \(\Lambda\) and \(a\) are, which is exactly why proving (3)'s
individual bounds took the sieve calculation, the rational-sampling lemma,
and the classical prime number theorem, rather than four lines of projection
algebra. Section 5 makes this concrete by exhibiting a sequence for which one
piece's *proof* has no analogue at all.

**Retained cross terms.** \(\mathrm{Energy}(N)\) is derived from the full
expansion [LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) eq. (22),
\[
 \|G_{\rm corr}\|_2^2=\|X\|_2^2+\|Y\|_2^2+\|R_{\rm mod}\|_2^2
 +2\operatorname{Re}\langle X,Y\rangle
 +2\operatorname{Re}\langle X+Y,R_{\rm mod}\rangle,
                                                               \tag{4}
\]
by triangle inequality, **not** by an assertion that the cross terms vanish
or are small; that document states plainly "No sign or cancellation estimate
for the last two terms has been proved here," and this document changes
nothing about that. This is the honest sense in which cross terms between
scales are retained here: present in (4), paid for (not deleted) by the
factor structure of (1)-(2), and explicitly flagged as unresolved rather than
assumed away -- the opposite failure mode from
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md), whose cross terms were retained
by being *proved* exactly zero. Both are legitimate ways to satisfy the
constraint; only one of them turned out to carry arithmetic content.

## 4. The one arithmetic fact each scale consumes

- **\(\Delta_{\rm denom}\), \(\Delta_{\rm short}\):** the rational-sampling
  lemma (eq. 10) plus the sieve calculation (SIEGEL_UNIFORMITY.md eq. 9-11,
  reused there via LOCALIZED_MIXED_ENERGY.md eq. 6-7), which needs
  \(\Lambda\) (via \(\nu,a\)) to be
  supported on an explicit sieve of primes below \(Z\), and Ramanujan-sum
  orthogonality \(\sum_{h\bmod q}c_q(h)^2=q\phi(q)\) -- both consequences of
  the multiplicative structure of the residues mod \(q\), not of size alone.
- **\(\Delta_{\rm fallback}\):** the uniform linear-phase bound
  \(\sup_\alpha|W(\alpha)|\ll_\kappa Ne^{-c_\kappa\ell^\kappa}\)
  (Tao-Teräväinen Theorem 2.7 via Gowers-uniformity control of \(\Lambda\)),
  itself built from Vaughan's identity, a divisor-convolution decomposition
  of \(\Lambda\) that exists **because** \(-\zeta'/\zeta(s)=\sum\Lambda(n)n^{-s}\)
  is the log-derivative of an Euler product.
- **\(\Delta_{\rm mean}\):** the classical prime number theorem,
  \(\Delta(t):=\psi(t)-t=O(t\exp(-c\mathcal L(t)))\)
  (LOCALIZED_MIXED_ENERGY.md eq. 15-19, citing TT Theorem 1.3(i)), whose
  *proof* -- de la Vallée-Poussin's zero-free region, and its
  Vinogradov-Korobov strengthening -- uses exactly one arithmetic fact about
  \(\Lambda\): **\(\Lambda(n)\ge0\)**. This is the classical "3-4-1"
  inequality
  \(-3\operatorname{Re}(\zeta'/\zeta(\sigma))-4\operatorname{Re}(\zeta'/\zeta(\sigma+it))
  -\operatorname{Re}(\zeta'/\zeta(\sigma+2it))\ge0\), which reduces to
  \(-\sum_n\Lambda(n)n^{-\sigma}\cdot2(1+\cos(t\log n))^2\le0\) using nothing
  about \(\Lambda\) beyond \(\Lambda(n)\ge0\) (log of a prime power is
  \(\ge0\)) and that \(\Lambda\) is the *same* sequence read off
  \(-\zeta'/\zeta\) at \(\sigma\), \(\sigma+it\), \(\sigma+2it\) -- i.e. that
  \(\zeta\) has an Euler product at all. This is exactly the property
  `zeta/epstein.py`'s `claim_euler_product_positivity` names and tests: "the
  input to the classical zero-free region," in that module's own words.

No other estimate in (3) is used to prove \(\Delta_{\rm mean}\); no positivity
or multiplicativity assumption is used to prove \(\Delta_{\rm denom}\),
\(\Delta_{\rm short}\), or \(\Delta_{\rm fallback}\) beyond the ones just
named. This is the line the cross-session review asked to be pointed at
before writing anything down.

## 5. The Davenport-Heilbronn battery

### 5.1 Running the module's own claims against the mean-mode hypothesis

`hunts/prime_pair_error/s8_positivity_battery.py` reuses
`zeta.epstein.battery`, `claim_multiplicativity`, `claim_euler_product_positivity`,
and `dh_interface` **unmodified** (never reimplemented; these are exactly the
repository's own falsification harness for gate #3, built for exactly this
kind of check), and writes `results_s8_positivity_battery.json`.

```
claim_multiplicativity:            riemann_zeta = True,  davenport_heilbronn = False
claim_euler_product_positivity:    riemann_zeta = True,  davenport_heilbronn = False
```

Both fail for the Davenport-Heilbronn interface, reconfirming what
`zeta/epstein.py`'s own docstrings already record: DH has real coefficients,
a genuine Riemann-type functional equation \(F(s)=F(1-s)\), a real Hardy
function, and a zero at \(\rho\approx0.808517+85.699348i\) off the critical
line -- but no Euler product, and its log-derivative coefficients
\(\Lambda_F(n)\) (`zeta.epstein.log_derivative_coefficients`, defined by
\(a(n)\log n=\sum_{d\mid n}a(d)\Lambda_F(n/d)\), \(a_1=1\), the *only* route
from a rival's Dirichlet coefficients to the quantity a positivity-based
mechanism actually reads) are not \(\ge0\).

This script reverifies the failure independently rather than re-quoting the
module's docstring number, using its own \(O(n_{\max}\log n_{\max})\)
divisor-sieve solution of the identical recursion (the module's own
implementations are \(O(n_{\max}^2)\), fine at their stated \(n_{\max}=200\)
but not at the \(n_{\max}=2\times10^5\) this document needs for Section 5.3).
Cross-check at \(n_{\max}=200\) against `zeta.epstein.log_derivative_coefficients`
(mpmath, mirroring the module's own doubly-implemented convention in
`zeta/factorization.py` and `zeta/quasicrystal.py`): maximum absolute
difference \(8.9\times10^{-16}\). Independently computed
\(\Lambda_F(3)=-0.31209\ldots\), sign-confirming the module's claim (its
docstring quotes \(-6.78\) for the same coefficient, a discrepancy this
document does not resolve and does not need to -- both values are negative,
and the sign, not the magnitude, is what
`claim_euler_product_positivity` reads). \(\kappa\), the Davenport-Heilbronn
constant, was re-derived here via `zeta.epstein.kappa`, never hardcoded, per
that module's own stated convention.

**Consequence for \(\Delta_{\rm mean}\).** The one hypothesis its proof
needs, \(\Lambda(n)\ge0\), is false for \(\Lambda_F\). The classical
zero-free-region argument cannot be run on the Davenport-Heilbronn sequence
at all: the "3-4-1" inequality of Section 4 needs the sign
\(-\sum_n\Lambda_F(n)n^{-\sigma}\cdot(\cdots)\le0\), and this fails as soon as
any \(\Lambda_F(n)<0\), which happens already at \(n=3\). This is a stronger
failure mode than a numeric near-miss: the construction's *proof* does not
go through, exactly the sense [CHALLENGE.md](CHALLENGE.md) attack 3 asked
for, run here in the positive direction (naming the one step that uses the
structure of the primes, rather than confirming that none does).

### 5.2 What the missing positivity actually costs: a cited consequence

\(F\) is entire (no pole at \(s=1\): its coefficients' period average is
\(1+\kappa-\kappa-1+0=0\)). Its log-derivative \(G(s)=-F'/F(s)\) therefore has
no "trivial" pole at \(s=1\) supplying a growing main term the way
\(-\zeta'/\zeta\) does for \(\Lambda\); but at the located simple zero
\(s=\rho\) of \(F\), \(G(s)=-F'/F(s)\) **does** have a simple pole, with
residue \(-1\) (elementary: \(F(s)=(s-\rho)h(s)\), \(h(\rho)\ne0\), gives
\(F'/F(s)=1/(s-\rho)+h'/h(s)\)). By the same Mellin/Perron-holomorphy
mechanism [CORRECTED_RH_BRIDGE.md](CORRECTED_RH_BRIDGE.md) Section 5 eq. (20)
already uses in the forward direction here (small partial sums make an
integral holomorphic past a candidate zero, contradiction) -- run instead
in the converse direction against a pole whose location is already pinned,
which is the standard content of Landau's oscillation theorem for Dirichlet
series with a genuine singularity, cited rather than re-derived here, exactly
as the sibling `SCALE_TRANSITION.md` line of work names it as this hunt's
known barrier mechanism -- any partial-sum bound
\(\sum_{n\le t}\Lambda_F(n)=O(t^\theta)\) for \(\theta<\operatorname{Re}(\rho)=0.808517\ldots\)
is impossible. **This is the sense in which "the same construction applied to
Davenport-Heilbronn does not give a matching bound": it gives a claim that is
false**, not merely an untested or unprovable one, because the classical
zero-free-region mechanism would need to exclude a zero at \(\operatorname{Re}=0.8085\)
to reach even the weak bound \(O(t^{1/2+\epsilon})\), and \(\rho\) is a
verified counterexample to exactly that exclusion (already located, pinned to
50 digits, and cross-checked against Spira 1994 in `zeta/epstein.py`).

This paragraph cites standard theory in the same way the inherited documents
cite Tao-Teräväinen or Montgomery-Vaughan; it is not re-derived here, and the
convergence/growth properties of \(\Lambda_F\)'s own Dirichlet series in a
given half-plane are not established in this document beyond what Section
5.3 checks directly.

### 5.3 A robust numerical fact that does not depend on the asymptotic statement

Landau-type Omega statements are limsup statements and are not expected to be
visible at any numerically reachable \(N\) (the same caution applies to the
classical PNT decay `LOCALIZED_MIXED_ENERGY.md` cites for the real
mean-mode: at \(N=2\times10^5\), \(\exp(-\sqrt{\log N})\approx0.030\), nowhere
near its asymptotic regime either). The partial-sum growth-rate fit in
`results_s8_positivity_battery.json` (`fitted_growth_exponent_top_half`,
`top_quarter`) is accordingly noisy and inconclusive at \(n_{\max}=2\times10^5\)
-- reported for completeness, not claimed as evidence.

A different, non-asymptotic-sensitive fact is robust at this range and is
the one actually load-bearing here. For the primes,
\(\Lambda(n)\le\log n\) always (used pervasively in the inherited documents,
e.g. SIEGEL_UNIFORMITY.md/LOCALIZED_MIXED_ENERGY.md's \(|a(n)|\le2b_Z\),
\(\Lambda(n)\le\ell\) bounds). Is \(\Lambda_F(n)=O(\log n)\) for
Davenport-Heilbronn? Measured (own divisor-sieve computation, cross-checked
as above), maximum \(|\Lambda_F(n)|\) in dyadic-ish windows against
\(\log(\text{window right edge})\):

| window | \(\max|\Lambda_F(n)|\) | \(\log(\text{right edge})\) | ratio |
|---|---:|---:|---:|
| \([2,2000)\) | 26.73 | 7.60 | 3.52 |
| \([2000,20000)\) | 157.80 | 9.90 | 15.93 |
| \([20000,200000)\) | 630.97 | 12.21 | 51.69 |

The ratio is not merely nonzero; it grows by roughly a factor of \(4.4\) each
time the window's right edge grows by a factor of \(10\), i.e. \(|\Lambda_F|\)
is growing polynomially in \(n\) here (consistent with, though this document
does not fit, an exponent well above \(0\); \(\sqrt n\) at \(n=2\times10^5\)
is \(447\), the same order as the measured \(631\)), while \(\log n\) grows
by less than \(1\). This is the elementary bound every minor-arc and
sieve estimate in \(\Delta_{\rm denom}\), \(\Delta_{\rm short}\),
\(\Delta_{\rm fallback}\) also uses for \(\Lambda\) itself, so it is a second,
independent place (beyond the sign failure of Section 5.1) where the
Davenport-Heilbronn analogue of the primes' arithmetic input is measurably,
robustly false, already within reach of direct computation, without needing
the harder Omega-theorem statement of Section 5.2 at all.

## 6. What this changes, and what it does not: the a-0070 relay

A parallel attempt on the same corrected error (`a-0070`, relayed via a peer
session) reports that any bounded-divisor-level model comparison of the
\(\nu(n)\), \(Z=\exp(\ell^{1/10})\) shape used throughout
[SIEGEL_UNIFORMITY.md](SIEGEL_UNIFORMITY.md)/[ENDPOINT_BOUND.md](ENDPOINT_BOUND.md)'s
architecture is structurally capped: the \(N^3\) budget forces a divisor
level \(D_0=Z^s\) with \(s=o(\ell^{1-\kappa})\), while reaching a rate
\(\ell^\kappa\) needs \(s\) to decay at least that fast, and the two cannot
both hold past \(\kappa=1/2\).

\(\Delta_{\rm denom}\), \(\Delta_{\rm short}\), and \(\Delta_{\rm fallback}\)
are reused directly from that architecture (Section 4), so they inherit
exactly that ceiling; nothing here removes it. \(\Delta_{\rm mean}\) does
**not** go through any \(Z\)-level sieve truncation at all -- its bound
(LOCALIZED_MIXED_ENERGY.md eq. 19) is the classical, level-free
de la Vallée-Poussin/Vinogradov-Korobov estimate for \(\psi(t)-t\) directly,
with no divisor level \(D_0\) and no arithmetic-progression modulus \(q\) in
its statement at all. It has no analogous tension between a truncation level
and the \(N^3\) budget, and in fact already reaches a *stronger* rate,
\(\mathcal L(N)=\ell^{3/5}(\log\ell)^{-1/5}\) (Vinogradov-Korobov), than the
\(\ell^{1/10}\) the rest of the architecture is capped at.

This is not, however, an improvement to \(E_{\rm corr}(N)\)'s total order.
\(\mathcal M\)'s size in (3) is governed by whichever term is largest, and
\(N^3e^{-c\mathcal L(N)}\) (the mean mode) is *smaller* than
\(N^3e^{-c_\kappa\ell^\kappa}\) (the fallback pieces, \(\kappa<1/10\)) for
large \(N\), since \(\ell^{3/5}(\log\ell)^{-1/5}\gg\ell^{1/10}\). The
bottleneck was never the mean mode; it is exactly where
[LOCALIZED_MIXED_ENERGY.md](LOCALIZED_MIXED_ENERGY.md) already located it
(its eq. 20, the long-window *mean square*, a strictly stronger and
unestablished statement, and the unresolved cross-term cancellation of its
eq. 22). \(\mathrm{Energy}(N)\) therefore has the same order as before this
document: \(E_{\rm corr}(N)\ll_\kappa N^3\exp(-c'_\kappa\ell^\kappa)\) for
every fixed \(\kappa<1/10\), no fixed power saving. Section 8's request for
"a genuinely arithmetic multiscale upper bound" did not require beating that
order, only that the bound's proof be arithmetic rather than vacuous and that
it fail the battery a merely-algebraic construction would pass; this document
supplies that, not a smaller \(\mathrm{Energy}(N)\).

## 7. Section 8's constraints, checked one by one

- **Retains the mean/central mode.** \(\Delta_{\rm mean}\) (Section 2) is
  exactly this, and Section 4 identifies its own arithmetic content
  separately from every other scale.
- **Retains the cross terms between scales.** Present in (4) and paid for by
  triangle inequality through to (1)-(2), not assumed zero or dropped
  (Section 3).
- **The changing correction data.** \(a(n)\), \(R_{\rm mod}\), and
  \(\widehat C_N\) are built from whatever \(q,\chi,\beta\) apply at each
  \(N\) (Section 1, inherited); no step here uses a fixed exceptional
  conductor.
- **Sharp endpoint \(N-h\); no smoothing.** Inherited unchanged through
  \(r_N(h)\), \(\psi_2(N,h)\), and the un-smoothed window identity
  (LOCALIZED_MIXED_ENERGY.md eq. 1).
- **No primes-only replacement.** \(\Lambda\) includes every proper prime
  power throughout; the model \(a(n)\) is a comparison object, not a
  replacement, exactly as in every inherited document.

All five hold, by inheritance; this document adds none of them and removes
none of them.

## 8. Grade

**Assembly of (2)-(3) from LOCALIZED_MIXED_ENERGY.md eq. (9), (12), (14),
(19), (25)-(26): PROVED, by citation** -- no new size estimate is claimed for
any \(\Delta\) term; the arithmetic is entirely the cited document's.
**The per-scale attribution of Section 4: an independent reading**, checked
against the actual proofs cited, in the same sense
[CHALLENGE.md](CHALLENGE.md) attack 3 is a reading of
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md)'s proof. **The battery run of
Section 5.1: MEASURED**, independently, to \(1.5\times10^{-16}\) relative
error at the module's own cross-check point, with the fast solver's code in
`s8_positivity_battery.py`. **The Omega-theorem consequence of Section 5.2:
CITED**, not proved here (standard theory, applied to a pinned zero, not
re-derived from Perron's formula in full rigor in this document).
**The magnitude comparison of Section 5.3: MEASURED**, robust at the computed
range, not asymptotic-sensitive. **The order discussion of Section 6: a
direct reading of already-established inequalities**, not a new estimate,
and not an improvement to \(E_{\rm corr}(N)\)'s total order.

No fixed power saving is claimed. No exceptional zero is asserted to exist or
excluded. This document does not reopen or weaken any inherited result; it
answers, specifically, whether a Section-8-compliant \(\mathrm{Energy}(N)\)
can be built whose domination proof survives the Davenport-Heilbronn battery
at the one step a merely-algebraic construction like
[CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md)'s could not identify. It can, at
the mean/central-mode scale, via \(\Lambda(n)\ge0\); it explicitly cannot, at
every other scale reused here, escape the ceiling `a-0070` describes for the
same reason CANDIDATE_ENERGY.md's construction escaped nothing: those scales
were never this document's new content.
