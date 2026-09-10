# Does Remark 2.8's larger Siegel-model parameter survive the endpoint chain?

2026-09-10. Base: the chain SIEGEL_UNIFORMITY.md -> EXCEPTIONAL_ENERGY.md ->
LOCALIZED_MIXED_ENERGY.md -> ENDPOINT_BOUND.md (reviewed in
ENDPOINT_BOUND_REVIEW.md). All of those files are unchanged by this pass.

**Verdict.** No. Substituted verbatim as printed in the source, the larger
model parameter breaks the chain at one identifiable place:
ENDPOINT_BOUND.md's Section 2 (the bounded-order/Bonferroni divisor
approximation), specifically its fixed cutoff \(m=2\lceil\sqrt{\log N}\rceil\)
feeding into the \(N^2D_0\sqrt Z\) term of equation (18). With that cutoff
unchanged, \(D_0=Z^m\) stops being \(N^{o(1)}\) and becomes \(\asymp N^2\),
so the single term \(N^2D_0\sqrt Z\) alone reaches order \(N^{4+o(1)}\),
which is larger than the trivial bound on \(E_{\rm corr}\) itself. This is
the first step in the chain that breaks.

Retuning \(m\) (rather than the whole architecture) recovers a chain that
tolerates every \(Q=\exp((\log N)^\kappa)\) with \(\kappa<1/2\) strictly, at
the cost of reverting from ENDPOINT_BOUND.md's sharp single exponent to an
\(\epsilon\)-indexed family, the same shape the pre-endpoint
SIEGEL_UNIFORMITY.md result already had at \(\kappa<1/10\):
\[
 E_{\rm corr}(N)\ll_\kappa N^3\exp(-c_\kappa(\log N)^\kappa),
 \qquad\text{every fixed }0<\kappa<\tfrac12.                    \tag{A}
\]
The value \(\kappa=1/2\) itself is not attained by this route; the supremum
\(1/2\) is open. This matches, rather than beats, what Remark 2.8's own
wording already concedes about Proposition 2.2 under the substitution: an
exponent "\(1/2-\epsilon\)", not a sharp \(1/2\). Either way, (A) is still an
exponential-in-a-fractional-power-of-\(\log N\) saving over \(N^3\), not the
near-quadratic \(N^{2+\epsilon}\) that CORRECTED_RH_BRIDGE.md needs for
RH-sufficiency. That target remains completely out of reach on this route,
independent of the wall identified here.

This is a handwritten deduction, checked against the source text quoted
below and against one finite numerical illustration; it is not a formal
verification.

## 1. What Remark 2.8 actually says

Fetched from the paper itself (arXiv:2107.02158v4, HTML rendering,
Section 2, printed immediately after Proposition 2.2):

Proposition 2.2 states, for every arithmetic progression \(P\subset[N]\),
\[
 \sum_{n\in P}(\mu(n)-\mu_{\rm Siegel}(n))\ll N\exp(-c\log^{1/10}N),
\]
and the analogous bound (2.5) for \(\Lambda-\Lambda_{\rm Siegel}\), both
using the default Siegel-model parameter \(Q=\exp((\log N)^{1/10})\)
fixed earlier in Section 2 (project name \(Z\)).

Remark 2.8, quoted:

> If one redefined the Siegel models \(\mu_{\rm Siegel},\Lambda_{\rm Siegel}\)
> by assigning the parameter \(Q\) the larger value \(\exp((\log N)^{1/2})\),
> one could inspect that the exponent of logarithm in (2.12) and (2.13)
> (and in particular in Proposition 2.2) could be increased to \(1/2-\epsilon\),
> hence essentially matching the shape of the error term in the classical
> prime number theorem. For this modification, one would have to tweak the
> exponents in Section 5 a little; in particular in Proposition 5.2 the
> exponents \(3/5\) and \(4/5\) would have to be replaced with \(1/2\). As
> the precise value of the exponent has very little influence on our
> bounds, we leave the details of this strengthening to the interested
> reader.

Two things follow directly from this text, before any of the project's own
machinery is touched.

**(i) The claimed exponent already carries an \(\epsilon\)-loss.** The
remark's own phrase is "increased to \(1/2-\epsilon\)", the same shape as
(2.12)-(2.13) (which are themselves \(\epsilon\)-indexed consequences of
the general higher-order theorem, TT Theorem 2.7). Proposition 2.2 as
printed and used by ENDPOINT_BOUND_REVIEW.md is *not* an \(\epsilon\)-family:
it is a single bound with a single fixed exponent \(1/10\) and a single
constant \(c\); ENDPOINT_BOUND_REVIEW.md's checked dependency list says
explicitly "[t]he endpoint exponent is obtained from this proposition. It
is not obtained by setting \(\kappa=1/10\) in Theorem 2.7." Nothing in
Remark 2.8 asserts that the strengthened statement keeps Proposition 2.2's
sharp, non-\(\epsilon\) form; its own wording says the opposite. So even
before checking the project's downstream files, citing "Proposition 2.2 at
\(Q=\exp((\log N)^{1/2})\)" as a drop-in replacement for [S1]'s (1) in
ENDPOINT_BOUND.md Section 1 already means replacing a sharp bound by a
family of bounds indexed by \(\epsilon\) -- which is exactly the family
shape that ENDPOINT_BOUND.md's whole point was to escape.

**(ii) The remark is an unverified aside, not a proved theorem.** The
authors explicitly did not carry out the retuning of their own Section 5
(Proposition 5.2, exponents \(3/5,4/5\to1/2\)) that the modification
requires; they "leave the details... to the interested reader." So even
taking (i) at face value, "Proposition 2.2 at \(Q=\exp((\log N)^{1/2})\)"
is not a citable statement of the source paper -- it is a claim the paper
says is plausible and does not prove. Anything built on it inherits that
gap on top of whatever the project's own files require.

Point (ii) is a caveat about the source, separate from the question the
task asks: whether the project's own chain (SIEGEL_UNIFORMITY.md through
ENDPOINT_BOUND.md), which largely does *not* reuse Proposition 2.2's proof
machinery but instead redoes an independent two-form sieve computation
around the same parameter \(Z=Q\), survives the substitution. Section 2
below answers that question directly and finds a harder, load-bearing
break inside the project's own arithmetic, independent of (i)-(ii).

## 2. Tracing \(t=\ell^{1/10}\to\ell^\kappa\) through each file

Write \(\ell=\log N\), and replace every occurrence of \(Z=\exp(\ell^{1/10})\)
in the chain by \(Z=\exp(\ell^\kappa)\), \(t=\ell^{1/10}\) by \(t=\ell^\kappa\),
tracking each place a *specific number* (not just the symbol \(1/10\)) was
chosen because of the specific value \(\kappa=1/10\).

### 2.1 SIEGEL_UNIFORMITY.md -- survives up to and including \(\kappa=1/2\)

Section 3's sieve estimate (10)-(11) uses TT Lemma 5.1 (the classical
fundamental lemma of the sieve, not paper-specific machinery) at level
\(D=\lfloor N^{1/4}\rfloor\), a level chosen freely by the project, not
inherited from \(Z\). Its exponent parameter is
\(s=\log D/\log Z\asymp\ell^{1-\kappa}/4\); the stated remainder
\(O(Ne^{-cL^{9/10}})\) becomes \(O(Ne^{-c\ell^{1-\kappa}})\). For any fixed
\(\kappa<1\), \(s\to\infty\) and the fundamental lemma applies; at
\(\kappa=1/2\) the remainder is \(O(Ne^{-c\ell^{1/2}})\), matching (not
beating, but not breaking) the target order. The other error term,
\(D(1+\log D)=O(N^{1/4}\log N)\), is independent of \(Z\) entirely and stays
negligible. Section 1's use of TT (2.13) (the general Theorem 2.7
consequence, at \(k=2\)) is exactly the kind of statement Remark 2.8
targets, so it inherits caveats (i)-(ii) above but no *new* project-level
break; it was already an \(\epsilon\)-family before this substitution.
Section 2, "A uniform sieve calculation," and Sections 4-5 (exceptional
term bookkeeping) use \(q<Z<\sqrt N\); this remains true for any fixed
\(\kappa<1\). No numeric parameter here is tied specifically to \(1/10\).

### 2.2 EXCEPTIONAL_ENERGY.md and LOCALIZED_MIXED_ENERGY.md -- survive

EXCEPTIONAL_ENERGY.md Section 5's range bookkeeping,
\((\log q)^{10}<\log N<(c_0/\delta)^{10}\) (its equation 27), comes from
inverting \(q<Z=\exp(\ell^{1/10})\); at general \(\kappa\) the exponent
\(10\) becomes \(1/\kappa\) (e.g. \(2\) at \(\kappa=1/2\)). This is a
bookkeeping substitution, not a break: nothing else in that file's period-mass
or lower-bound argument (Sections 3-4) depends on \(1/10\) specifically,
only on \(q<Z<N\).

LOCALIZED_MIXED_ENERGY.md's own fixed exponents -- the rational-denominator
cutoff \(R=N^\rho\) at \(\rho=1/10\) in its equation (13), and the short-kernel
cutoff \(L_0=\lfloor N^{3/5}\rfloor\) in (14) -- are chosen freely against
\(N\), not against \(Z\); they do not need retuning. Its long-window estimate
(19), \(T_N(0)\ll N^3e^{-c\mathcal L(N)}\) with \(\mathcal
L(N)=\ell^{3/5}(\log\ell)^{-1/5}\), is the classical prime number theorem
rate (TT Theorem 1.3(i)) and does not involve \(Z\) at all; its exponent
\(3/5\) already exceeds \(1/2\), so it is not the bottleneck at \(\kappa=1/2\)
either. This file's own stated bottleneck (Section 6) is the inherited
\(O(N^{3/2}e^{-c\ell^{1/10}})\) model-comparison term from
SIEGEL_UNIFORMITY.md/ENDPOINT_BOUND.md, i.e. it is downstream of whatever
those two files produce, not an independent obstruction.

### 2.3 ENDPOINT_BOUND.md Section 2 -- breaks at \(\kappa=1/2\)

This is where the substitution fails, in a part of the chain that is the
project's own construction, not TT's. Section 2 approximates
\(\nu(n)=b_Z1_{(n,P(Z))=1}\) by the bounded-order Möbius sum
\(B_m(n)=\sum_{d\mid P,\,d\mid n,\,\omega(d)\le m}\mu(d)\), with
\[
 m=2\lceil\sqrt\ell\rceil,\qquad D_0=Z^m,
\]
fixed once, not as a function of \(\kappa\). Equation (5)-(6) bounds the
approximation error by \(N H_Z^{m+1}/(m+1)!\) with \(H_Z\le1+\log Z=1+\ell^\kappa\),
and the write-up's own derivation ("the elementary estimate \(H_Z\le1+\log Z\)
and \(k!\ge(k/e)^k\)") only checks this decays *for \(\kappa=1/10\)*. The
same computation at general \(\kappa\), with \(m=2\lceil\sqrt\ell\rceil\) held
fixed, gives ratio
\[
 \frac{H_Ze}{m+1}\ \sim\ \frac e2\,\ell^{\kappa-1/2},
\]
which \(\to0\) (so the Bonferroni error genuinely decays) only for
\(\kappa<1/2\); at \(\kappa=1/2\) it tends to the *constant* \(e/2\approx1.36>1\),
so \((H_Ze/(m+1))^{m+1}\) does not shrink as \(N\to\infty\) -- the truncation
error stops being an error term at all. Simultaneously,
\[
 \log D_0 = m\log Z = 2\lceil\sqrt\ell\rceil\cdot\ell^\kappa
                \ \sim\ 2\ell^{\,\kappa+1/2}.
\]
At \(\kappa=1/10\) this is \(2\ell^{3/5}=o(\ell)\), exactly what
ENDPOINT_BOUND_REVIEW.md's budget section records
(\(\log(D_0\sqrt Z)=2\ell^{3/5}+O(\ell^{1/10})=o(\ell)\)), keeping
\(D_0=N^{o(1)}\) and the term \(N^2D_0\sqrt Z\) at \(N^{2+o(1)}\), comfortably
inside the \(N^3\) budget of equation (18). At \(\kappa=1/2\) this becomes
\(\log D_0\sim2\ell\), i.e. \(D_0\asymp N^2\), and the single term
\(N^2D_0\sqrt Z\) in (18) reaches order \(N^{4+o(1)}\) -- larger than
\(N^3\) outright, let alone smaller than \(E_{\rm corr}\)'s target order.
This is the first place the chain breaks: the fixed numeric cutoff
\(m=2\lceil\sqrt\ell\rceil\) was tuned for \(\kappa=1/10\) and is simply
the wrong cutoff at \(\kappa=1/2\), not a small constant-factor loss but a
qualitative one (the divisor-approximation device stops producing any
saving at all).

**This does not improve with a different (untuned) choice of \(m\).**
Write \(m=\lambda H_Z\) for a parameter \(\lambda\) to be chosen (constant
or slowly growing). Decay of the Bonferroni error needs
\(H_Ze/m=e/\lambda\to0\), i.e. \(\lambda\to\infty\), or at least
\(\lambda>e\) for a nontrivial fixed bound. But then
\[
 \log D_0=m\log Z=\lambda H_Z\log Z\sim\lambda\,\ell^{2\kappa}/\ell^{\,?}
\]
more precisely, with \(H_Z\sim\ell^\kappa\) and \(\log Z=\ell^\kappa\),
\(\log D_0\sim\lambda\ell^{2\kappa}\), so
\(A(N):=\log D_0/\log N\sim\lambda\ell^{2\kappa-1}\). For \(\kappa<1/2\),
\(\ell^{2\kappa-1}\to0\), so \(\lambda\) can be sent to infinity slowly
enough that \(A(N)\to0\) *and* \(\lambda>e\) eventually -- both requirements
are simultaneously satisfiable, and \(D_0=N^{o(1)}\) is recoverable with a
retuned \(m\). At \(\kappa=1/2\) exactly, \(\ell^{2\kappa-1}=\ell^0=1\)
identically, so \(A(N)\sim\lambda\) is pinned to whatever constant
\(\lambda\) is chosen; decay of the Bonferroni error forces \(\lambda>e\),
so \(A(N)>e\) unavoidably, giving \(D_0\gtrsim N^e\) and
\(N^2D_0\sqrt Z\gtrsim N^{2+e+o(1)}\gg N^3\) no matter how \(m\) is chosen.
**No choice of \(m\) makes this device produce a saving at \(\kappa=1/2\).**
For any fixed \(\kappa<1/2\) it works, with the achievable margin
\((1/2-\kappa)\) shrinking to zero as \(\kappa\to1/2\).

### 2.4 Numerical illustration

`artifacts/endpoint_half/check.py` (one thread, closed form, no
distribution-theory input) evaluates \(A(N)=\log D_0/\log N\) for the
*fixed* cutoff \(m=2\lceil\sqrt\ell\rceil\) exactly as printed in
ENDPOINT_BOUND.md, at \(\kappa\in\{0.1,0.3,0.45,0.49,0.5,0.6\}\) and
\(N=10^{20},10^{100},10^{1000},10^{10000}\), and separately finds, at fixed
\(N=10^{60}\), the smallest \(m\) for which the raw ratio
\(H_Z^{m+1}/(m+1)!\) first drops below 1, for the same \(\kappa\) values.
Both confirm Section 2.3 quantitatively:

- \(\kappa=0.1\): \(A(N)\) falls from \(0.45\) to \(0.036\) as \(N\) runs
  \(10^{20}\to10^{10000}\) (heading to \(0\), as expected: \(o(1)\)).
- \(\kappa=0.3\): \(A(N)\) falls from \(0.96\) to \(0.27\) (still heading
  to \(0\), more slowly).
- \(\kappa=0.45\): \(A(N)\) falls from \(1.70\) to \(1.21\) over the same
  range -- decreasing, consistent with \(o(1)\) asymptotically
  (\(\ell^{\kappa-1/2}=\ell^{-0.05}\) decays extremely slowly), but nowhere
  near \(0\) at any \(N\) that could ever be written down. The fixed
  \(m=2\lceil\sqrt\ell\rceil\) is asymptotically fine but practically the
  wrong cutoff as \(\kappa\to1/2\); a retuned, \(\kappa\)-dependent \(m\)
  is genuinely needed, not optional, well before \(\kappa=1/2\) is reached.
- \(\kappa=0.49\) and \(\kappa=0.5\): \(A(N)\) sits at \(1.8\)-\(2.0\) and
  \(2.0\)-\(2.1\) respectively across the entire tested range, matching the
  closed form \(A\sim2\ell^{\kappa-1/2}\to2\ell^0=2\) exactly at
  \(\kappa=1/2\): no decay, a genuine power \(D_0\asymp N^2\).
- \(\kappa=0.6\): \(A(N)\) *grows* with \(N\) (\(3.0\to5.5\)), matching
  \(2\ell^{0.1}\to\infty\): the device is not merely stalled but actively
  diverges past \(\kappa=1/2\).
- The minimal-\(m\) table, at fixed \(N=10^{60}\), shows
  \(m_{\min}/H_Z\) sitting at \(1.9\)-\(2.6\) across every tested \(\kappa\)
  (pre-asymptotic; the true threshold is \(e\approx2.718\)), and the
  resulting \(A\) at that minimal \(m\) climbing from \(0.06\) at
  \(\kappa=0.1\) to \(2.43\)-\(2.64\) at \(\kappa=0.49,0.5\) -- direct
  confirmation that the minimal viable \(m\) for decay forces \(A\) up
  toward the constant \(e\), not down toward \(0\), exactly where the
  algebra of Section 2.3 says it must.

Raw output is saved in `artifacts/endpoint_half/result.json`.

## 3. What this means for the budget (18) and the m = 2⌈√(log N)⌉ / D_0√Z term specifically

The task's own question was precisely whether \(m=2\lceil\sqrt{\log N}\rceil\)
and the \(D_0\sqrt Z\) term survive. They do not, verbatim, at
\(\kappa=1/2\): the single term \(N^2D_0\sqrt Z\) in equation (18) of
ENDPOINT_BOUND.md moves from \(N^{2+o(1)}\) (comfortably absorbed) to at
least \(N^{4+o(1)}\) (dominating the entire budget and exceeding even the
trivial \(O(N^3)\) bound on \(E_{\rm corr}\) coming from
\(|r(h)|,|C_N(h)|\le O(N)\) pointwise). Every other term in (18) --
\(N^3R^7e^{-2\gamma t}\), \(N^3R^{-1/6}\), \(N^{14/5}\), and the two
remaining exponential terms -- either scales benignly with \(t=\ell^\kappa\)
(the major/minor arc terms, Sections 3-4 of ENDPOINT_BOUND.md, which
actually *improve* as \(\kappa\) grows, since \(R=\exp(\sigma t)\) grows
faster) or is a fixed power of \(N\) below \(3\) regardless of \(\kappa\)
(the Montgomery-Vaughan \(N^{14/5}\) term, from a classical estimate that
does not reference \(Z\) at all). The Bonferroni/\(D_0\sqrt Z\) term is the
only one that is qualitatively, not just quantitatively, broken by the
substitution.

## 4. Largest \(Q\) the chain tolerates, and the exponent it yields

Retuning \(m\) as a function of \(\kappa\) -- e.g.
\(m=\lceil\lambda(N)\cdot\ell^{1/2-\kappa}\cdot\ell^\kappa\rceil\) for any
slowly growing \(\lambda(N)\to\infty\) with \(\lambda(N)>e\) eventually,
matching the derivation in Section 2.3 -- and correspondingly retuning
EXCEPTIONAL_ENERGY.md's range bookkeeping (Section 2.2 above), the chain
tolerates
\[
 Q=\exp((\log N)^\kappa)\qquad\text{for every fixed }0<\kappa<\tfrac12,
\]
with \(\kappa=1/2\) itself excluded (Section 2.3 shows no choice of \(m\)
works there). This yields, chain-wide,
\[
 E_{\rm corr}(N)\ll_\kappa N^3\exp(-c_\kappa(\log N)^\kappa),
 \qquad\text{every fixed }0<\kappa<\tfrac12,
\]
i.e. exactly statement (A) from the top of this file: an improvement over
the pre-endpoint family (which only reached \(\kappa<1/10\)), but a
reversion from ENDPOINT_BOUND.md's sharp single exponent
\(\kappa=1/10\) back to an \(\epsilon\)-indexed family, capped strictly
below \(1/2\). Reaching a sharp \(\kappa=1/2\) endpoint -- the literal
reading of the task's target
\(E_{\rm corr}(N)\ll N^3\exp(-c(\log N)^{1/2-\epsilon})\) with a single
substituted budget -- is not available from this chain as constructed,
because its own divisor-approximation device (Section 2.3) has no slack
left at exactly \(\kappa=1/2\), independent of whether Remark 2.8's
unverified claim about Proposition 2.2 itself (Section 1, points (i)-(ii))
is granted or not.

Nothing here excludes a *different* proof of the minor-arc control TT's
Proposition 2.2 supplies -- one that does not route through a
bounded-order/Bonferroni divisor approximation of \(\nu\) at all -- from
reaching \(\kappa\) closer to or at \(1/2\); Section 2.3 identifies a wall
in this specific project construction, not a theorem that no construction
can do better.

## 5. Scope

Written under `hunts/prime_pair_error/` only. No file outside this
directory was read or touched. No claim of proof, disproof, or external
validation beyond the finite check in `artifacts/endpoint_half/` is made.
