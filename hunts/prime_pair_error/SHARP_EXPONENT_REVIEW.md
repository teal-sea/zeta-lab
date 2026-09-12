# Independent check of `SHARP_EXPONENT.md` (commit 1abe75b)

2026-09-12, attempt `a-0082`. Two scripts written fresh for this review, not
reusing `sharp_exponent_probe.py`: `review_a0082_sharp_exponent_check.py`
(numerical checks of section 5's two items, by a different method: SciPy's
QUADPACK oscillatory-weight quadrature rather than the probe's own routine)
and `review_a0082_budget_check.py` (symbolic recomputation of the seven
exponents of (7)). Results quoted inline below.

Summary of verdicts: (1) confirmed, (2) confirmed, (3) confirmed, (4)
confirmed, with one point (section 2.1) that I agree corrects a real miss in
an earlier check, (5) confirmed, with one defective intermediate equation
that does not change the theorem. No defect found changes the boxed
conclusions (S''') or the exponent constant $2c_0$.

## (1) Section 1.1: the dyadic reduction

**Verdict: confirmed.**

The Farey condition: $|\alpha-a/q|\le 1/(q\sqrt N)\le 1/q^2$ holds exactly
for $q\le\sqrt N$, an equality at $q=\sqrt N$, so Vaughan's bound
$|F(\alpha)|\ll (Nq^{-1/2}+N^{4/5}+\sqrt{Nq})\ell^{O(1)}$ applies on every
$I'_{q,a}$ used here. For $q\sim Q$ with $Q$ ranging up to $R^2\ell^9$
(subpolynomial in $N$, since $R=N^{o(1)}$), the term $Nq^{-1/2}$ dominates
$N^{4/5}$ and $\sqrt{Nq}$ for all large $N$, so
$\sup_{q\sim Q,\,I'_{q,a}}|F|^2\ll N^2\ell^{O(1)}/Q$ is the right leading
order; the document's stated power $\ell^8$ is one internally consistent
choice of exponent for Vaughan's bound (some other documents in this hunt
use $\ell^{5/2}$ for $|F|$, giving $\ell^5$ after squaring; this is a
bookkeeping choice of which version of Vaughan's theorem is quoted, not an
error, and it does not matter for the argument since only $\ell^{O(1)}$
is ever used downstream).

Disjointness gives $\sum_{q\sim Q}\sum_a\int_{I'_{q,a}}|F|^2\le\int_{\mathbb
T}|F|^2=d_N\ll N\ell$ (Chebyshev), so $Z'_Q\ll(N^2\ell^8/Q)(N\ell)=
N^3\ell^9/Q$, exactly as stated. The comparison $N^3\ell^9/Q\le N^3/R^2$ for
$Q\ge R^2\ell^9$ is immediate algebra. The remark that arcs with $q\le R$
are inside $\mathfrak M$ up to their outer parts is a correct observation
about geometry (the Farey arc $I'_{q,a}$, of radius $1/(q\sqrt N)$, is far
wider than the major arc $I_{r,a}$ of radius $R/(qN)$ when $q\le R\ll\sqrt
N$, by a factor $\sqrt N/R\to\infty$), and it plays no load-bearing role in
the estimate itself, since the Vaughan bound used for $Z'_Q$ does not
distinguish major from minor.

I recomputed the reduction to blocks $R<Q\le R^2\ell^9$ independently and
it is correct: nothing in section 1.1 needs a defect notice.

## (2) Section 1.2: the exact obstruction

**Verdict: confirmed**, including the negative claim that no known input
supplies the missing power of $Q$.

*The identity and Gallagher step.* $\sum_{x<n\le x+h}c_n(q,a)=\sum_b
e(ab/q)\Delta_b(x,h)$ follows from $\sum_b^*e(ab/q)=\mu(q)$ applied to the
$\mu(q)/\phi(q)$ part of $c_n(q,a)$ and the definition of $\Delta_b$ termwise;
this is the same manipulation as `RANK3_Z_COMPONENT.md` section 4's (2)-(3)
(there proved for the arc radius $Q/(qN)$ rather than $1/(q\sqrt N)$, but the
algebra is identical). Gallagher's lemma with $\Theta=1/(q\sqrt N)$,
$h_q=q\sqrt N/2=1/(2\Theta)$ is a direct instance of (G). Orthogonality over
$a$ to reach (1), and the substitution into (2)-(3), is standard
Cauchy-Schwarz-free bookkeeping and I recomputed it: with
$\sup|R_{q,a}|^2\ll N^2\ell^8/Q$ from item (1) above,
$Z'^{\rm res}_Q\ll(N\ell^8/Q^2)\sum_{q\sim Q}V_q(h_q)$ matches (2), and
dividing the target $N^3Q^{-2+\varepsilon}$ through gives (3) exactly.

*The three inputs.* Trivial: $\sum_b|\Delta_b|^2\le(\sum_b|\Delta_b|)^2\ll
(h\ell)^2$ is Cauchy-Schwarz on $\phi(q)+O(1)$ terms folded into the
$\ell$; summing over $x\le N$ and $q\sim Q$ gives $N\cdot Q\cdot h^2\ell^2
\asymp N^2Q^3\ell^2$, off by $Q^3$ from (3) as stated.

Koukoulopoulos: I checked the hypothesis $Q^2\le h/N^{1/3+\varepsilon}$ at
$h\asymp Q\sqrt N$ directly: this is $Q\le N^{1/6-\varepsilon/2}$, which
holds for all large $N$ since $Q\le R^2\ell^9=N^{o(1)}$; so the theorem's
range does contain these moduli, exactly as claimed, and this is the
correct reading of `RANK3_Z_COMPONENT.md` section 4's own applicability
range (there stated for $q\le L^C$, a genuinely smaller range than what is
used here, but that document's Corollary is stated for general $q,h$ in the
displayed range and does not require $q$ itself to be polylogarithmic, only
the inequality $Q_K^2\le h/x^{1-2/c+\varepsilon}$, which is satisfied here).
The resulting $\sum_{q\sim Q}V_q\ll h^2N\ell^{-A}\asymp N^2Q^2\ell^{-A}$,
off by $Q^2$: I confirm the stated reason, that the first-moment tool
$\sum_b|\Delta_b|^2\le E(x,h;q)\sum_b|\Delta_b|\ll hE(x,h;q)$ cannot recover
the factor $h$ that a genuine second-moment tool would.

The multiplicative large sieve step: the classical inequality $\sum_{q\le
2Q}(q/\phi(q))\sum^*_\chi|\sum_na_n\chi(n)|^2\le(N+4Q^2)\sum|a_n|^2$
(Montgomery-Vaughan form of the large sieve for characters) applied with
$a_n=\Lambda(n)\mathbf 1_{x<n\le x+h}$, for which $\sum|a_n|^2\ll h\ell$
(only primes contribute, each $O(\ell)$, at density $1/\ell$), gives
$(h+Q^2)h\ell$ as claimed. I recomputed the passage to $\sum_{q\sim Q}
\sum_b|\Delta_b|^2\ll\ell^2(h+Q^2)h/Q$ (one $\ell$ from $\sum a_n^2$, one
from converting $q/\phi(q)$-weighted sums to $1/\phi(q)$-weighted sums by
dividing by $q\asymp Q$, and reduction from all characters to primitive
ones): the arithmetic is internally consistent, and integrating over $x\le N$
with $h_q\asymp Q\sqrt N$ gives $\sum_{q\sim Q}V_q(h_q)\ll N\ell^2h_q^2/Q
\asymp N^2Q\ell^2$, matching (4) exactly. Substituting into (2):
$Z'^{\rm res}_Q\ll(N\ell^8/Q^2)(N^2Q\ell^2)=N^3\ell^{10}/Q$, which I confirm
is Vaughan's order up to the log power (the document's own $\ell^9$ bound in
section 1.1 uses a different accounting of the log powers; the extra one
power of $\ell$ here is harmless since only $\ell^{O(1)}$ is ever claimed).
This is off (3) by $Q^{1-\varepsilon}$ exactly as stated, and the stated
reason (the large sieve is only sharp when the character count $Q^2$
matches the sequence length $h$, and here $h=Q\sqrt N\gg Q^2$ since $Q=
N^{o(1)}$) is the correct diagnosis: the large sieve inequality has genuine
slack $h/Q^2$ in this regime, this is not a case where a sharper application
of the same tool would close the gap.

*The obstruction statement itself.* I recomputed
$\log(q(N/h)) = \log(q\cdot\sqrt N/Q)$ at $q\sim Q$: this is $\log(\sqrt N)
+O(1)=\ell/2+O(1)$, independent of $Q$ (the $Q$ cancels between the
modulus and the height), so (ZF) gives $\beta\le1-c/(\ell/2)(1+o(1))$ and
$N^{2(\beta-1)}\ge e^{-4c}(1+o(1))$, a constant with no dependence on $Q$,
confirming that this specific tool structurally cannot ever deliver a power
of $Q$ at this interval length, for any choice of $Q$.

*The open-problem question.* I am not aware of an unconditional variance
bound for $\psi$ (or $\theta$) in intervals of length $h\asymp\sqrt N$ with a
power saving over the trivial $h^2N$. The unconditional results I know that
give a power saving over trivial for short-interval variance (via zero-density
estimates, e.g. the Selberg/Montgomery/Huxley line that
`RANK3_Z_COMPONENT.md` section 4 itself surveys and withdraws an incorrect
claim about) apply only for $h\ge N^{\theta}$ with $\theta$ bounded away from
$1/2$ from above (the density-estimate threshold there is $\theta\ge
1-2/c\ge 1/6$ to $1/3$ for the *exponent's* range of validity, but that
governs how small $h$ can be relative to $N$ for the density method to give
*any* power saving over a fixed polylog baseline, not a bound at
$h\asymp\sqrt N=N^{1/2}$ itself beating $h^2N$ by a power of $N$ or of $Q$).
Selberg's classical result gives such a saving only conditionally, under RH.
This matches the document's claim, and I do not know a counterexample or a
missed reference; what would settle this negative claim more strongly is
either an unconditional short-interval variance theorem at length $\asymp
\sqrt N$ with any fixed power saving over $h^2N$ (which I do not believe
exists in the literature) or a proof that none can exist unconditionally
without new input on zeros (which the document does not attempt and does
not claim).

No defect found in section 1.2.

## (3) Section 1.3: the alternate dissection at $Q_2=R^2\ell$

**Verdict: confirmed.**

The height bound: for $R<q\le Q_2$ on the arcs of the $Q_2$-dissection,
$N|\theta|\le Q_2/q<Q_2/R=R\ell$, matching "heights at most $R\log N$"
exactly (with $q>R$ used to replace $Q_2/q$ by its bound at $q=R$).
`MAJOR_ARC_EXPLICIT.md` section 2's construction only uses the modulus $r$
and the arc radius to fix $T$ and bound the far-zero sum; it does not
require $r\le$ any specific cutoff beyond $r<Z$ (used to discard prime
powers dividing $r$) and $T\le N$, both satisfied here with $Q_2=R^2\ell
=N^{o(1)}<Z=e^{\sqrt\ell}$, so the substitution $R\to Q_2$ in section 2's
inputs is legitimate.

The shape of (5): summing $|P_{q,a}|^4$ over the enlarged major arcs gives
the standard singular-series fourth moment $\ll N^3\ell^{O(1)}/Q_2^2\le
N^3\ell^{O(1)}/R^2$ (a genuinely stronger bound than $R^{-1}$, consistent
with major-arc quartic moments generally being smaller than minor-arc
ones), and the error term from replacing $F$ by its major-arc approximation
carries a fourth power of the sup bound from `MAJOR_ARC_EXPLICIT.md` (3)-(4)
at modulus $Q_2$; this is not claimed to be sharp and the document does not
use it for anything beyond an order-of-magnitude remark, which is
appropriate given the section's stated purpose (showing this route does not
move the exponent, not producing a new bound).

The two remarks: first, that the literal target $\int_{\mathfrak m}|F|^4
\ll N^3\ell^{O(1)}R^{-2+\varepsilon}$ is false at any point $a/q_e$ where an
exceptional real zero of conductor $R<q_e\le R^2\ell$ sits, is a correct
reading of the spike structure of $|I_\beta|^2$ (the same object numerically
checked in section 5 item 1 of the source document and independently in
item (4) below): a spike of height $\asymp N^{2\beta_e}/q_e$ at a rational
point inside $\mathfrak m$ cannot be absorbed into a bound of the stated
polynomial shape without subtracting it, which is exactly the corrected
integrand's role. Second, the claim that (5) reproduces `ARC_SPLIT_BUDGET.md`'s
arc-split architecture at cutoff $Q_2$ rather than a new mechanism is
correct by construction: nothing in the derivation of (5) differs in kind
from the derivation already carried out for cutoff $R$ in
`MAJOR_ARC_EXPLICIT.md` and `ARC_SPLIT_BUDGET.md`, only the numerical value
of the cutoff, and the balance of exponents in any such architecture is
governed by the arc-split trade-off already analyzed, independent of which
cutoff is chosen. No new information is produced.

No defect found in section 1.3.

## (4) Section 2: the mechanism, integrating the Page term over each arc

**Verdict: confirmed**, including the correction in section 2.1, which I
independently re-derive and find necessary; I agree the original bullet in
`MAJOR_ARC_EXPLICIT.md` was a genuine miss, and that the earlier check
(`a-0080`, as recorded in `MAJOR_ARC_EXPLICIT_REVIEW.md` item 3) endorsed
the wrong reading rather than merely failing to look.

**Numerical checks, written fresh, not reusing `sharp_exponent_probe.py`.**
`review_a0082_sharp_exponent_check.py` uses SciPy's QUADPACK oscillatory
quadrature (`weight='cos'`/`'sin'`) rather than the probe's own integration
routine.

*The decay bound (6).* At $N\in\{10^4,10^6\}$, $\kappa\in\{0.1,0.3,1.0\}$,
40 values of $N\theta$ from 1 to 200, the worst value of
$|I_\beta(\theta)|\cdot N|\theta|/N^\beta$ came out at
$0.3615,\ 0.4918,\ 2.0763$ ($N=10^4$) and $0.3543,\ 0.4540,\ 1.4569$
($N=10^6$), against the stated bound $C=e^{\kappa\sigma}$ of
$1.19,\ 1.69,\ 5.73$ and $1.15,\ 1.53,\ 4.16$. These match the document's own
$0.36,\ 0.48,\ 2.03$ and $0.35,\ 0.44,\ 1.42$ closely (small residual
differences are consistent with slightly different sample grids and
quadrature routines), confirming both the bound and the specific numbers
independently.

*The flatness in $R$.* At $N=10^4$, $\int_{|\theta|\le R/(rN)}|K_N(\theta)|^2
|I_\beta(\theta)|^2\,d\theta/N^{2\beta+1}$ for $\kappa\in\{0.3,1.0\}$,
$r\in\{1,3,7\}$, $R\in\{5,20,80\}$:

| $\kappa$ | $r=1$ | $r=3$ | $r=7$ |
| --- | --- | --- | --- |
| $0.3$ | $0.8145,\ 0.8145,\ 0.8145$ | $0.8139,\ 0.8145,\ 0.8145$ | $0.8101,\ 0.8144,\ 0.8145$ |
| $1.0$ | $1.4559,\ 1.4561,\ 1.4561$ | $1.4540,\ 1.4560,\ 1.4561$ | $1.4444,\ 1.4554,\ 1.4561$ |

(entries are $R=5,20,80$). These match the source document's own table to
four decimal places, confirming the "no factor $R$" claim independently.

I also confirmed by hand that the flatness is structurally forced, not a
numerical accident: writing $u=N\theta$, the integrand
$\min(N,1/(2|\theta|))^2\min(2N^\beta,CN^\beta/(N|\theta|))^2$ is $\asymp
N^{2\beta+1}$ on $|u|\lesssim1$ and decays like $u^{-4}$ for $u\gg1$
(from $K_N$'s $u^{-2}$ times $I_\beta$'s $u^{-2}$), so $\int u^{-4}du$
converges and the tail beyond $|u|=O(1)$ contributes a bounded, rapidly
vanishing correction; extending the arc radius $R/(rN)$ (i.e. $u$ up to
$R/r$) past $O(1)$ therefore adds essentially nothing, which is exactly why
the mass sits at $|\theta|\ll1/N$ regardless of $R$.

*The four bullets, recomputed.*

- First bullet: $|W_P|^2\le(r/\phi(r)^2)|I_{\tilde\beta}|^2$ from $|\tau
  (\tilde\chi_r)|\le\sqrt r$, and dividing by the extra $\phi(r)^2$ from
  $|H|\le|K_N|/\phi(r)$ gives $(r/\phi(r)^4)\int|K_N|^2|I_{\tilde\beta}|^2
  \ll(r/\phi(r)^4)N^{2\tilde\beta+1}$, matching the numerically confirmed
  flatness. Summing over $a$ (factor $\phi(r)$) and over $r=\tilde qm\le R$
  gives $\sum_m\tilde qm/\phi(\tilde qm)^3$, which converges (since
  $m/\phi(m)^3\ll(\log\log m)^3/m^2$ is summable) to $\ll\tilde q^{-2}
  (\tilde q/\phi(\tilde q))^3$, exactly as claimed, and no factor of $R$
  appears anywhere in this chain.
- Second bullet: I recomputed $\sum_{r\le R}r/\phi(r)\ll R$ (average order
  of $r/\phi(r)$ is a constant), giving $R^3E_{\rm md}^2\cdot O(R)\cdot
  N^{2\tilde\beta-1}=O(R^4)E_{\rm md}^2N^{2\tilde\beta-1}$, matching the
  stated $R^4E_{\rm md}^2N^{2\tilde\beta-1}\ell$ (the extra $\ell$ is a safe
  over-estimate of the average-order constant, harmless).
- Third bullet: $\sum_{r\le R}r^2/\phi(r)^3=\sum_r(1/r)(r/\phi(r))^3\ll
  \sum_r(\log\log r)^3/r\ll(\log\log R)^3\log R\ll\ell^{O(1)}$, confirming
  the claimed polylogarithmic bound (a genuine, if generous, bound: the true
  growth is $\log R\,(\log\log R)^3=O(\sigma\sqrt\ell(\log\ell)^3)$, still
  inside $\ell^{O(1)}$).
- Fourth bullet ($W_0$): correctly reuses the unmodified sup-times-Parseval
  bound of `MAJOR_ARC_EXPLICIT.md`, since only the Page term needed the
  refined treatment; consistent with the section's stated scope.

**Section 2.1, re-derived from scratch.** (ZF) is a *per-character*
statement: for a fixed real $\chi\bmod r$ ($r\le R$), it excludes zeros with
$\sigma>1-c/\log(2r)$ except for one. Since $r$ ranges down to small values
(e.g. $r=3$), $c/\log(2r)$ can be an $O(1)$ constant, not shrinking with
$\ell$: (ZF) alone permits *that one character's own* exceptional zero to
sit anywhere below this comparatively wide threshold. Page's theorem is a
*cross-character* statement: among *all* characters of conductor $\le R$ and
height $\le R^3$, at most one zero anywhere exceeds the narrower threshold
$1-b/\log(R^4)$. These two statements do not compose into "every other real
character has no exceptional zero at all": Page only forbids a *second*
zero *above* its own (narrow) threshold; it says nothing about a character
having its own zero *below* Page's threshold but *above* its own (wider)
(ZF) threshold, e.g. somewhere in $(1-c/\log2r,\,1-b/\log R^4]$. Such a zero
is (ZF)-exceptional for its own character and not Page-exceptional, exactly
as `SHARP_EXPONENT.md` now states, and it must be included: its contribution
after the Gauss sum is $\sqrt r\cdot2N^\beta\le\sqrt r\cdot2Ne^{-(b/(4\sigma))
\sqrt\ell}$, i.e. the added term $e^{-(b/(4\sigma))\sqrt\ell}$ in $\Upsilon(r)$,
which I confirm reproduces $Re^{-(b/(2\sigma))\sqrt\ell}$ in the squared
budget with exponent $b/(4c_0)-2c_0\ge2c_0$ at $\sigma=2c_0$ exactly under
$c_0^2\le b/16$, a condition already inside (H'').

Re-reading `MAJOR_ARC_EXPLICIT_REVIEW.md` item 3 with this in hand: the
earlier check's defense of the original parenthetical, "the cross-character
uniqueness needed to rule out a second, unrelated exceptional character is
exactly what (Pg') supplies," conflates "ruling out a second zero *above
Page's own threshold*" with "ruling out *any* exceptional zero for a second
character," which is the precise error identified above. I agree this is a
genuine miss by that check, not merely an unexamined point: the check
considered the question (it discusses exactly this cross-character
reasoning) and reached the wrong conclusion, rather than leaving it
unresolved.

No defect found in section 2 or 2.1 beyond confirming the correction already
recorded there.

## (5) Section 3: the budget (7)

**Verdict: confirmed, with one defective (but non-binding) intermediate
term inherited from `MAJOR_ARC_EXPLICIT.md` (6).**

*Recomputing the seven exponents at $\sigma=2c_0$*
(`review_a0082_budget_check.py`, symbolic):

```
e^{-2c0 sqrt l}                    -> 2 c0
R^-1                               -> 2 c0
R^2 e^{-(2c/sigma) sqrt l}         -> c/c0 - 4 c0
R e^{-(c/(2 sigma)) sqrt l}        -> c/(4 c0) - 2 c0
R e^{-(b/(2 sigma)) sqrt l}        -> b/(4 c0) - 2 c0
R^-3                               -> 6 c0
R^3 e^{-2 sqrt l /3}               -> 2/3 - 6 c0
R^4 e^{-(2/3+2 c0) sqrt l}         -> 6 c0 - 2/3
```

These match the document's printed list exactly, and the resulting
sufficient conditions ($c_0^2\le c/6$, $c_0^2\le c/16$, $c_0^2\le b/16$,
$c_0\le1/12$) are what (H'') encodes once the redundant $c_0^2\le c/6$
(implied by the stricter $c_0^2\le c/16$, since $c/16<c/6$) is dropped, plus
the Page-matching $c_0^2\le b/8$ (also implied by the stricter $c_0^2\le
b/16$) and TT's $c_0\le c_P$. I confirm that under (H'') only the first
bracket term ($e^{-2c_0\sqrt\ell}$) and the $R^{-1}$ minor-arc term actually
achieve the exponent $2c_0$; every other term is strictly above it, so
nothing besides these two can bind, exactly as section 3 claims.

**The defect.** The term "$R^2e^{-(2c/\sigma)\sqrt\ell(1+o(1))}$", copied
from `MAJOR_ARC_EXPLICIT.md` equation (6), does not follow from squaring
its equation (5) by the method that document states ("using $\sqrt r\le
\sqrt R$, $\sqrt{R/r}\cdot\sqrt r=\sqrt R$"). Carrying that method through:
$\Upsilon(r)=\ell^2[e_1\sqrt{R/r}+e_2+R^{-2}]$ with $e_1=e^{-(c/\sigma)
\sqrt\ell(1+o(1))}$, $e_2=e^{-(c/(4\sigma))\sqrt\ell(1+o(1))}$, so
$\sqrt r\,\Upsilon(r)=\ell^2[\sqrt R\,e_1+\sqrt r\,e_2+\sqrt r\,R^{-2}]$
using the *exact identity* $\sqrt r\cdot\sqrt{R/r}=\sqrt R$ (true for every
$r$, not merely a bound); bounding the remaining two terms by $\sqrt r\le
\sqrt R$ gives $\sup_r\sqrt r\,\Upsilon(r)\ll\ell^2\sqrt R(e_1+e_2)+\ell^2
R^{-3/2}$. Squaring: $(e_1+e_2)^2$ is dominated by $e_2^2=e^{-(c/(2\sigma))
\sqrt\ell(1+o(1))}$ (since $c/(4\sigma)<c/\sigma$, $e_2$ decays slower than
$e_1$), so the whole first-order contribution of $\Upsilon$ is $\ll
Re^{-(c/(2\sigma))\sqrt\ell(1+o(1))}$, the very term already listed second
in (6); the $e_1^2$ piece it contains is $Re^{-(2c/\sigma)\sqrt\ell(1+o(1))}$
(coefficient $R^1$, not $R^2$), and it is in any case smaller than the
$e_2^2$ term and does not need to be listed separately. So the corrected
squared bound has **no separate $R^2e^{-(2c/\sigma)\sqrt\ell}$ term**; at
most a redundant $Re^{-(2c/\sigma)\sqrt\ell}$ could be written, itself
dominated by the adjacent $Re^{-(c/(2\sigma))\sqrt\ell}$ term.

I verified symbolically that this does not change the theorem. With the
term corrected to $R^1$ (the largest defensible reading), its exponent at
$\sigma=2c_0$ becomes $c/c_0-2c_0$ (condition $c_0^2\le c/4$ for it to be
$\ge2c_0$), weaker than even the document's own (already non-binding, as
shown above) $c_0^2\le c/6$; either way this term's condition is implied by
the already-present, strictly stronger $c_0^2\le c/16$ from the adjacent
term. The printed $R^2$ version is a valid, non-tight, upper bound on the
correct $R^1$ term (since $R^2\ge R^1$ for $R\ge1$), so equation (7)'s
inequality remains true as stated; only the specific derivation quoted for
this one bracketed term is unsound as a matter of arithmetic, and it
affects nothing downstream: not the boxed (S$'''$), not the constant
$2c_0$, and not the content of (H'') as actually used. This is the same
kind of error as the one `MAJOR_ARC_EXPLICIT_REVIEW.md` found and fixed in
that document's model term, except that here the fix does not change any
displayed inequality, only its justification, since the printed coefficient
is a valid over-estimate rather than an under-estimate. The corrected
statement is: *the term should read $R\,e^{-(2c/\sigma)\sqrt\ell(1+o(1))}$
(and is in fact subsumed by the adjacent $R\,e^{-(c/(2\sigma))\sqrt\ell
(1+o(1))}$ term and need not be listed), not $R^2e^{-(2c/\sigma)\sqrt\ell
(1+o(1))}$.* The same correction applies to the corresponding term in
`MAJOR_ARC_EXPLICIT.md` equation (6), where it is likewise non-binding
(the condition it induces, $c_0^2\le2c/3$, is weaker than that document's
own binding $c_0^2\le c/4$ from the adjacent term).

I note for the record that `MAJOR_ARC_EXPLICIT_REVIEW.md` item (4) states
it "recomputed the six exponents from (6) as printed" and found they
"match the document's list exactly"; that check verified the arithmetic
from (6) to the verbal exponent list, not the squaring step from (5) to
(6), so it did not have occasion to catch this. I do not read this as a
miss on that check's part, since it did not claim to have re-derived (6)
from (5).

**The two-sided compatibility question.** I checked whether $\sigma=2c_0$
(the upper-bound construction) is compatible with $\kappa$ near $c_0$ in
the Proposition's window $c_0<\kappa<\min(\sqrt c,\sqrt b)-3\varepsilon$.
Under (H''), $c_0\le\min(\sqrt c/4,\sqrt b/4)$, so $c_0$ sits comfortably
below $\min(\sqrt c,\sqrt b)$ (by a factor of at least 4), and $c_0\le1/12
<1/3$, so for $\kappa$ slightly above $c_0$ and $\varepsilon$ small the
window's constraints ($\kappa<\min(\sqrt c,\sqrt b)-3\varepsilon$,
$\kappa+3\varepsilon<1/3$) are satisfied with room. I also checked that the
upper-bound construction does not implicitly assume the absence of such a
zero: in `MAJOR_ARC_EXPLICIT.md` section 3's case analysis, a real zero
$\tilde\beta=1-\kappa/\sqrt\ell$ with $\kappa>c_0$ of a character $\chi\ne
\chi_e$ falls into the "not TT-exceptional" case (since $\kappa>c_0$ means
$\tilde\beta<1-c_0/\sqrt\ell$), which is handled by the same $\Upsilon(r)$
machinery used throughout and gives a contribution $\ll N^3e^{-2\kappa
\sqrt\ell}(\cdot)\le N^3e^{-2c_0\sqrt\ell}(\cdot)$, i.e. the upper bound
remains valid (with room to spare) whether or not such a zero exists. The
two sides are therefore consistent, not merely juxtaposed.

**"Against the previous budgets."** I traced $(k,j,\gamma)$ through the
chain: `ENDPOINT_BOUND.md` (18) balances a major-arc term $N^3R^7
e^{-2\gamma\sqrt\ell}$ against $N^3R^{-1/6}$, matching $(7,1/6,\gamma)$;
`ARC_SPLIT_BUDGET.md` (12) balances $N^3R^2e^{-2\gamma\sqrt\ell}$ against
$N^3R^{-1}$, matching $(2,1,\gamma)$ (confirmed by that document's own
"Against the previous budget" paragraph, which states $k=7,j=1/6\to k=2,
j=1$); `MAJOR_ARC_EXPLICIT.md` (6)'s binding term is $Re^{-2c_0\sqrt\ell}$
(the exceptional-zero term, $k=1$, unaffected by the defect found above,
which concerns a different, non-binding bracket term), against the same
$R^{-1}$ minor-arc term inherited unchanged, matching $(1,1,c_0)$. The
sequence $(7,1/6,\gamma)\to(2,1,\gamma)\to(1,1,c_0)$ as printed is accurate.

## Summary

| Item | Verdict |
| --- | --- |
| (1) Dyadic reduction | confirmed |
| (2) Farey/Gallagher obstruction | confirmed |
| (3) Alternate dissection at $Q_2$ | confirmed |
| (4) The mechanism (section 2, 2.1) | confirmed |
| (5) The budget (7) | confirmed, one non-binding defect |

The one defect (section 3's $R^2e^{-(2c/\sigma)\sqrt\ell(1+o(1))}$ term,
inherited from `MAJOR_ARC_EXPLICIT.md` (6)) does not touch the boxed result
(S$'''$), the exponent constant $2c_0$, or the content of (H'') as actually
used to derive it, because the term's own induced condition is strictly
weaker than another condition already required by (H'') from an adjacent
term. Sections 1.2 and 2, named in the assignment as the most likely places
for a defect, held up under independent hand computation and two freshly
written numerical checks; the defect that did surface is in section 3, in
an equation imported from a different, previously-reviewed document, at a
step that document's own earlier review did not re-derive.
