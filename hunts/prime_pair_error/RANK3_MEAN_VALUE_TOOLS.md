# Route E: mean-value theorems for primes in progressions, and why they do
# not close rank 3's polynomial range either

This document investigates, as RANK3_SCOPE.md Section 2 asks, whether some
unconditional tool other than the three named in UPPER_BOUND.md -- the
Siegel-Walfisz major-arc approximation (17)/(SW), Vaughan's exponential-sum
estimate (V), and the additive large sieve (LS) used dyadically in
(24)-(27) -- could bound the mixed and fourth moments \(U_{(q)}\),
\(Z_{(q)}\) for denominators in the polynomial-in-\(N\) range
\(\lfloor L^B\rfloor<q\le R_0\) (\(L=\log N\), \(Q=\lfloor\sqrt N/3\rfloor\),
\(R_0=Q/L\)), where RANK3_SCOPE.md shows all three named tools give only a
trivial-order bound. RANK3_SCOPE.md's Section 3 names and prices four
routes (A-D), all built from the same three tools; this document looks at a
fifth: mean-value theorems for primes in arithmetic progressions --
Bombieri-Vinogradov and Barban-Davenport-Halberstam -- which rest on the
*multiplicative* (character) large sieve rather than the *additive*
(Farey-fraction) large sieve (LS) that (24)-(27) already uses. This is
"a different large-sieve weighting" in the sense RANK3_SCOPE.md's task asks
about: same underlying large-sieve mechanism, different indexing (by
Dirichlet character rather than by rational point), and, as shown below, a
genuinely different degeneration profile at small \(q\). The finding is
negative: this route names a real, previously-unnamed candidate, gets
further than routes A-D on the *shape* mismatch, but stops short of
\(N^{2+\epsilon}\) by exactly one unresolved factor of \(N\), which is
named precisely in Section 5, plus the separate transfer-step obstruction
RANK3_ROUTE_D.md Section 6 already identifies, which this route does not
touch either. \(Z_{(q)}\) fares worse: no candidate tool for it is found
here at all (Section 6).

Notation throughout is UPPER_BOUND.md's and RANK3_ROUTE_D.md's: \(F_N,K_N,
\Lambda,\psi,\mu,\phi\) as in UPPER_BOUND.md Section 1; \(P_{q,a},R_{q,a},
U_{(q)},Z_{(q)}\) as in UPPER_BOUND.md Section 6 and RANK3_SCOPE.md Section
1; \(\Delta(t;q,b)=\psi(t;q,b)-t/\phi(q)\) and \(T(q,b)\) as in
RANK3_ROUTE_D.md (D5), (D7), (D11). This document assumes RANK3_ROUTE_D.md
as already established and does not re-derive its identities.

## 1. The candidate: mean-value theorems, and why they are a different tool

Write \(\Delta(x;q,a)=\psi(x;q,a)-x/\phi(q)\) for the classical (not
\(K_N\)-convolved) prime-counting discrepancy in an arithmetic progression.
Two classical unconditional theorems bound this, on average over \(q\), far
beyond \(q\le L^B\):

**Bombieri-Vinogradov** (Bombieri 1965; A. I. Vinogradov 1965; see
Davenport, *Multiplicative Number Theory*, Chapter 28, or Montgomery and
Vaughan, *Multiplicative Number Theory I*, Chapter 17). For every \(A>0\)
there is \(B=B(A)\) such that
\[
 \sum_{q\le x^{1/2}(\log x)^{-B}}\ \max_{y\le x}\ \max_{(a,q)=1}
 \big|\psi(y;q,a)-y/\phi(q)\big|\ \ll_A\ x(\log x)^{-A}.
\tag{BV}
\]

**Barban-Davenport-Halberstam** (Barban 1966; Davenport and Halberstam
1966; sharp asymptotic form Montgomery 1970, and independently Hooley; see
Montgomery, *Topics in Multiplicative Number Theory*, Springer Lecture
Notes in Mathematics 227, Chapter 4, and Montgomery and Vaughan,
*Multiplicative Number Theory I*, Chapter 17 and its notes). Uniformly for
\(1\le Q\le x\),
\[
 D(x,Q):=\sum_{q\le Q}\ \sum_{\substack{a\bmod q\\(a,q)=1}}
 \big(\psi(x;q,a)-x/\phi(q)\big)^2\ \ll\ Qx\log x.
\tag{BDH}
\]

Neither is named in UPPER_BOUND.md or RESULTS.md. Both are proved via the
*multiplicative large sieve* -- the large sieve inequality for Dirichlet
characters, sum_{q\le Q}\sum_{\chi\bmod q}|\sum_n a_n\chi(n)|^2\le(N+Q^2)
\sum_n|a_n|^2 (Montgomery and Vaughan, *Multiplicative Number Theory I*,
Theorem 6.7, or Iwaniec and Kowalski, *Analytic Number Theory*, Theorem
7.13) -- which is dual, via Gauss sums, to the additive large sieve (LS)
UPPER_BOUND.md already cites, but is applied differently: (24)-(27) applies
(LS) to points \(a/q\) restricted to a single dyadic block \(R<q\le2R\),
one block at a time, then sums the blocks; (BV) and (BDH) apply the
character large sieve to *all* moduli \(q\le Q\) simultaneously, in one
inequality, then subtract off the low-\(q\) part.

**Why this changes the small-\(q\) degeneration.** RANK3_SCOPE.md Section 2
identifies exactly where (24)-(27) fails: the per-block estimate (25),
applied to the smallest block \(R=1\) (i.e. \(q=2\)), gives
\(U_{q=2}\ll w(Q)^2N^3L\), because the large-sieve ceiling \((N-1+4R^2)d_N\)
in (24) does not shrink with \(R\) -- for one modulus with few points, the
large sieve saves nothing over the trivial bound on that block alone. The
same objection applies, term for term, to a *dyadic-block* version of the
multiplicative large sieve: restricting the character large sieve to
\(R<q\le2R\) and dividing by \(\phi(q)\sim R\) to normalize (needed to
extract \(D(x,Q)\)'s per-\(q\) sum \(\sum_a(\Delta)^2=(1/\phi(q))\sum_\chi
|\psi(x,\chi)|^2+O(\cdots)\) from a bound on the unweighted \(\sum_\chi
|\psi(x,\chi)|^2\)) reproduces the same failure at \(R=O(1)\): a single
modulus contributes nothing to a large-sieve saving on its own. **(BV) and
(BDH), as actually proved, do not go through this block-by-block route at
all** -- they apply the character large sieve to the *entire* range
\(q\le Q\) in one inequality and are stated, and provably hold, uniformly
down to \(Q=O(1)\) (trivially, since restricting a valid inequality to a
sub-range of nonnegative terms cannot increase it). This is the substantive
difference from routes A-D: it is not a re-application of (LS) in a new
place, it is a use of the large-sieve mechanism that structurally avoids
the specific dyadic-block degeneration RANK3_SCOPE.md Section 2 diagnoses.
Section 2 below checks this on real data.

## 2. Bombieri-Vinogradov is the wrong strength, not the wrong range

\(R_0=Q/L\) with \(Q=\lfloor\sqrt N/3\rfloor\), so \(R_0\asymp\sqrt N/(3L)\).
(BV)'s range, \(x^{1/2}(\log x)^{-B}\) for \(B=B(A)\), comfortably contains
\(R_0\) for suitable fixed \(A\) (any fixed \(B\) exceeds a fixed power of
\(\log N\), and \(R_0\) is \(\sqrt N\) divided by *one* power of \(L\), so
for a large enough choice of \(A\) -- hence \(B\) -- (BV)'s range reaches
past \(R_0\)). **Range is not the obstruction here.** Strength is: (BV)
bounds a *sum* (not a sum of squares) of the max-over-\(y\), max-over-\(a\)
discrepancy, summed over up to \(x^{1/2-o(1)}\) moduli, by \(x(\log
x)^{-A}\) for every fixed \(A\) -- an arbitrary saving of a power of
\(\log x\), never a saving of any power of \(x\). This is exactly the
strength (SW) already has at \(q\le L^B\): both are "Siegel-Walfisz-type"
statements, and (BV) is provably no stronger in kind, only wider in
averaged range. Plugging (BV) into the identity in place of the
individual-\(q\) uniformity Route A needs would therefore, in the best
case, extend an (17)-style major-arc approximation across the *summed*
range \(q\le R_0\) at (SW)'s own strength: a bound of shape
\(O_H(N^3L^{-H'})\) for every fixed \(H\) (matching rank 1's own established
order, RANK3_SCOPE.md Section 1), not \(O_\epsilon(N^{2+\epsilon})\).
RANK3_SCOPE.md Section 4 already shows that rank 1's log-power bound is the
current bottleneck of (23), and that closing another door to the *same*
log-power strength does not move the total order. So even a fully worked
out application of (BV) to rank 3's mixed moment would reproduce, not beat,
an obstruction the text already has. This is a clean, low-cost conclusion
that needs no numerical check: it follows from (BV)'s own stated strength,
which this document cites rather than measures. (The Elliott-Halberstam
conjecture, extending (BV)'s range to \(Q\le x^{1-\epsilon}\), changes
nothing about this point -- it is conditional, not admissible here, and,
in any case, only widens the range, not the log-vs-power-saving character
of the bound.)

## 3. Barban-Davenport-Halberstam is the right shape and the right strength

(BDH) is a sum of *squares*, matching \(T(q,b)\)'s structure in
RANK3_ROUTE_D.md (D5) far better than (BV) does, and its unconditional
strength is genuinely power-type: \(D(x,Q)\ll Qx\log x\) against a trivial
per-term bound of \(4x^2\) (Chebyshev: \(|\psi(x;q,a)|,x/\phi(q)\le\psi(x)
\ll x\)) summed over \(\sum_{q\le Q}\phi(q)\asymp Q^2\) terms, i.e. a
trivial ceiling of order \(Q^2x^2\). (BDH)'s \(Qx\log x\) is smaller than
this trivial ceiling by a factor of order \(Qx/\log x\) -- a full power of
both \(Q\) and \(x\) saved, unconditionally, down to every \(Q\le x\)
including small \(Q\). This is the kind of saving rank 3 needs and (25)-
(26) cannot supply at small \(q\).

**Numerical check.** `rank3_bdh_probe.py` (results in
`results_rank3_bdh_probe.json`) measures
\(D(N,Q)=\sum_{q\le Q}\sum_{a\bmod q}^*(\psi(N;q,a)-N/\phi(q))^2\) directly
from the true von Mangoldt function (prime-power enumeration, no sampling),
two ways.

*Fixed \(Q=30\), \(N\) from \(2\times10^4\) to \(8\times10^5\).* \(D(N,Q)/N\)
stays in the narrow band \(10.8\) to \(13.7\) with no systematic trend
across a 40-fold range of \(N\); \(D(N,Q)/(N\log N)\) stays in \(0.94\) to
\(1.21\). This cleanly confirms the \(N\)-dependence of \(D(N,Q)\) is
linear in \(N\), matching (BDH)'s \(N\)-power exactly -- this is the power
that matters most for Section 5's scaling argument, and it is confirmed
directly rather than assumed.

*Fixed \(N=150000\), \(Q\) from \(10\) to \(500\).* \(D(N,Q)/(QN)\) rises
from \(0.08\) to \(2.25\) -- a 28-fold increase against a 50-fold increase
in \(Q\), i.e. faster than the \(\log(500)/\log(10)\approx2.7\)-fold rise a
pure \(Q\log Q\) shape would predict. This experiment, alone, cannot tell a
pre-asymptotic regime (a known feature of mean-value theorems: the
displayed leading term needs \(Q\) large enough relative to lower-order
terms before it dominates) from a genuinely steeper \(Q\)-dependence at
these particular finite parameters, and is reported as measured, not fit
to either shape; \(Q=500\) is close to \(\sqrt N=387\), where the
large-sieve ceiling \((N+Q^2)\) itself crosses from \(N\)-dominated to
\(Q^2\)-dominated, which is a plausible source of the acceleration seen
here and is a reason for caution about extrapolating this \(Q\)-range
number to \(Q=R_0\ll\sqrt N\). What both sub-experiments confirm robustly:
\(D(N,Q)\) is seven to eight orders of magnitude below the trivial
ceiling \(Q^2N^2\) at every checkpoint (`ratio_measured_over_trivial` in
the JSON, ranging only from \(9.3\times10^{-8}\) down to
\(3.0\times10^{-8}\) across the whole 50-fold range of \(Q\) -- itself
varying by less than a factor of \(3\), meaning the *ratio* to the trivial
\(Q^2N^2\) bound does not run away either), i.e. a genuine, large, measurable saving is present
even at the small-to-moderate \(q\) where (25)-(26) gives none.

Section 5 below uses only the classical cited form (BDH), \(D(x,Q)\ll Qx
\log x\), for the scaling argument, and only cross-checks its \(N\)-power
against the clean measurement above; it does not lean on this document's
own uncertain read of the \(Q\)-power.

## 4. Where (BDH) would have to plug in, and why (D11)'s transfer term is untouched

RANK3_ROUTE_D.md (D11) already reduces \(U_{(q)}\) (up to the \(R^{(2)}\)
correction, controlled there) to
\[
 U_{(q)}\ \le\ 2\mu(q)^2\sum_{b\bmod q}^*T(q,b)\ +\ O\!\Big(\frac{q^2N^3L}
 {Q^2\phi(q)}\Big),
\]
with \(T(q,b)=\sum_{t=1}^N\Delta(t;q,b)^2+\sum_{t=1}^{N-1}
[\Delta(N;q,b)-\Delta(t;q,b)]^2\) (RANK3_ROUTE_D.md (D5)). (BDH) is a
candidate for the first term. It is **not** a candidate for the second: the
transfer term is already shown, in RANK3_ROUTE_D.md Section 6, to cost
\(O(N^3)\) once summed over \(2\le q\le R_0\) *regardless* of how well
\(\sum_b^*T(q,b)\) is controlled -- "the obstruction is the transfer step
itself, not the main term." Nothing in this document changes that; a
bound on \(T(q,b)\) from (BDH) would still need RANK3_ROUTE_D.md Section
6's own missing ingredient (a dyadic, non-crude transfer argument) before
it could help \(U_{(q)}\) at all. Section 5 below therefore prices only the
first term, on the understanding -- already on record in
RANK3_ROUTE_D.md -- that a second, independent obstruction remains even if
it fully succeeds.

## 5. Pricing (BDH) against the first term: short by exactly one factor of \(N\)

(BDH)'s object, \(D(t,Q)=\sum_{q\le Q}\sum_b^*\Delta(t;q,b)^2\), is a
single-endpoint (in \(t\)) quantity. \(T(q,b)\), summed over \(q,b\), needs
\(\sum_{q\le Q}\sum_b^*\sum_{t=1}^N\Delta(t;q,b)^2\) -- the *same* quantity
summed again over every \(t\) from \(1\) to \(N\), not evaluated once at
\(t=N\). (BDH) is proved uniformly in the endpoint (Section 1's citations
state it for \(x\le\) the stated range, and the standard proof, via the
character large sieve applied to \(\Lambda(n)\mathbf 1_{n\le t}\), holds at
every integer endpoint \(t\) on the same terms as at \(N\)), so it may be
applied separately at each \(t\le N\):
\[
 D(t,Q)\ll Qt\log t\le QN\log N\qquad\text{for every }1\le t\le N,
\]
and summing this bound over the \(N\) values of \(t\) -- the crude
combination this document uses to bridge the endpoint-vs-full-sum gap,
clearly separate from anything (BDH) itself asserts -- gives
\[
 \sum_{t=1}^N D(t,Q)\ \ll\ QN^2\log N,\qquad\text{hence}\qquad
 \sum_{q\le Q}\sum_b^*T(q,b)\ \ll\ QN^2\log N
\tag{E1}
\]
(the second summand of \(T(q,b)\) is controlled the same way, by
\((x-y)^2\le2x^2+2y^2\) applied to \([\Delta(N;q,b)-\Delta(t;q,b)]^2\),
without changing the order). At \(Q=R_0=\lfloor\sqrt N/3\rfloor/L\asymp
\sqrt N/(3L)\), and using \(2\mu(q)^2=O(1)\) from (D11) (the *proved*,
cancellation-free weight RANK3_ROUTE_D.md Section 5 establishes on
\(\sum_b^*T(q,b)\); the smaller, unproven \(\mu(q)^2/\phi(q)\) or
\(\mu(q)^2/\phi(q)^2\) weights that Section 5 discusses would only improve
this, not worsen it, so (E1) is used with its own weight for an upper
bound):
\[
 \sum_{L^B<q\le R_0}U_{(q)}^{(\text{first term})}\ \ll\ R_0N^2\log N
 \ \asymp\ \frac{\sqrt N}{3L}\cdot N^2\cdot L\ =\ \frac{N^{5/2}}3.
\tag{E2}
\]
The \(\log N\) from (BDH) and the \(1/L\) from \(R_0\)'s own definition
exactly cancel (\(L=\log N\)), leaving a bare \(N^{5/2}\) with no residual
log saving at all in this crude combination -- a bookkeeping accident of
how coarsely (E1) sums over \(t\), not a claim that this route reaches
\(N^{5/2}\) *without* logs more precisely than CHHL's own conditional
statement does; this document does not track log powers past the point
where they stop affecting the conclusion below, and (E2)'s log-free
appearance should be read as "this crude argument's logs happen to
cancel," not as a sharper log power than a more careful argument would
give.

**The comparison that matters.** \(N^{5/2}\) is precisely the order of
CHHL's own conditional benchmark, \(E(N)\ll N^{5/2}L^c\) **under GRH for
Dirichlet \(L\)-functions** (UPPER_BOUND.md Section 1, item 1) -- the same
power of \(N\), reached here through an entirely different, unconditional
route (the character large sieve, applied optimally and without any
individual-\(q\) uniformity assumption), landing at exactly the exponent
that assuming GRH already gives. That is a meaningful, if negative,
finding: **the strongest unconditional averaged second-moment tool
available for this identity does not beat the GRH-conditional order it is
trying to reach unconditionally; it matches it.** The gap to the actual
target, \(N^{2+\epsilon}\), is one full power of \(N^{1/2}\) -- exactly the
power lost in (E1)'s crude step of summing \(N\) copies of the
single-endpoint bound. Closing that gap would need an *integrated*
mean-value theorem -- a genuine bound on \(\sum_{q\le Q}\sum_b^*
\sum_{t\le N}\Delta(t;q,b)^2\) of order \(QN^{1+\epsilon}\), not the
\(QN^2\log N\) that summing the endpoint bound over \(t\) naively gives --
and this document does not find such a theorem named or provable from
(BV)/(BDH) as customarily stated. Whether one exists in the literature
under some other name (a "mean square of \(\psi(t;q,a)-t/\phi(q)\)
integrated over \(t\)," in the spirit of the Barban-Vehov / Motohashi
weighted sieve literature, or a large-sieve density theorem for zeros of
\(L(s,\chi)\) averaged over \(\chi\) and over height simultaneously) is
exactly the open question this document surfaces and does not resolve.

## 6. \(Z_{(q)}\): no candidate found

(BDH) is a *second*-moment tool. \(Z_{(q)}=\sum_a^*\int_{\rm arc}|R_{q,a}|^4\)
is a fourth moment, and RANK3_ROUTE_D.md Section 7 already shows it does
not even reduce to \(\Delta(t;q,b)\)-type quantities in the first place --
the identity's quadruple additive convolution \(Y(b_1,b_2,b_3,b_4)\) has no
telescoping structure, a *structural* obstruction independent of what
estimate is available for \(\Delta\). A fourth-moment analogue of (BDH) --
bounding \(\sum_{q\le Q}\sum_a^*|\psi(x;q,a)-x/\phi(q)|^4\), say -- is not
part of the two standard theorems cited in Section 1, and this document did
not find, or attempt to derive, such a statement with any confidence; it is
named here as a missing ingredient, not supplied. Independently, even
granting some fourth-moment mean-value bound, RANK3_ROUTE_D.md Section 7's
second point stands unaffected: \(Z_{(q)}\)'s integrand carries no
\(|P_{q,a}|^2\) factor, so there is no arc-transfer argument of the kind
Section 4 uses for \(U_{(q)}\), and a full-circle mean-value bound would
not, on its own, bound the arc-restricted \(Z_{(q)}\). So this document
finds **no** candidate tool for \(Z_{(q)}\) over the polynomial range, not
even one that falls short the way Section 5's does for \(U_{(q)}\).

## 7. A different splitting of the arcs by denominator

RANK3_SCOPE.md's task also asks about a different splitting of the arcs by
denominator (e.g., by smoothness/friability of \(q\), by \(\omega(q)\), or
by largest prime factor) rather than a different estimate. Section 1 above
is the reason this does not obviously help: (BV) and (BDH) are *already*
whole-range statements over \(q\le Q\) that do not degrade based on how the
range is internally partitioned -- restricting either theorem to any
measurable sub-collection of \(q\in(L^B,R_0]\) (friable \(q\), \(q\) with
few prime factors, or any other structured subset) only removes
nonnegative terms from the same valid inequality, so it cannot produce a
bound better in *order* than applying the theorem to the whole range at
once, which Section 5 already prices. A finer split could in principle
help if it exploited some extra structure specific to a sub-class of \(q\)
(for instance, if \(\Delta(t;q,b)\) were provably smaller, individually,
for smooth \(q\) than the general uniform-in-\(q\) case) -- but that would
be a return to Route A's individual-modulus uniformity question
(RANK3_SCOPE.md Section 3), not a new averaged tool, and RANK3_SCOPE.md
already shows no unconditional source for that beyond \(q\le L^B\). This
document does not find that any denominator-splitting changes Section 5's
conclusion.

## 8. Where this leaves rank 3's polynomial range

A genuinely different, previously unnamed unconditional tool exists for
this range -- the multiplicative large sieve and its consequences (BV),
(BDH) -- and it behaves qualitatively better than the additive-large-sieve
dyadic-block argument (24)-(27) at small \(q\), both by citation (Section
1) and by direct measurement (Section 3, `results_rank3_bdh_probe.json`).
But:

- (BV) is the wrong *strength* (log-saving only, matching rank 1's own
  bottleneck, not a power-of-\(N\) saving) -- Section 2, no numerical check
  needed.
- (BDH) is the right *shape and strength* for the piece of \(U_{(q)}\) it
  could reach, but only reaches \(N^{5/2}\) order once bridged (by the one
  crude, clearly-labeled step in Section 5) from a single-endpoint theorem
  to the full-\(t\)-sum quantity \(T(q,b)\) the identity actually needs --
  exactly matching, not beating, CHHL's GRH-conditional benchmark, and
  falling short of \(N^{2+\epsilon}\) by one power of \(N^{1/2}\).
- Even if that gap were closed, RANK3_ROUTE_D.md Section 6's transfer-step
  obstruction -- an independent \(O(N^3)\) cost, untouched by any bound on
  \(T(q,b)\) -- would remain for \(U_{(q)}\).
- No candidate at all is found here for \(Z_{(q)}\) (Section 6).
- Splitting the arcs by denominator differently does not change any of
  this (Section 7).

What would be needed, stated as precisely as this document can state it:
(i) an *integrated-in-\(t\)*, summed-in-\(q\) mean-value theorem for
\(\sum_{q\le Q}\sum_b^*\sum_{t\le N}\Delta(t;q,b)^2\) at order
\(QN^{1+\epsilon}\), not the \(QN^2\log N\) the customary (BDH) gives once
naively summed over \(t\); (ii) independently, the non-crude arc-transfer
argument RANK3_ROUTE_D.md Section 6 already names as missing; (iii) any
fourth-moment mean-value analogue of (BDH) for \(Z_{(q)}\), or some other
route to it entirely, given the structural (not just strength) obstruction
RANK3_ROUTE_D.md Section 7 identifies. None of the three is supplied here.
This is consistent with, and adds one further specific candidate and its
specific failure mode to, RANK3_SCOPE.md Section 3's conclusion that no
route among those it names is costed to completion by the source
documents.

This document is citation of standard theorems (Section 1), a scaling
argument built on them with one clearly labeled crude step (Section 5),
and a direct numerical measurement of the ingredient second moment
(Section 3); it assumes and establishes nothing about zeros of
\(L\)-functions or the Riemann Hypothesis.
