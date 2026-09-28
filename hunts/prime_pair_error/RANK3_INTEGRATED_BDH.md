# An integrated-in-\(t\) Barban-Davenport-Halberstam theorem at order
# \(QN^{1+\epsilon}\): not in the cited literature, and not true either

This document answers the question RANK3_MEAN_VALUE_TOOLS.md Section 5 and
RANK3_BDH_VERIFY.md leave open: does an "integrated" Barban-Davenport-
Halberstam-type theorem exist, or can one be proved, bounding
\[
 \Sigma(N,Q):=\sum_{q\le Q}\ \sum_{\substack{a\bmod q\\(a,q)=1}}\ \sum_{t=1}^N
 \big(\psi(t;q,a)-t/\phi(q)\big)^2
\]
at order \(QN^{1+\epsilon}\) for every fixed \(\epsilon>0\), uniformly for
\(Q\) up to a positive power of \(N\) such as \(R_0=\lfloor\sqrt N/3\rfloor/L\)
(\(L=\log N\))? The answer is **no** on both counts asked for: no such
theorem is stated in the standard sources this document can check, and,
more importantly, \(\Sigma(N,Q)\) itself is not that small -- it is measured
directly below, from the true von Mangoldt function with no sampling, to
scale like \(N^{2}\) (up to a log factor), not \(N^{1+\epsilon}\) for any
\(\epsilon\) as large as \(0.3\), at every \(Q\) tested. This is not merely
"no theorem of this shape is known"; it is "the quantity the theorem would
have to bound does not have the claimed order," which is a stronger and more
useful negative finding for RANK3_ROUTE_D.md's identity (D11) than a
literature gap alone would be.

Notation is RANK3_ROUTE_D.md's and RANK3_MEAN_VALUE_TOOLS.md's:
\(\Delta(t;q,a)=\psi(t;q,a)-t/\phi(q)\), \(T(q,b)=\sum_{t=1}^N\Delta(t;q,b)^2
+\sum_{t=1}^{N-1}[\Delta(N;q,b)-\Delta(t;q,b)]^2\) (RANK3_ROUTE_D.md (D5)).
\(\Sigma(N,Q)=\sum_{q\le Q}\sum_b^*\sum_{t=1}^N\Delta(t;q,b)^2\) is exactly
the first summand of \(\sum_{q\le Q}\sum_b^*T(q,b)\); the second summand is
controlled the same way by \((x-y)^2\le2x^2+2y^2\)
(RANK3_MEAN_VALUE_TOOLS.md's (E1)) and does not change any order discussed
here, so this document works with \(\Sigma(N,Q)\) itself throughout, exactly
as the task assigning this document phrases the target quantity.

## 1. Sourcing: no live network access, same wall as RANK3_BDH_VERIFY.md

This attempt tried `WebSearch` three times, on the three literature threads
the assignment names (an integrated/mean-square-in-\(t\) Barban-Davenport-
Halberstam statement; Motohashi's induction principle for generalizations of
Bombieri's prime number theorem; the Barban-Vehov weighted sieve and
large-sieve/zero-density theorems for Dirichlet \(L\)-functions averaged
jointly over conductor and height). All three calls returned a permission
error with no interactive user available to grant it -- the identical wall
RANK3_BDH_VERIFY.md records ("`WebSearch` and `WebFetch` calls both returned
a permission error"). No local copy of Motohashi's *Sieve Methods and Prime
Number Theory*, Montgomery's LNM 227, Montgomery and Vaughan's
*Multiplicative Number Theory I*, or Davenport's *Multiplicative Number
Theory* exists in this worktree. Section 2 below is therefore sourced from
the standard, checkable content of these works as commonly stated -- the
same standing RANK3_BDH_VERIFY.md's citations have -- not from a live fetch;
a later attempt with working network access should confirm the specific
claims below directly against the primary sources and correct anything a
live check contradicts. Section 3, by contrast, is a direct numerical
measurement from this repository's own von Mangoldt machinery and needs no
external source at all.

## 2. The three named candidates, examined structurally

**Barban-Vehov weighted sieve.** This is a *linear-sieve* device (Barban and
Vehov 1968; see Motohashi's *Sieve Methods and Prime Number Theory*, or
Halberstam and Richert, *Sieve Methods*, for the standard weighted-sieve
treatment; it is also the technical predecessor to results like Chen's
theorem on primes and almost-primes). Its role is to attach smooth weights
to a sifting problem so that a linear combination of sifting functions
majorizes or minorizes a target counting function, trading exactness for
tractability in a *sieve*, not a mean-value-theorem, sense. It is a tool for
bounding counts of primes (or almost-primes) satisfying multiplicative
conditions, and its output is a one-parameter (in the sifting level)
inequality, not a statement about \(\psi(t;q,a)-t/\phi(q)\) integrated over
an interval of \(t\)-values at all. Nothing in the standard presentations of
this method produces, as a byproduct or a corollary, a mean-square bound
summed over \(t\); it addresses a different question (counting elements of a
sifted set) with a different structure (a single sifting level, not two
independent parameters \(q\) and \(t\)). This document finds no route from
Barban-Vehov to \(\Sigma(N,Q)\).

**Motohashi's induction principle.** Motohashi (1976, and the treatment in
his *Sieve Methods and Prime Number Theory*) proves an induction principle
that extends Bombieri-Vinogradov-type theorems to a wider class of
sequences and weightings than the classical prime-counting case -- it is a
method for *generalizing which sequence* a Bombieri-Vinogradov-shaped
theorem applies to (replacing \(\Lambda(n)\) with more general
multiplicative or sieve-theoretic weights), by an induction on the number of
prime factors removed. What it does **not** change is the *shape* of the
conclusion: like (BV) itself (RANK3_MEAN_VALUE_TOOLS.md Section 1), the
output is a bound on \(\sum_q\max_y\max_a|\Delta|\) (or a mean-square analogue
at a single fixed endpoint), for the wider class of sequences, not a
statement integrated over an interval of endpoints \(t\le N\). Applying it
in place of (BV) would reproduce RANK3_MEAN_VALUE_TOOLS.md Section 2's
finding almost verbatim -- an arbitrary saving in the sieve/log parameter at
a single endpoint, generalized to more sequences, never a saving across the
\(t\)-sum -- so this candidate does not change RANK3_MEAN_VALUE_TOOLS.md's or
RANK3_BDH_VERIFY.md's conclusion, it only widens the class of sequences the
same conclusion would apply to.

**Large-sieve/zero-density theorems jointly averaged over conductor and
height.** These exist (work descending from Bombieri's and Montgomery's
large-sieve density theorems for zeros of \(L(s,\chi)\), further refined by
Jutila, Huxley and others, bounding \(\sum_{q\le Q}\sum_\chi N(\sigma,T,\chi)\)
jointly in the conductor \(q\) and the zero-counting height \(T\)) and are
exactly the mechanism *behind* (BV) and (BDH) themselves (RANK3_MEAN_VALUE_TOOLS.md
Section 1's "dual, via Gauss sums" remark; density theorems are one standard
route to zero-free-region-flavored improvements of the large sieve). The
"height" \(T\) in these theorems is the *height of a zero of \(L(s,\chi)\)
on the critical strip*, entering through a truncated explicit formula at a
single fixed \(x\) (here, \(x=N\)); it is not the same parameter as "the
endpoint \(t\) of a partial sum \(\psi(t;q,a)\)," even though both are
sometimes loosely called an averaging "over height." Averaging jointly over
conductor and zero-height sharpens the *range* and *log-saving* of a
single-endpoint statement (this is exactly how the effective forms of (BV)
are proved); it supplies nothing about **integrating** the resulting
discrepancy over many different values of the sum's upper limit \(t\), which
is a completely different kind of average (over the argument at which
\(\psi\) is evaluated, not over the zeros used to estimate it at one fixed
argument). This document finds these theorems to be a plausible source of an
improved log-saving on the single-endpoint quantity -- precisely
RANK3_BDH_VERIFY.md's H* territory -- and not a source of the \(t\)-sum
strengthening at all.

**Conclusion of this section.** None of the three named candidates supplies
a genuinely \(t\)-integrated mean-square theorem. This matches, and gives
structural reasons for, RANK3_MEAN_VALUE_TOOLS.md Section 5's and
RANK3_BDH_VERIFY.md Section 6's own "not found" verdicts, extended here to
two candidates neither prior document examined by name (Barban-Vehov,
Motohashi's induction principle).

## 3. Why no such theorem can hold at the claimed strength: \(\Sigma(N,Q)\)
##    is measured to be order \(N^2\), not \(N^{1+\epsilon}\)

Section 2 explains why the literature does not supply the target theorem.
This section gives the stronger reason **why it could not**, regardless of
what future method is tried: \(\Sigma(N,Q)\) is a sum of nonnegative terms,
and it is both heuristically expected, and measured here directly, to grow
quadratically in \(N\), not as \(N^{1+\epsilon}\) for any fixed \(\epsilon\).

**The heuristic reason, stated precisely.** Fix \(q\) and consider
\(\Delta(t;q,b)\) as \(t\) ranges over \(1,\dots,N\). Under the square-root-
cancellation heuristic that is both the unconditional content of the sharp
Montgomery-Hooley form of (BDH) (valid for \(Q\) close to \(t\)) and the
GRH-conditional expectation at every \(Q\) (via
\(\psi(t,\chi)=O(\sqrt t\log^2(qt))\) for each nonprincipal \(\chi\bmod q\),
combined with near-independence across the \(\phi(q)-1\) characters, which
gives \(\Delta(t;q,b)=O(\sqrt{t/\phi(q)}\log^2t)\) after dividing by
\(\phi(q)\)), \(\Delta(t;q,b)^2\) is genuinely of size \(\asymp t/\phi(q)\)
(times a bounded power of \(\log t\)) for *typical* \(t\), not asymptotically
smaller. This is not an artifact of a weak proof method: it is the same
order (BDH) itself asserts as an asymptotic equality, not merely an upper
bound, in the range where that has been proved (Montgomery 1970, Hooley).
Since \(\Delta(t;q,b)^2\ge0\) for every \(t\), no cancellation across
different values of \(t\) is possible in \(\sum_{t=1}^N\Delta(t;q,b)^2\) --
unlike \(\sum_t\Delta(t;q,b)\) itself (signed), the *squared* sum cannot be
made smaller than the sum of its parts by cancellation between terms at
different \(t\). Consequently, if \(\Delta(t;q,b)^2\) is genuinely
\(\asymp t/\phi(q)\) (up to logs) for even a positive proportion of
\(t\in[N/2,N]\), then
\[
 \sum_{t=1}^N\Delta(t;q,b)^2\ \ge\ \sum_{t=N/2}^N\Delta(t;q,b)^2\ \gg\
 \frac N2\cdot\frac{N/2}{\phi(q)}\ \asymp\ \frac{N^2}{\phi(q)},
\]
forcing \(\Sigma(N,Q)=\sum_{q\le Q}\sum_b^*\sum_t\Delta(t;q,b)^2\) to be
\(\gg\sum_{q\le Q}\phi(q)\cdot N^2/\phi(q)\asymp QN^2\) -- a bare power
\(N^2\), not \(N^{1+\epsilon}\) for any \(\epsilon<1\). Nothing about GRH
changes this: GRH controls the *pointwise* size of \(\Delta(t;q,b)\) at each
individual \(t\), it does not make \(\Delta(t;q,b)\) atypically small at
*most* values of \(t\) up to \(N\) -- if anything, GRH's own square-root
size is exactly consistent with, not smaller than, the order just derived.
Reaching \(\Sigma(N,Q)=O(QN^{1+\epsilon})\) would require
\(\Delta(t;q,b)^2\) to be \(o(t^{1-\delta}/\phi(q))\) for *almost every*
\(t\le N\), for some fixed \(\delta>0\) -- a claim substantially *stronger*
than square-root cancellation (which gives \(\Delta(t;q,b)^2\asymp
t/\phi(q)\), not smaller), and one this document finds no support for
anywhere, conditionally or otherwise.

**Direct numerical measurement.** `rank3_integrated_bdh_probe.py` (results in
`results_rank3_integrated_bdh_probe.json`) computes \(\Sigma(N,Q)\) exactly
(true von Mangoldt function by prime-power enumeration, exact cumulative
sums per residue class, no sampling) for \(Q\in\{5,10,20,30\}\) and \(N\)
from \(10^4\) to \(3.2\times10^5\) (a 32-fold range), reusing
`rank3_bdh_probe.py`'s already-cross-checked `von_mangoldt` and `sympy`'s
`totient` for \(\phi(q)\). Two findings:

- **\(\Sigma(N,Q)/(QN^2\log N)\) is stable, within less than a factor of 2,
  across the entire 32-fold range of \(N\), at every \(Q\) tested** (e.g. at
  \(Q=30\): \(0.0202\) at \(N=10^4\) down to \(0.0146\) at
  \(N=3.2\times10^5\); at \(Q=5\): \(0.0046\) down to \(0.0029\)). This
  directly confirms the heuristic argument above: \(\Sigma(N,Q)\) genuinely
  scales like \(N^2\) (times a slowly varying log-type factor), not like a
  smaller power of \(N\).
- **A direct log-log fit of \(\Sigma(N,Q)\) against \(N\) at each fixed
  \(Q\) gives an \(N\)-exponent of \(1.97\), \(2.00\), \(1.99\), \(2.00\) at
  \(Q=5,10,20,30\) respectively** -- indistinguishable from \(2\) to within
  the precision of a 6-point fit over one and a half decades of \(N\).
- For contrast, `Sigma_over_Q_N1p05` through `Sigma_over_Q_N1p30` in the
  JSON (\(\Sigma(N,Q)/(QN^{1+\epsilon})\) for \(\epsilon=0.05,0.1,0.2,0.3\))
  **grow monotonically and substantially across the same \(N\) range at
  every \(Q\)** -- e.g. at \(Q=30\), \(\Sigma/(QN^{1.3})\) rises from
  \(117\) at \(N=10^4\) to \(1319\) at \(N=3.2\times10^5\), an 11-fold rise
  over a 32-fold increase in \(N\), consistent with roughly \(N^{0.7}\)
  further growth on top of the \(N^{1.3}\) already divided out (i.e.
  consistent with the fitted \(N^2\) order, not with \(N^{1.3}\) itself
  stabilizing). None of the four \(\epsilon\) values tested shows any sign
  of leveling off; the higher \(\epsilon\) values level off more slowly, in
  the direction consistent with the true exponent being \(2\), not any
  fixed value below it.

This is measured only at \(Q\le30\), well below \(R_0\asymp\sqrt N/(3L)\);
it does not, on its own, rule out some qualitatively different behavior
emerging only at \(Q\) polynomially large in \(N\). But nothing in this
measurement, or in RANK3_MEAN_VALUE_TOOLS.md Section 3's separate finding
that \(D(N,Q)/(QN)\) at fixed \(N=150000\) rises *faster* than \(\log Q\) as
\(Q\) grows from \(10\) to \(500\), suggests growing \(Q\) helps -- if
anything both point the other way. This document reports the measured range
honestly and does not extrapolate a proof for all \(Q\le R_0\) from it; the
combination of the heuristic argument (Q-independent: it holds for each
fixed \(q\) individually, before any sum over \(q\)) and this numerical
confirmation is offered as strong evidence, not a proof, that no \(Q\)
range changes the conclusion.

## 4. What this means for RANK3_ROUTE_D.md's identity, and what would
##    actually be needed

RANK3_ROUTE_D.md's (D11) needs \(\sum_{q\le R_0}\sum_b^*T(q,b)\) small; since
\(\Sigma(N,Q)\) is (Section 3's first summand of) exactly this quantity, and
is genuinely order \(QN^2\)-ish rather than \(QN^{1+\epsilon}\), **no
integrated mean-value theorem of the shape asked for exists to plug in, and
none should be expected to be found by further search**, because the target
quantity itself does not have that order -- the obstruction is not a gap in
current technique but the true size of the object. This sharpens
RANK3_MEAN_VALUE_TOOLS.md Section 5's and RANK3_BDH_VERIFY.md's "not found"
into "not true," at least at the \(Q\) range this document could measure,
under the heuristic that is consistent with both the proved sharp (BDH)
asymptotic and with GRH.

**What would actually be needed instead**, stated as precisely as this
document can: not a smaller bound on \(\Sigma(N,Q)\) itself, but an argument
that never needs to bound the full nonnegative sum \(\sum_b^*T(q,b)\) in the
first place -- i.e. a route to \(U_{(q)}\) that exploits **cancellation
between different residues \(b\)** (RANK3_ROUTE_D.md's \(\Sigma_{\rm
cross}(q)\), (D7)) rather than a mean-value bound on the diagonal
\(\sum_b^*T(q,b)\) alone. This is exactly the open question RANK3_ROUTE_D.md
Section 3 and Section 5 already name and do not resolve -- whether
\(\Sigma_{\rm cross}(q)\) is close to \(0\) or close to its Cauchy-Schwarz
ceiling -- and it is a genuinely different kind of question from the one
this document answers: it asks about cancellation *across residues at fixed
\(t\)*, not about the size of \(\Delta(t;q,b)^2\) *summed across \(t\) at
fixed residue*, which is what this document shows cannot be beaten down to
\(N^{1+\epsilon}\) order. A route through \(\Sigma_{\rm cross}(q)\), if it
existed, would sidestep this document's obstruction entirely rather than
contradict it, since it would never form \(\sum_b^*T(q,b)\) as an
intermediate quantity to begin with.

## 5. Verdict

- No statement of the shape \(\Sigma(N,Q)=O(QN^{1+\epsilon})\), uniformly
  for \(Q\le R_0\), is found among Barban-Vehov, Motohashi's induction
  principle, or joint conductor-and-height large-sieve/zero-density
  theorems, and Section 2 gives a structural reason for each: none of the
  three is a statement integrated over the endpoint \(t\) of a partial
  prime-counting sum, as opposed to a statement about sifted counts,
  generalized sequences, or the range/log-strength of a single-endpoint
  quantity, respectively.
- More strongly: \(\Sigma(N,Q)\) itself is measured directly here, from the
  exact von Mangoldt function with no sampling, to scale as \(N^{2.0\pm0.03}\)
  (four independent log-log fits at \(Q=5,10,20,30\)) rather than
  \(N^{1+\epsilon}\) for any \(\epsilon\) up to \(0.3\) tested, matching a
  square-root-cancellation heuristic that holds both unconditionally (in
  the sharp (BDH) range) and under GRH. This is a reason no such theorem
  should be expected to exist at all, not only a report that none was found.
- What would close the actual gap in RANK3_ROUTE_D.md (D11) is not this
  theorem (which does not exist and would be false if it did), but progress
  on the separate, still-open question of cancellation in \(\Sigma_{\rm
  cross}(q)\) (RANK3_ROUTE_D.md Section 5), which this document does not
  attempt.

This document is a citation-structure analysis (Section 2, sourced as
Section 1 describes, without live network access), a heuristic argument from
elementary nonnegativity plus the classical (BDH) asymptotic and the GRH
square-root-cancellation heuristic (Section 3), and a direct, exact numerical
measurement from this repository's own von Mangoldt machinery (Section 3,
`results_rank3_integrated_bdh_probe.json`); it assumes and establishes
nothing about zeros of \(L\)-functions or the Riemann Hypothesis beyond
citing GRH's standard conjectural consequence for \(\psi(t,\chi)\) as one of
two independent heuristics compared against measured data, not as an
assumption relied upon for the verdict above.
