# Checking RANK3_POLYRANGE.md Section 5's t-integrated, \(\phi(q)^{-2}\)-weighted
# Barban-Davenport-Halberstam claim against the literature -- and against
# elementary consequences of the classical theorem this hunt already cites

This document answers the task assigned to it: search the unconditional
analytic number theory literature for a "t-integrated" analogue of the
Barban-Davenport-Halberstam (BDH) / Bombieri-Vinogradov (BV) theorems, in the
exact shape and \(q\)-range `RANK3_POLYRANGE.md` Section 5 needs, or report
precisely that none is found. **This attempt's worktree does not contain
`RANK3_POLYRANGE.md`** -- the same situation `RANK3_ROUTE_D.md` §5 already
records for its own assignment -- so the statement below is taken verbatim
from this document's own task description, not read from that file directly;
whoever next holds both should reconcile them.

## 1. The statement, restated exactly

For \(L=\log N\), \(Q=\lfloor\sqrt N/3\rfloor\), \(R_0=Q/L\), and any fixed
\(B>0\), is it a known unconditional theorem that
\[
 S(N,B):=\sum_{q=\lfloor L^B\rfloor+1}^{R_0}\frac{\mu(q)^2}{\phi(q)^2}
 \sum_{\substack{a\bmod q\\(a,q)=1}}\int_1^N\big(\psi(t;q,a)-t/\phi(q)\big)^2\,dt
 =O_\epsilon(N^{2+\epsilon})
\]
for every \(\epsilon>0\)? \(\psi(t;q,a)=\sum_{n\le t,\,n\equiv a(q)}\Lambda(n)\).
Since \(\psi(t;q,a)\) is a step function constant on each unit interval
\([t,t{+}1)\), \(\int_1^N(\cdots)^2\,dt\) and \(\sum_{t=1}^N(\cdots)^2\)
agree up to an \(O(1)\)-per-\(t\) discretization difference that does not
change any order tracked here; this document, and the script accompanying
it, work with the discrete sum, matching the convention `RANK3_ROUTE_D.md`
(D5) and `RANK3_MEAN_VALUE_TOOLS.md` already use for the same object,
\(T(q,b)=\sum_t\Delta(t;q,b)^2+(\text{telescoping term})\).

## 2. The literature search: no live access, same wall as this hunt's other citation checks

`WebSearch` and `WebFetch` were both attempted from this worktree and both
returned "you haven't granted it yet" with no interactive user able to
grant it -- the identical wall `RANK3_BDH_VERIFY.md` §"A word on sourcing"
already recorded, and the one `RANK3_POLYRANGE.md` itself is quoted (in this
document's own assignment) as having hit first, via the
personal.science.psu.edu course-notes URL `UPPER_BOUND.md` cites. No PDF or
local copy of Montgomery and Vaughan (*Multiplicative Number Theory I*),
Montgomery (*Topics in Multiplicative Number Theory*, LNM 227), Davenport
(*Multiplicative Number Theory*), or any paper by Motohashi, Friedlander-
Iwaniec, Fouvry, or Bombieri-Friedlander-Iwaniec exists under this worktree.
What follows is therefore sourced from the standard, checkable content of
those theorems as this hunt's own sibling documents already cite them, plus
this document's general knowledge of the named literature strands -- not
from a live fetch -- exactly the caveat `RANK3_BDH_VERIFY.md` states for
itself, reused here rather than re-argued.

**Reading the named literature strands against the exact shape asked for.**
None of (BV), (BDH), Motohashi's mean-value refinements, the
Friedlander-Iwaniec/Fouvry/Bombieri-Friedlander-Iwaniec line on primes in
arithmetic progressions to smooth or well-factorable moduli, or the "variance
of primes in short intervals/arithmetic progressions" literature (Hooley,
Goldston-Montgomery, Keating-Rudnick and its number-field-only analogue) is,
to this document's knowledge, stated as an integral- or sum-over-\(t\)
(rather than single-endpoint or max-over-\(t\)) second moment. Every version
of (BDH) this document is aware of -- including the sharp asymptotic
strengthening by Montgomery (1970) and Hooley -- is stated at a single
endpoint \(x\) (or, in some refinements, with a \(\max_{y\le x}\) outside the
\(q\)-sum, which is Bombieri-Vinogradov's shape, not a sum or integral over
the endpoint). The Motohashi/Friedlander-Iwaniec/Fouvry/BFI line extends
(BV)'s *range* (to well-factorable or smooth moduli near \(x^{4/7}\),
\(x^{1/2+\theta}\) for small \(\theta\), etc.) and BFI's own further work
extends the *level of distribution* in the Type II/III sums used for bounded
gaps between primes, but none of these, as far as this document is aware,
changes (BV)'s or (BDH)'s *endpoint* structure to an integral over \(t\).
The Barban-Vehov/Motohashi *weighted sieve* literature (which
`RANK3_MEAN_VALUE_TOOLS.md` §5 names as a place such a statement "might" live,
without confirming one) concerns weighted second moments in \(q\) at a fixed
endpoint, still, to this document's knowledge -- it is a different kind of
weighting (a sieve weight on \(q\), not an integral over \(t\)) and this
document does not find, or recall, a genuine \(t\)-integrated member of that
family either. **No theorem of the literal \(t\)-integrated shape asked for
here is found**, under any of the names the task lists, consistent with
(and no stronger a finding than) what `RANK3_BDH_VERIFY.md` §6 already
concluded for the closely related, harder H* question, and what
`RANK3_MEAN_VALUE_TOOLS.md` §5 already flagged as an open question it does
not resolve.

This is a negative literature finding, reported as precisely as this
document's access allows: not "no such theorem exists" (this document cannot
prove a negative over literature it cannot search live), but "this document,
working from the standard content of the named sources and no live search,
does not find one, and none of the three sibling documents in this hunt that
already checked adjacent statements against the same sources
(`RANK3_BDH_VERIFY.md`, `RANK3_MEAN_VALUE_TOOLS.md`) found one either."

## 3. What the literature search alone does not settle: \(S(N,B)\) is provable anyway

Section 2's negative finding is not the end of the story for *this specific*
statement, because \(S(N,B)\)'s extra factor \(1/\phi(q)^2\) -- absent from
every version of H* `RANK3_BDH_VERIFY.md` checked, and absent from (BDH)
itself -- is strong enough that the classical, single-endpoint (BDH), summed
crudely over \(t\) exactly the way `RANK3_MEAN_VALUE_TOOLS.md` §5 already
does to get its own (E1), and then summed over \(q\) by an elementary partial
summation (Abel summation) against the decaying weight \(\mu(q)^2/\phi(q)^2\),
already gives \(S(N,B)=O_\epsilon(N^{2+\epsilon})\) for every fixed \(B>0\)
-- **without needing any \(t\)-integrated theorem beyond what this hunt
already cites**. This is a derivation this document performs itself, not a
citation, and it is reported as such.

**Setup.** Write \(f(q):=\sum_{a\bmod q}^*\sum_{t=1}^N\Delta(t;q,a)^2\ge0\)
(the discrete form of \(S(N,B)\)'s inner double sum, dropping the
\(1/\phi(q)^2\) weight for the moment), and \(A:=\lfloor L^B\rfloor\). For
\(A<Q\le R_0\), define the running sum \(F(Q):=\sum_{q=A+1}^Q f(q)\). Since
\(f(q)=\sum_t d(t,q)\) with \(d(t,q):=\sum_a^*\Delta(t;q,a)^2\) the per-\(q\)
summand of (BDH)'s own \(D(t,Q)=\sum_{q\le Q}d(t,q)\),
\[
 F(Q)=\sum_{t=1}^N\big[D(t,Q)-D(t,A)\big]\ \le\ \sum_{t=1}^N D(t,Q)
 \ \ll\ \sum_{t=1}^N Qt\log t\ \ll\ QN^2\log N,
\]
using classical (BDH), \(D(t,Q)\ll Qt\log t\) uniformly for \(1\le Q\le t\)
(Barban 1966; Davenport-Halberstam 1966; see the sources cited in Section 1
of `RANK3_MEAN_VALUE_TOOLS.md` and `RANK3_BDH_VERIFY.md`), applied separately
at each integer \(t\le N\) and summed -- **exactly the crude step
`RANK3_MEAN_VALUE_TOOLS.md` §5 already uses to get its own (E1)**, reused
here, not re-derived. (For the small range \(t<Q\), where (BDH)'s stated
range \(Q\le x\) does not literally cover \(D(t,Q)\), a direct trivial
estimate -- each term \(\Delta(t;q,a)^2=O((\log t)^2)\) since at most one
integer \(n\le t<q\) can lie in a given residue class -- gives
\(D(t,Q)=O(Q^2\log^2t)\) there, smaller order than \(Qt\log t\) once summed
over the negligibly short range \(t<Q\le R_0\ll\sqrt N\); this document
does not belabor this boundary case further, as it does not change the
order below.) So \(F(Q)\ll QN^2\log N\) uniformly for every \(Q\) in
\((A,R_0]\), not only at \(Q=R_0\) -- this uniformity in \(Q\), which (BDH)
supplies "for free" because it holds at every \(Q\le t\), is exactly the
ingredient partial summation needs and a bound only at the single endpoint
\(Q=R_0\) would not supply.

**Partial summation against the weight.** \(w(q):=\mu(q)^2/\phi(q)^2\)
satisfies \(w(q)\le C(\log\log q)^2/q^2\) for \(q\ge3\) (from the classical
\(\phi(q)\gg q/\log\log q\)), so \(w(q)\le W(q):=C(\log\log q)^2/q^2\), a
majorant that is eventually non-increasing. Since \(f(q)\ge0\),
\[
 S(N,B)\ \le\ \sum_{q=A+1}^{R_0}W(q)f(q)
 =W(R_0)F(R_0)+\sum_{q=A+1}^{R_0-1}\big(W(q)-W(q+1)\big)F(q)
\]
(Abel summation; \(F(A)=0\)). The boundary term is negligible:
\(W(R_0)F(R_0)\ll(1/R_0^2)(\log\log R_0)^2\cdot R_0N^2\log N=
N^2\log N(\log\log R_0)^2/R_0\), and \(R_0\asymp\sqrt N/(3L)\to\infty\), so
this term is \(o(N^2)\) trivially. For the sum, \(W(q)-W(q+1)\ge0\)
eventually and \(F(q)\ll qN^2\log N\), so
\[
 \sum_{q=A+1}^{R_0-1}(W(q)-W(q+1))F(q)\ \ll\ N^2\log N\sum_{q=A+1}^{R_0-1}q\big(W(q)-W(q+1)\big).
\]
A second partial summation (or direct comparison with
\(\int_A^{R_0}x\,d(-W(x))\), integrable since \(xW(x)\sim(\log\log x)^2/x\))
gives \(\sum_{q=A+1}^{R_0-1}q(W(q)-W(q+1))\ll\sum_{q=A+1}^{R_0}W(q)\ll
(\log\log A)^2/A\). Combining,
\[
 S(N,B)\ \ll\ N^2\log N\cdot\frac{(\log\log A)^2}{A}
 \ +\ o(N^2),\qquad A=\lfloor L^B\rfloor.
\]
At \(A\asymp(\log N)^B\), \(\log N/A\asymp(\log N)^{1-B}\), so
\[
 \boxed{\ S(N,B)\ \ll_B\ N^2(\log N)^{\max(1-B,\,0)}(\log\log N)^{O(1)}.\ }
\]
This is \(O(N^2)\) for \(B=1\) and \(o(N^2)\) for \(B>1\) -- and, since any
fixed power of \(\log N\) (or \(\log\log N\)) is \(O_\epsilon(N^\epsilon)\)
for every \(\epsilon>0\), **this proves \(S(N,B)=O_\epsilon(N^{2+\epsilon})\)
for every fixed \(B>0\)**, exactly the statement asked about, at the full
stated range \(q\le R_0\), directly from classical (BDH) alone.

**What this is and is not.** This is an elementary partial-summation
argument built entirely from ingredients this hunt already has on record
(classical BDH, cited not re-derived; the same per-\(t\) crude bridging step
`RANK3_MEAN_VALUE_TOOLS.md` §5 already uses). It is not a citation of a
"\(t\)-integrated BDH" theorem, because Section 2 does not find one; it shows
that, for *this specific weight*, none is needed. It is this document's own
derivation and has not been checked by a second, independent party; Section
4 checks it numerically as far as reachable scale allows.

## 4. Numerical check: exact but too far pre-asymptotic to confirm or refute the rate

`polyrange_weighted_bdh_check.py` computes \(S(N,B)\) (discrete-\(t\) form)
exactly -- true von Mangoldt enumeration, closed-form per-residue-class
partial sums (no sampling, no \(O(N)\)-per-\(t\) loop; validated against a
brute-force \(O(N)\) per-\(t\) computation on small cases to floating-point
precision, see the script's own development notes) -- for \(N\) from
\(3\times10^5\) to \(2.4\times10^6\), \(B=1\) (results in
`results_polyrange_weighted_bdh_check.json`; \(B=2\) needs \(R_0>\lfloor
L^2\rfloor\), which needs \(N\) far beyond what this session's compute
budget affords -- \(R_0\) only reaches \(14\) to \(35\) across the \(N\)
range tested here, and \(B=2\) is reported empty at every \(N\) tried, not
silently skipped).

At these \(N\), \(S(N,1)/N^2\) rises from \(0.0045\) to \(0.018\) across an
8-fold range of \(N\) -- **not** the near-flat behavior Section 3's
\((\log\log N)^{O(1)}\) bound would suggest at \(B=1\) (where the bound is
\(O(N^2)\) with only log-log-power fluctuation, i.e. \(S/N^2\) should be
nearly constant, not visibly rising). This is not read as evidence against
Section 3's bound: \(R_0\) itself is only \(14\) to \(35\) at these \(N\) --
`rank3_bdh_probe.py`'s own experiment 1 already found and flagged that
(BDH)'s *measured* \(Q\)-dependence at comparably small \(Q\) (\(10\) to
\(500\), with \(N\) fixed) rises noticeably faster than the \(Q\log Q\)
asymptotic shape, attributing this to a pre-asymptotic regime where
lower-order terms have not yet become negligible relative to the leading
term -- and \(R_0\) here is smaller still, and *also* growing with \(N\)
(not held fixed), so the two data points compare genuinely different,
non-overlapping \(q\)-windows, not the same window at different \(N\). This
numerical check cannot, at reachable \(N\), distinguish "obeys Section 3's
bound with a pre-asymptotic transient" from "grows faster than Section 3
claims"; it is reported as measured, not fit to either reading, exactly the
caution `rank3_bdh_probe.py` and `RANK3_MEAN_VALUE_TOOLS.md` §3 already
apply to their own small-\(Q\) measurements. What the same script does
confirm cleanly: at every \(N,B\) checked, \(S(N,B)\) computed with the
weight \(\mu(q)^2\) alone (no \(1/\phi(q)^2\)) -- i.e. `RANK3_ROUTE_D.md`
(D11)'s actually-*proven* weight, Section 5 below -- is one to four orders
of magnitude larger than \(S(N,B)\) with the \(\mu(q)^2/\phi(q)^2\) weight at
the same \(N,q\)-range (e.g. at \(N=2.4\times10^6\): \(1.05\times10^{11}\)
versus \(2.68\times10^{13}\)), consistent with, though not a proof of,
Section 3's claim that the extra \(1/\phi(q)^2\) factor is doing real,
substantial work.

## 5. The caveat this document inherits from `RANK3_ROUTE_D.md`: this weight is not the one proven needed

`RANK3_ROUTE_D.md` §5, working from the same assignment's quoted
\(\mu(q)^2/\phi(q)^2\) guess, derives (D7)-(D11) exactly (Parseval,
character orthogonality, Cauchy-Schwarz -- no approximation) and finds the
guess is **not** what its own derivation establishes: the weight (D11)
actually proves, without assuming any cancellation in the cross term
\(\Sigma_{\rm cross}(q)\), is \(2\mu(q)^2\) -- \(O(1)\), with **no**
\(1/\phi(q)^2\) at all. Reaching \(\mu(q)^2/\phi(q)^2\) would require
\(\Sigma_{\rm cross}(q)\) to cancel the diagonal term down by a full extra
factor of \(\phi(q)^2\) beyond assuming it is merely negligible -- a claim
`RANK3_ROUTE_D.md` explicitly states is undetermined by anything in
`UPPER_BOUND.md` or `RESULTS.md`, and does not resolve.

Consequently: **confirming \(S(N,B)=O_\epsilon(N^{2+\epsilon})\) (Section 3
above) does not, by itself, resolve `RANK3_ROUTE_D.md` (D11)'s bound on
\(U_{(q)}\)**, because (D11)'s proven weight is \(\mu(q)^2\), not
\(\mu(q)^2/\phi(q)^2\). Plugging Section 3's method in with the *proven*
weight instead (\(w(q)=O(1)\), no decay) reproduces exactly
`RANK3_MEAN_VALUE_TOOLS.md`'s own (E1)-(E2): the Abel-summation boundary
term \(w(R_0)F(R_0)\asymp R_0N^2\log N\asymp N^{5/2}\) now dominates (since
\(w\) no longer decays, there is nothing for partial summation to save), and
Section 3's bound degrades exactly to `RANK3_MEAN_VALUE_TOOLS.md` §5's
already-recorded \(N^{5/2}\) order -- matching, not beating, CHHL's own
GRH-conditional benchmark, the same conclusion that document already
reached by a different (dyadic block, unweighted) route. This document adds
no improvement to that conclusion; it only pins down, precisely, that the
\(\phi(q)^{-2}\) weight is exactly the ingredient separating a bound that
closes (Section 3, but for a weight not known to be the right one) from a
bound that does not (`RANK3_MEAN_VALUE_TOOLS.md`'s, for the weight that is
proven).

## 6. Verdict

- **Literature search (Section 2):** no theorem of the exact "\(t\)-integrated
  BDH" shape is found, under any name checked, working from this hunt's own
  cited sources and general knowledge of the strands the task names
  (Bombieri-Vinogradov, Barban-Davenport-Halberstam and its Montgomery/Hooley
  sharp form, Motohashi, Friedlander-Iwaniec, Fouvry,
  Bombieri-Friedlander-Iwaniec, variance-of-primes and Barban-Vehov weighted
  sieve literature) -- with no live network access to confirm or overturn
  this (`WebSearch`/`WebFetch` both denied, same wall as
  `RANK3_BDH_VERIFY.md`).
- **But the specific statement asked about is true anyway (Section 3):**
  \(S(N,B)=O_\epsilon(N^{2+\epsilon})\) for every fixed \(B>0\), at the full
  range \(q\le R_0\), follows from classical (BDH) alone via elementary
  partial summation against the \(\mu(q)^2/\phi(q)^2\) weight -- no
  additional theorem, named or not, is needed for *this* weighted
  statement. This is this document's own derivation, not a citation.
- **Numerically (Section 4):** exact at every point checked, but the
  reachable \(q\)-range (\(R_0\) only \(14\)-\(35\)) is too small and too
  far pre-asymptotic to empirically confirm or refute the claimed rate,
  matching the same caution this hunt's own BDH probe already applies to
  itself at comparably small \(Q\).
- **The catch (Section 5, inherited from `RANK3_ROUTE_D.md`):** the
  \(\phi(q)^{-2}\) weight that makes Section 3's argument close is not the
  weight `RANK3_ROUTE_D.md` (D11) proves is actually needed for
  \(U_{(q)}\) -- that weight is the larger \(\mu(q)^2\) (no \(\phi(q)\)
  division), for which the identical method only reproduces
  `RANK3_MEAN_VALUE_TOOLS.md`'s already-recorded \(N^{5/2}\), not
  \(N^{2+\epsilon}\). So this document resolves the literature-search
  question it was assigned, but that resolution does not, on its own, unlock
  `RANK3_ROUTE_D.md`'s \(U_{(q)}\) bound; what would still be needed for that
  is a proof (not an assumption) that `RANK3_ROUTE_D.md` (D7)'s cross term
  \(\Sigma_{\rm cross}(q)\) genuinely cancels the diagonal term down toward
  the \(\phi(q)^{-2}\)-weighted size, which neither that document nor this
  one supplies.

This document is a literature search (Section 2, negative, network-access
limited), one elementary partial-summation derivation built from a
classical theorem this hunt already cites (Section 3), a numerical
measurement reported with its own pre-asymptotic limitation stated plainly
(Section 4), and a reconciliation with `RANK3_ROUTE_D.md`'s independent,
exact finding about which weight is actually proven (Section 5); it assumes
and establishes nothing about zeros of \(L\)-functions or the Riemann
Hypothesis.
