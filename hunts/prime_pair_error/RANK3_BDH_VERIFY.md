# Checking hypothesis H* (RANK3_MEAN_VALUE_TOOLS.md Section 3's BDH input)
# against the primary sources it is attributed to

This document checks, against citable primary sources rather than by
re-derivation, a specific hypothesis H* that would be needed to push
RANK3_MEAN_VALUE_TOOLS.md Section 3's Barban-Davenport-Halberstam route
further than that document itself takes it. It does not attempt the
Abel-summation splice into \(U_{(q)}\) that a confirmed H* would feed
(that is separate work, as the task assigning this document says). It
writes nothing about zeros of \(L\)-functions or the Riemann Hypothesis.

**A word on sourcing.** This attempt has no live network access: `WebSearch`
and `WebFetch` calls both returned a permission error with no interactive
user available to grant it, and no local copy of Montgomery and Vaughan,
*Multiplicative Number Theory I*, Montgomery, *Topics in Multiplicative
Number Theory* (LNM 227), or Davenport, *Multiplicative Number Theory*
exists anywhere under this worktree. This is the same wall the document
this task quotes already recorded ("via a URL to course notes ... that this
attempt could not fetch"). What follows is therefore sourced from the
precise, checkable, standard textbook content of those three books as
commonly stated (the same three RANK3_MEAN_VALUE_TOOLS.md Section 1 already
cites and whose citations this document reuses rather than re-checks), not
from a live fetch of a specific page. Where the exact theorem number or page
is not something this attempt could re-verify online, that is flagged
explicitly rather than stated as if checked. A later attempt with working
network access should confirm exact theorem/page numbers directly against
the PDF at the URL UPPER_BOUND.md already cites, or against Davenport or
Montgomery's LNM 227 directly, and correct anything below that a live check
contradicts.

## 1. H*, restated exactly

\[
 \text{For every fixed }A>0,\text{ uniformly for }1\le Q\le R_0:\qquad
 \sum_{q\le Q}\ \sum_{\substack{a\bmod q\\(a,q)=1}}\ \sum_{t=1}^N
 |\Delta_a(t;q)|^2\ \ll_A\ QN^2(\log N)^{C_0-A}
\]
for some absolute constant \(C_0\), where
\(\Delta_a(t;q)=\sum_{n\le t}\big[\Lambda(n)e(na/q)-\mu(q)/\phi(q)\big]\),
\(R_0=Q_{\max}/L\) with \(Q_{\max}=\lfloor\sqrt N/3\rfloor\) and \(L=\log N\)
(UPPER_BOUND.md Section 6; note UPPER_BOUND.md and RANK3_SCOPE.md both call
the arc parameter itself \(Q\), so here "\(Q\)" is H*'s own summation cutoff,
distinct from UPPER_BOUND.md's fixed \(Q=\lfloor\sqrt N/3\rfloor\), matching
how the task phrasing uses it).

\(\Delta_a(t;q)\) is not RANK3_ROUTE_D.md's or RANK3_MEAN_VALUE_TOOLS.md's
\(\Delta(t;q,b)=\psi(t;q,b)-t/\phi(q)\): it is the partial sum, up to \(t\),
of \(F_N\)'s integrand at the single rational frequency \(a/q\) minus
UPPER_BOUND.md Section 6's own major-arc model density
\(P_{q,a}=(\mu(q)/\phi(q))K_N(\alpha-a/q)\) restricted to that frequency
(\(\mu(q)/\phi(q)\) is exactly \(P_{q,a}\)'s coefficient there). This is a
faithful, if differently indexed, discrepancy quantity for the same
approximation the identity actually uses, and Section 2 below relates it
precisely to \(\Delta(t;q,b)\).

## 2. \(\Delta_a(t;q)\) and \(\Delta(t;q,b)\) are the same object, dually

By orthogonality, for \((a,q)=1\),
\[
 \sum_{n\le t}\Lambda(n)e(na/q)
 =\sum_{b\bmod q}e(ba/q)\sum_{\substack{n\le t\\ n\equiv b\,(q)}}\Lambda(n)
 =\sum_{b\bmod q}e(ba/q)\psi(t;q,b),
\]
and \(\psi(t;q,b)=O(\log q\log t)\) for \((b,q)>1\) (only prime-power
divisors of \(q\) contribute), so up to that negligible correction,
\[
 \sum_{n\le t}\Lambda(n)e(na/q)
 =\sum_{\substack{b\bmod q\\(b,q)=1}}e(ba/q)\,\psi(t;q,b)+O(\log q\log t).
\]
Since the Ramanujan sum at \((a,q)=1\) is \(c_q(a)=\mu(q)\), subtracting
\(t\mu(q)/\phi(q)=\big(t/\phi(q)\big)\sum_{(b,q)=1}e(ba/q)\) from both sides
gives
\[
 \Delta_a(t;q)=\sum_{\substack{b\bmod q\\(b,q)=1}}e(ba/q)\,\Delta(t;q,b)
 +O(\log q\log t).
\]
This is the standard duality RANK3_MEAN_VALUE_TOOLS.md Section 1 already
names ("dual, via Gauss sums, to the additive large sieve"), applied here at
the level of the partial sum rather than only the full large-sieve
inequality; it is bookkeeping, not a new estimate. Summing over
\((a,q)=1\) and using orthogonality of \(e(ba/q)\) over the reduced
residues (a finite character-sum identity, not the large sieve itself),
\[
 \sum_{\substack{a\bmod q\\(a,q)=1}}|\Delta_a(t;q)|^2
 =\phi(q)\sum_{\substack{b\bmod q\\(b,q)=1}}|\Delta(t;q,b)|^2
 +O\big(\phi(q)\log^2q\log^2t\big),
\]
i.e. H*'s left side, for fixed \(q\), is \(\phi(q)\) times \(D(t,\{q\})\)'s
single-modulus summand, up to an error that is negligible at every scale
this document or RANK3_MEAN_VALUE_TOOLS.md tracks. **So checking H* against
a classical statement of (BDH) for \(\Delta(t;q,b)\) is legitimate**, not a
category error, modulo this standard identification, which this document
states once and does not re-derive further.

## 3. The single-endpoint case: classical (BDH), confirmed, but at one fixed
##    log power, not "for every \(A\)"

The task's own framing of the single-point special case is exactly the
classical theorem: for \(1\le Q\le x\),
\[
 D(x,Q):=\sum_{q\le Q}\sum_{\substack{b\bmod q\\(b,q)=1}}
 \big(\psi(x;q,b)-x/\phi(q)\big)^2\ \ll\ Qx\log x
\tag{BDH}
\]
unconditionally (Barban 1966; Davenport and Halberstam 1966), proved via
the multiplicative large sieve (Montgomery and Vaughan, *Multiplicative
Number Theory I*, the large-sieve chapter and its Barban-Davenport-
Halberstam corollary; Montgomery, *Topics in Multiplicative Number Theory*,
LNM 227, Chapter 4; Davenport, *Multiplicative Number Theory*, the chapter
on the large sieve and primes in arithmetic progressions). This is exactly
the form RANK3_MEAN_VALUE_TOOLS.md Section 3 already cites and numerically
checks (`rank3_bdh_probe.py`), and this document adds nothing new to that
citation beyond the duality of Section 2. Two range facts matter here, and
this document reads them the same way RANK3_MEAN_VALUE_TOOLS.md Section 3
already states them:

- **(BDH) as an upper bound holds for the *entire* range \(1\le Q\le x\)**,
  with no lower threshold on \(Q\) and no dependence of the range on any
  extra parameter -- it is a single valid inequality restricted to fewer
  terms as \(Q\) shrinks, so it applies at \(Q=R_0\ll\sqrt N\) exactly as it
  does at \(Q=N\). Range is not an obstruction for the single-endpoint case.
- **The sharp asymptotic strengthening is a different, narrower-range
  statement.** Montgomery (1970), and independently Hooley, proved
  \(D(x,Q)\sim Qx\log Q\) (matching the trivial-looking upper bound as a
  genuine two-sided asymptotic, not just an upper bound) uniformly for
  \(x(\log x)^{-A}\le Q\le x\), for every fixed \(A>0\) -- i.e. for \(Q\)
  within any fixed power of \(\log x\) *below \(x\) itself*, not for small
  \(Q\). \(R_0\asymp\sqrt N/(3L)\) is nowhere near this range (it is far
  below \(x(\log x)^{-A}\) for any fixed \(A\), once \(N\) is large): the
  "stronger forms much further" the task's own phrasing anticipates reach
  *closer to \(Q=x\)*, not closer to \(Q=1\). This is consistent with, not
  contradicting, the previous bullet: the *upper bound* (BDH) reaches every
  \(Q\), the *sharp asymptotic* only reaches large \(Q\). Since H* only
  needs an upper bound at \(Q\le R_0\), this distinction does not by itself
  block H* -- but it does mean the "for every \(A\)" language in the sharp
  form is about the *precision* of the asymptotic at large \(Q\), not about
  an arbitrarily strong saving available at every \(Q\) including small
  \(Q\), which is the reading H* needs and Section 4 addresses.

**Reading against H* at the single endpoint.** Taking \(t=N\) only (dropping
H*'s sum over \(t\)) and comparing to (BDH) via Section 2's duality: (BDH)
gives exactly \(QN\log N\), a *single* fixed power of \(\log N\) -- matching
H* with \(C_0=1\) and \(A=0\), i.e. the *weakest* member of H*'s claimed
family. It does **not**, on its own, give H*'s stronger members: (BDH), as
the standard theorem is stated in these three sources, carries no free
parameter \(A\) with an arbitrarily strong log saving. **The single-endpoint
case of H* is confirmed only at \(A=0\)** (i.e. as the bound \(\ll QN\log
N\), full range \(Q\le R_0\)); the claim "for every fixed \(A>0\)" is a
strictly stronger statement that (BDH) as classically stated does not
supply, at any \(Q\), let alone uniformly down to \(R_0\).

## 4. Where an arbitrary-\(A\) log saving would have to come from, and why
##    it is not available from (BV) either

An arbitrary-\(A\) saving on a mean-*square*, summed-in-\(q\) quantity is
exactly Bombieri-Vinogradov's *kind* of strength, not Barban-Davenport-
Halberstam's. RANK3_MEAN_VALUE_TOOLS.md Section 2 already checked (BV)
against this same identity and found: (BV) bounds a sum of max-deviations,
not a sum of squares, by \(x(\log x)^{-A}\) for every fixed \(A\), at the
cost of a range \(x^{1/2}(\log x)^{-B(A)}\) with \(B\) growing with \(A\);
plugging it in reproduces only (SW)'s own log-power strength
(\(O_H(N^3L^{-H})\)), "never a saving of any power of \(x\)." That
conclusion, reused here rather than re-derived, is exactly why an
arbitrary-\(A\) member of H* cannot simply be assembled from (BV) squared,
Cauchy-Schwarz'd, or otherwise combined with (BDH)'s shape at a fixed range
independent of \(A\): (BV)'s own range *shrinks* as \(A\) grows (\(B(A)\)
increases), while H* asks for the *same* range \(Q\le R_0\), with no
\(A\)-dependence in the range at all, for every \(A\) simultaneously. A
hybrid theorem with (BDH)'s square-sum shape and (BV)'s arbitrary-\(A\)
saving, valid on a single \(A\)-independent range down to \(Q\le R_0\), is
not among the theorems stated in any of the three named books as this
document or RANK3_MEAN_VALUE_TOOLS.md read them, and this document did not
find one under another name either. This is the same category of gap
RANK3_MEAN_VALUE_TOOLS.md Section 5 already surfaces from a different
angle (there, for the \(t\)-summed quantity specifically); Section 5 below
gives the \(t\)-summed version of the same gap.

## 5. The \(t\)-sum: available at order \(QN^2\log N\) (i.e. H* with
##    \(A=0\)), not with any further saving found

UPPER_BOUND.md's own remark, quoted in the task, that "the version with a
maximum over \(t\) follows from the usual theorem by treating \(t\le
N/L^D\) trivially and applying it above that point," is stated for (SW),
whose *content* is an error term \(O_{B,H}(NL^{-H})\) against a main term
\(t/\phi(q)\) of full size \(t\): trivially bounding \(|\Delta(t;q,b)|\le t\)
for \(t\le N/L^D\) costs at most \(N/L^D\), which is already smaller than
(SW)'s own claimed saving once \(D\) is chosen large enough relative to
\(H\) -- the trivial range is *absorbed into the error budget the theorem
already has*.

**This trick does not transfer to (BDH)'s quantity.** (BDH)'s content,
\(D(t,Q)\ll Qt\log t\), is not an error term dominated by a separate larger
main term; it *is* the theorem's leading-order content, and it scales with
\(t\) itself (RANK3_MEAN_VALUE_TOOLS.md Section 3: "a full power of both
\(Q\) and \(x\) saved... down to every \(Q\le x\)"). Truncating \(t\le
N/L^D\) "trivially" means falling back to the *trivial* per-\(t\) bound
(order \(Q^2t^2\), RANK3_MEAN_VALUE_TOOLS.md Section 3's own accounting),
which is far *larger* than \(D(t,Q)\) itself at that same \(t\), not
smaller -- there is no saving to fall back into. Consequently no
dyadic-dissection bridge of the (SW) kind rescues a \(t\)-summed (BDH) at
better than the crude bound obtained by applying (BDH) separately at each
\(t\le N\) and summing:
\[
 \sum_{t=1}^N D(t,Q)\ \ll\ \sum_{t=1}^N Qt\log t\ \ll\ QN^2\log N,
\]
exactly RANK3_MEAN_VALUE_TOOLS.md's own (E1), independently re-derived here
from the structural reason the (SW)-style shortcut fails rather than
assumed. This is H* with \(C_0=1\), \(A=0\) again -- the same, weakest
member of H*'s family, and this document finds no route in the three named
sources, nor a structural bridge from (SW)'s own trick, to any stronger
member (\(A>0\)) of the \(t\)-summed claim either.

## 6. Verdict

**Confirmed, precisely:** the single-endpoint, \(A=0\) member of H*,
\(\sum_{q\le Q}\sum_a^*|\Delta_a(N;q)|^2\ll QN\log N\), uniformly for the
*entire* range \(1\le Q\le N\) (so in particular \(Q\le R_0\)) -- this is
classical (BDH), via Section 2's duality, and is the content
RANK3_MEAN_VALUE_TOOLS.md Section 3 already cites and measures.

**Confirmed, at the same weakest member only:** the \(t\)-summed extension,
at order \(QN^2\log N\) (H* with \(C_0=1\), \(A=0\)), via the crude
per-\(t\) sum of Section 5 -- matching, not exceeding, RANK3_MEAN_VALUE_TOOLS.md's
own (E1)/(E2).

**Not found, and not supported by (BDH) or (BV) as stated in Montgomery and
Vaughan, Montgomery's LNM 227, or Davenport:** the "for every fixed \(A>0\)"
clause of H*, at *either* the single-endpoint or the \(t\)-summed form,
uniformly on the single range \(Q\le R_0\). Section 3 shows (BDH)'s sharp,
arbitrary-precision asymptotic form reaches the wrong end of the \(Q\)-range
(large \(Q\), not small); Section 4 shows (BV)'s arbitrary-\(A\) strength
comes with an \(A\)-shrinking range, incompatible with H*'s fixed range;
Section 5 shows the natural (SW)-style bridge for extending to a \(t\)-sum
does not transfer to (BDH)'s shape. What is missing, stated as precisely as
this document can: a mean-square (not max-deviation) analogue of
Bombieri-Vinogradov -- an arbitrary-\(A\), \(A\)-independent-range,
\(t\)-integrated Barban-Davenport-Halberstam theorem -- and this document
does not find one named in the three sources it checked, nor construct one.
This is a refinement of, not a departure from, RANK3_MEAN_VALUE_TOOLS.md
Section 8's own list of missing ingredients (its item (i)); this document's
contribution is pinning exactly which two of H*'s three strengthenings
(arbitrary \(A\), and the \(t\)-sum) are and are not covered by the named
primary sources, and why, rather than treating H* as a single yes/no
question.

**Even if the missing hybrid theorem existed and gave the strongest member
of H* at every fixed \(A\):** plugged into RANK3_ROUTE_D.md (D11) at
\(Q=R_0\), it would give \(U_{(q)}\)'s first term order
\(R_0N^2(\log N)^{C_0-A}\ \asymp\ N^{5/2}(\log N)^{-1-A}\) for every fixed
\(A\) -- an improvement over RANK3_MEAN_VALUE_TOOLS.md Section 5's own
\(N^{5/2}\) by an arbitrary power of \(\log N\), but, by RANK3_MEAN_VALUE_TOOLS.md
Section 2's own reasoning applied here verbatim, never by any power of
\(N\): a log saving, however large but fixed, cannot on its own close the
full power \(N^{1/2}\) gap to \(N^{2+\epsilon}\). So confirming the missing
piece of H* would sharpen, but not by itself close, the same door
RANK3_MEAN_VALUE_TOOLS.md Section 5 already prices -- consistent with that
document's own conclusion and RANK3_SCOPE.md Section 3's, that no route
named so far is costed to completion. This point is recorded here because
it bears on whether pursuing H*'s missing piece is worth the next attempt's
time, not as the substance of the verify/refute task itself, which Section
6's first three paragraphs above answer.

This document is a citation check (Sections 1, 3, 4) plus one finite,
standard duality identity (Section 2) plus a structural argument for why a
specific bridging trick does not transfer (Section 5); it assumes and
establishes nothing about zeros of \(L\)-functions or the Riemann
Hypothesis.
