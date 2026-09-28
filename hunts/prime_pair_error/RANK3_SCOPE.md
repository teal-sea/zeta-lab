# Rank 3, priced: the mixed and fourth moments at \(2\le q\le R_0\)

This is a scoping document, not a proof attempt. It does not estimate the
quantities below; it says precisely what they are, why UPPER_BOUND.md leaves
them unestimated, what closing them would plausibly take, and whether closing
them alone would change anything. Everything here is derived from
UPPER_BOUND.md and RESULTS.md (its "The doors" section); no outside source is
used to establish a fact claimed below. Where those two documents do not
determine an answer, that is stated, together with what would.

Context: RESULTS.md's doors section ranks three unclosed constraints on the
budget of UPPER_BOUND.md equation (23). Rank 1 is the mixed moment at \(q=1\),
\(U_1\) (UPPER_BOUND.md Section 7). Rank 2 is the minor fourth moment \(I_Q\)
tied to the fourth residual moment at \(q>R_0\) (Section 6). Rank 3 is entered
in the doors table as "the remaining mixed and fourth moments at
\(2\le q\le R_0\)," with the cost cell "not attempted; cost unknown" and the
closing-route cell "not named in the text." This document prices that door.

## 1. What these terms are, and where they enter (23)

UPPER_BOUND.md Section 6 defines, for the square-root arcs
\(Q=\lfloor\sqrt N/3\rfloor\),
\[
 U_Q=\sum_{q,a}\int_{I_{q,a}}|P_{q,a}|^2|R_{q,a}|^2,\qquad
 Z_Q=\sum_{q,a}\int_{I_{q,a}}|R_{q,a}|^4,
\]
with \(P_{q,a}=(\mu(q)/\phi(q))K_N(\alpha-a/q)\), \(R_{q,a}=F_N-P_{q,a}\), and
the sum running over \(q\le Q\), \(a\) ranging over reduced residues mod
\(q\). These, plus the minor-arc fourth moment \(I_Q\) (a single quantity, not
indexed by \(q\)), enter the sufficient bound (23):
\[
 E(N)\le32U_Q+8Z_Q+4I_Q+O(N^2L^3).
\]
Both \(U_Q\) and \(Z_Q\) decompose additively by \(q\)-block, since the arcs
\(I_{q,a}\) are disjoint (Section 3). Write \(U_{(q)}\), \(Z_{(q)}\) for the
\(q\)-summand of each, so \(U_Q=\sum_{q\le Q}U_{(q)}\),
\(Z_Q=\sum_{q\le Q}Z_{(q)}\) (Section 7 already names \(U_{(1)}\) "\(U_1\)").
The text estimates:

- \(U_{(1)}=U_1\), via the exact identity (29)-(30) connecting it to
  \(\Delta(t)=\psi(t)-t\); reached bound \(O_H(N^3L^{-2H})\) for every fixed
  \(H\) (end of Section 7). This is rank 1.
- \(\sum_{q>R_0}U_{(q)}\), via the large-sieve dyadic-block argument
  (24)-(27); reached bound \(O(N^2L^5)\).
- \(\sum_{q>R_0}Z_{(q)}\), via Vaughan's bound (V) on the disjoint arcs with
  \(q>R_0\) (28); reached bound \(O(N^{13/5}L^6)\). This, with \(I_Q\)
  (bounded the same way in (22)), is rank 2.

Left over: \(\sum_{2\le q\le R_0}U_{(q)}\) and \(\sum_{q\le R_0}Z_{(q)}\).
These are rank 3. Section 8's own accounting table names this bucket "Other
moments with \(q\le R_0\)," bound "No adequate estimate here," contribution
"Still required by (23)" — the same fact the doors table records as rank 3.

**A discrepancy in the source's own scoping, stated rather than resolved.**
UPPER_BOUND.md's Section 8 table scopes the unestimated bucket as
\(q\le R_0\) (no exception for \(q=1\)), while RESULTS.md's doors table names
it "\(2\le q\le R_0\)." The reason for the difference is visible in the text:
Section 7 splits \(U_{(1)}\) off by name and gives it an identity and a
bound, so on the \(U\)-side the leftover really is \(2\le q\le R_0\). No
analogous step exists for \(Z\): the text never isolates \(Z_{(1)}\), gives it
an identity, or bounds it. So on the \(Z\)-side the leftover is the full
range \(1\le q\le R_0\), including \(q=1\). Whether \(Z_{(1)}\) is meant to
sit inside rank 3, inside rank 1 alongside \(U_1\), or as an unlabeled fourth
item is not determined by either document; nothing here decides it. What
would decide it is the same thing that would close part of rank 3 itself: a
convolution identity for \(Z_{(1)}=\int_{\|\beta\|\le Q/N}|K_N(\beta)|^2
|F_N(\beta)-K_N(\beta)|^4\,d\beta/|K_N|^2\)-type object, or some other
argument, of the kind Section 7 builds for \(U_1\) but never extends to the
fourth moment. Below, "rank 3" means the union
\(\{U_{(q)}:2\le q\le R_0\}\cup\{Z_{(q)}:1\le q\le R_0\}\), the largest
reading consistent with both tables, and the \(q=1\) fourth moment is flagged
explicitly wherever it matters.

## 2. Why the text has no estimate for this range

The construction has exactly three tools for bounding \(F_N\) or its
residual near a rational \(a/q\): the Siegel-Walfisz major-arc approximation
(17), Vaughan's exponential-sum bound (V), and the additive large sieve (LS)
used dyadically in (24)-(26). None of the three reaches \(2\le q\le R_0\) (or
\(1\le q\le R_0\) on the \(Z\)-side) at a useful strength, for three separate
reasons read directly off the text.

**(17)/(SW) does not reach this range at all.** Its uniformity is in
\(q\le Q'=\lfloor L^B\rfloor\) for a *fixed* \(B\) (Section 5); \(L^B\) is a
fixed power of \(\log N\), while \(R_0=Q/L\) with \(Q=\lfloor\sqrt N/3\rfloor\)
grows like a positive power of \(N\) (order \(N^{1/2}/L\)). For any fixed
\(B\), \(L^B\) is eventually smaller than \(R_0\) by a growing margin, so
(17) covers only a vanishing initial segment of \(2\le q\le R_0\), and
Section 6 does not attempt even that: it states plainly "Formula (17) does
not apply for all \(q\le Q\)" and abandons it in favor of (V) and (LS) for
the whole of the square-root-arc argument. No part of Section 6 or 7 invokes
(17) inside the range \(q\le R_0\).

**The (24)-(26) dyadic-block bound degrades exactly where rank 3 lives.** The
per-block estimate (25), for the block \(R<q\le\min(2R,Q)\), is
\[
 U_{R<q\le\min(2R,Q)}\ll w(Q)^2N^3L/R^2,
\]
which only saves against the trivial size of the sum when \(R\) is large.
Summing dyadic blocks from \(R_0\) upward telescopes to the useful bound (26),
\(U_{q>R_0}\ll w(Q)^2N^3L/R_0^2\), because the blocks shrink geometrically as
\(R\) grows. Running the same sum downward from \(R_0\) to cover
\(2\le q\le R_0\) instead does not telescope to anything small: the smallest
block, \(R=1\) (i.e. \(q=2\)), alone costs \(O(w(Q)^2N^3L)=O(N^3L^3)\) by
(25), since \(w(Q)\ll L\) by (15). That single block already exceeds the
target \(N^{2+\epsilon}\) by a full power of \(N\), and is no better than the
trivial-strength end of what (25) can give; the technique that closes rank 2
and \(U_{q>R_0}\) simply does not carry a saving at small \(R\), and the text
gives no separate argument for that regime.

**(V) is weakest exactly here, not just insufficiently strong.** Vaughan's
bound, \(|F_N(\alpha)|\ll(Nq^{-1/2}+N^{4/5}+\sqrt{Nq})L^{5/2}\), has its first
term dominate for small \(q\): at \(q=O(1)\) it gives \(|F_N|\ll NL^{5/2}\),
the same order as the trivial bound \(F_N=O(N)\), i.e. no saving at all. The
term \(Nq^{-1/2}\) falls below \(N^{4/5}\) only once \(q\gtrsim N^{2/5}\); for
\(q\lesssim N^{2/5}\), (V) is at its weakest, worse than the bound that
limits rank 2. Because \(R_0\sim N^{1/2}/(3L)\) grows faster than \(N^{2/5}\),
the range \(2\le q\le R_0\) splits: on its lower part, \(q\lesssim N^{2/5}\),
(V) gives essentially nothing; on its upper part, \(N^{2/5}\lesssim q\le
R_0\), (V) gives the same \(N^{4/5}\)-order bound that Section 6 already
identifies as the source of rank 2's shortfall (the paragraph after (22)
names the \(N^{4/5}\) term as coming from Vaughan's own Type I/II balance at
\(U=V=N^{2/5}\), independent of how \(Q\) is chosen). So no part of rank 3 is
covered adequately by (V) either.

**The one identity in the text that works is special to \(q=1\) and does not
generalize as written.** Section 7's bound on \(U_1\) comes from an exact
Parseval identity (29): at \(q=1\), \(P_{1,1}=K_N\) exactly (there is only one
reduced residue, and \(\mu(1)/\phi(1)=1\)), so \(R_{1,1}=F_N-K_N\) is a single
well-defined arithmetic object whose Fourier coefficients are partial sums of
\(\Lambda(n)-1\), and Parseval converts the weighted integral \(U_1\)
directly into a sum of \(\Delta(t)^2=(\psi(t)-t)^2\). For \(q\ge2\) there are
\(\phi(q)\) residues \(a\), and \(P_{q,a}\) models a \(q\)-periodic bias, not
a single classical function; no analogous identity converting \(U_{(q)}\) or
\(Z_{(q)}\) into a named arithmetic quantity is exhibited in either document
for \(q\ge2\). Building one (Route D below) would plausibly need, per
residue class, the analogue of \(\Delta(t)\), namely
\(\Delta(t;q,a)=\psi(t;q,a)-t/\phi(q)\) — which returns to the same
uniform-in-\(q\) estimate that (17)/(SW) cannot supply in this range.

In short: the range \(2\le q\le R_0\) (and, on the fourth-moment side,
\(q=1\) as well) sits strictly between where (17) is valid and where (V) and
the dyadic (LS) argument start to save, and the one exact identity available
in the text is tied to the single value \(q=1\). This is a gap in the tools
assembled here, not a claim that no tool exists.

## 3. Plausible routes, and what each would cost

Four routes are visible from the structure above. None is carried out, named
with a cost, or ruled out by either document; what follows prices each
against what the text already shows, and states plainly where the sources
stop determining the answer.

**Route A: extend (17)/(SW)-type uniformity to \(q\) up to a positive power
of \(N\).** This is the route the gap in Section 2 points to most directly:
what is missing is exactly a Siegel-Walfisz-strength estimate valid for
individual moduli growing like \(N^{1/2}\), not just fixed powers of
\(\log N\). The text's own evidence on the cost of this kind of estimate is
Section 7's \(q=1\) case: the only closing route it exhibits for the
analogous unconditional gap there, (31), assumes RH (Section 7, discharging
\(U_1\) to \(O(N^2L^4)\) "assuming RH"). Using RH to close a per-modulus
uniformity for rank 3 would carry the same problem UPPER_BOUND.md Section 1
already flags for the whole project: the point of an unconditional
\(N^{2+\epsilon}\) bound is that it would itself force RH via CHHL's lower
bound, so assuming RH to reach it is circular with respect to this hunt's own
stated target. An *averaged*-in-\(q\) variant, of a shape that would sit
naturally inside the already-\(q\)-summed quantities \(U_Q\), \(Z_Q\), is not
named, cited, or evaluated anywhere in UPPER_BOUND.md or RESULTS.md; whether
such an averaged estimate exists, what it would need to assume, and whether
it would even plug into the arc-by-arc structure used here (which needs
control at each \(q\), not only on average, since (18) and (23) bound
\(|R_{q,a}|\) arc by arc before summing) is not determined by these sources.

**Route B: refine the (24)-(26) large-sieve argument at small block size.**
This is the route local to rank 3 alone; it does not overlap with what
closes ranks 1 or 2. Section 2 above shows precisely what fails: the per-block
bound (25) does not save at small \(R\), and the smallest block already costs
a full power of \(N\) above target. The text gives no indication of what a
refinement would need to assume beyond stating that the present instance of
(24)-(26) is not it; a variant would need either a sharper cross-term average
than (LS) supplies at \(O(1)\)-sized blocks, or a different decomposition
that does not degrade there. Neither is sketched.

**Route C: a minor-arc bound for (V) stronger over \(2\le q\le R_0\).**
This route is not independent of rank 2. The doors table already names "a
minor-arc bound stronger than Vaughan's (V)" as rank 2's own missing tool,
and Section 6 states that the \(N^{4/5}\) term traces to Vaughan's Type I/II
balance point at \(U=V=N^{2/5}\), a structural feature of the identity used
to prove (V), not a parameter choice made in this construction. Section 2
above shows the upper part of rank 3's range (\(q\gtrsim N^{2/5}\)) hits
exactly this same floor. So any route that improves (V) enough to close rank
2 would plausibly help the upper part of rank 3 too, and conversely; the cost
of Route C is therefore the same open cost the doors table already assigns
rank 2 (a stronger exponential-sum estimate than (V), not exhibited or costed
in either document), not an additional, separate cost specific to rank 3. The
lower part of rank 3's range (\(q\lesssim N^{2/5}\), where (V) gives no
saving at all) is not touched by this route even if it succeeds for rank 2.

**Route D: a per-\((q,a)\) generalization of the \(q=1\) identity (29).**
As noted in Section 2, this restates Route A rather than avoiding it. The
identity half is plausible by the same Parseval/convolution computation
Section 7 performs for \(q=1\), carried out for each residue class; nothing
in the text suggests an obstruction to writing it down. But converting that
identity into a bound at each \(q\le R_0\) still needs a uniform estimate for
\(\Delta(t;q,a)\) at moduli growing like a power of \(N\) — the same
requirement Route A names. Route D therefore does not lower the cost of
Route A; it only relocates where the missing input would be used.

**Summary of cost.** Routes A and D reduce to the same unconditional gap,
which the text's own \(q=1\) precedent shows has no unconditional closing
route here and only a circular (RH-assuming) one. Route C overlaps with
rank 2's already-named, already-unpriced gap over part of rank 3's range and
does nothing for the rest. Route B is the one route local to rank 3, and the
sources show only that its present instance fails at small block size, not
what a working version would need to assume. None of the four is costed to
completion, in effort or in hypotheses, by UPPER_BOUND.md or RESULTS.md; that
the doors table records rank 3's cost as "unknown" is consistent with this,
not merely an omission the source text happened not to fill in.

## 4. Whether closing rank 3 alone could move the reached bound

No, for two separate reasons, both visible directly in the text.

**First, rank 3 has no connection to the bound already reached.** UPPER_BOUND.md's
proved result, (1), \(E(N)\ll_CN^3(\log N)^{-C}\) for every fixed \(C\), is
established in Section 5 using \(M_Q\) and \(I_Q\) at \(Q=\lfloor L^B\rfloor\)
(the polylog-arc regime), and never invokes \(U_Q\), \(Z_Q\), or the
\(q\)-block decomposition at all — that apparatus is built in Sections 6-7
solely for the separate, unfinished attempt at the sharper target
\(N^{2+\epsilon}\) through (23). So closing rank 3, in whole or in part,
changes nothing about (1); (1) does not read from it.

**Second, within the (23) route itself, closing rank 3 alone would not
change that route's total order.** Equation (23) sums three components with
no dual or shadow price to exploit (RESULTS.md's doors section, "Active
constraints": "UPPER_BOUND.md Section 8 already tallies the budget as a sum
of six components, not a single objective with one dual"). The total order
this route could reach is therefore governed by whichever named term is
weakest, however strong the others become. Rank 1's own established bound is
\(O_H(N^3L^{-2H})\) for every fixed \(H\) (Section 7): a saving of an
arbitrary fixed power of \(\log N\) off \(N^3\), and no saving of any power
of \(N\) proved without assuming RH. That is asymptotically weaker than rank
2's established \(O(N^{13/5}L^6)\) for every large \(N\) and every fixed
\(H\), since \(N^{13/5}\) is a fixed power below \(N^3\) while
\(N^3L^{-2H}\) exceeds \(N^{3-\delta}\) eventually for every \(\delta>0\), no
matter how \(H\) is fixed. So among the three named constraints, rank 1 is
currently the weakest link, not rank 2. Suppose rank 3 were closed outright
to the target strength \(O_\epsilon(N^{2+\epsilon})\), with ranks 1 and 2 left
exactly as UPPER_BOUND.md currently proves them: (23)'s total would still be
capped by rank 1's \(O_H(N^3L^{-2H})\), which is the same order of saving
(log-power off \(N^3\)) that (1) already reaches by a wholly different route.
Closing rank 3 alone would therefore leave the \((23)\)-route at no better an
order than what is already proved. Reaching \(N^{2+\epsilon}\) through (23)
needs ranks 1 and 2 closed to comparable strength as well; rank 3's closure
is necessary for that target and invisible in the final exponent without the
other two, exactly because (23) adds the ranks rather than letting the
smallest one dominate.
