# Checking whether the Section 5 Siegel-Walfisz argument splices onto U_Q and Z_Q

This checks one specific question: can the Siegel-Walfisz major-arc argument
of UPPER_BOUND.md Section 5, equations (17)-(19) — proved uniformly for
denominators \(q\le Q'=\lfloor L^B\rfloor\), any fixed \(B\), \(L=\log N\) —
be spliced onto Section 6's mixed moment \(U_Q\) and fourth moment \(Z_Q\)
(defined just before its (23), for \(Q=\lfloor\sqrt N/3\rfloor\)) so as to
bound \(U_{2\le q\le Q'}\) and \(Z_{2\le q\le Q'}\) separately, at the
strength (19) gives their combined quantity \(M_{Q'}\). All equation
numbers in parentheses refer to UPPER_BOUND.md unless marked "here."

**Answer: no.** A first attempt at this splice looks like it works, but it
silently substitutes one arc system for another. Once that is corrected, the
splice fails outright for every \(q\) in the claimed range, including the
smallest one, \(q=2\) — not because of anything to do with the size of
\(q\), but because of the width of the arc that \(U_Q\), \(Z_Q\) actually
integrate over. Section 3 below gives the exact reason.

## 1. The two arc systems are not the same, for the same q

By (7), the arc dissection is built from one integer parameter \(Q\), chosen
once: \(\delta_q=Q/(qN)\), \(I_{q,a}=\{\alpha:\|\alpha-a/q\|\le\delta_q\}\).
The width of the arc attached to a given modulus \(q\) depends on which
\(Q\) was chosen for the whole dissection, not on \(q\) alone.

- Section 6's \(U_Q\), \(Z_Q\) — the objects the task asks about — are built
  with \(Q=\lfloor\sqrt N/3\rfloor\) (Section 6's opening line: "Now set
  \(Q=\lfloor\sqrt N/3\rfloor\)"). For a fixed modulus \(q\), their arc
  \(I_{q,a}\) has half-width \(\delta_q=Q/(qN)\asymp1/(q\sqrt N)\).
- Section 5's (17) is proved for a *different* dissection, with its own
  \(Q'=\lfloor L^B\rfloor\) in place of \(Q\) (Section 5's opening line:
  "First take \(Q=\lfloor L^B\rfloor\), for fixed \(B\), rather than a
  square-root arc denominator"). For the same modulus \(q\), that arc has
  half-width \(\delta'_q=Q'/(qN)\asymp L^B/(qN)\).

For any fixed \(q\) (in particular for every \(q\le Q'\)), the ratio of
widths is
\[
 \delta_q/\delta'_q=Q/Q'\asymp\sqrt N/L^B\to\infty.
\]
Section 6's arc for modulus \(q\) is therefore always far wider than
Section 5's arc for the same \(q\) — and (17) is a statement about
Section 5's narrower arc only: it reads "\(q\le Q\), \(|\beta|\le Q/(qN)\)"
with \(Q\) there meaning Section 5's own \(Q'\), by construction. It says
nothing about \(F_N\) on the wider annulus of Section 6's arc that lies
outside Section 5's arc, for any \(q\).

## 2. The gap is not just unstated — the proof of (17) genuinely fails there

This is not only a labeling mismatch. The paragraph justifying (17)
(immediately after its statement) needs the partial-summation cost against
\(\exp1(t\beta)\), which is \(O(1+N|\beta|)\), to be a *fixed power of*
\(L\), so that Siegel-Walfisz's arbitrary log-power saving \(NL^{-H}\)
absorbs it after raising \(H\). Concretely:

- On Section 5's own arc, \(|\beta|\le Q'/(qN)\), so
  \(N|\beta|\le Q'/q\le Q'=\lfloor L^B\rfloor\), a fixed power of \(L\). This
  is exactly what the proof needs, and is why (17) holds there for every
  fixed \(B,H\).
- On Section 6's arc, \(|\beta|\le Q/(qN)\) with \(Q=\lfloor\sqrt N/3\rfloor\),
  so \(N|\beta|\le Q/q\asymp\sqrt N/(3q)\). For any *fixed* \(q\) (in
  particular for every \(q\) in the claimed range \(2\le q\le Q'\), since
  \(Q'=\lfloor L^B\rfloor=o(\sqrt N)\)), this is a growing power of \(N\),
  not a fixed power of \(L\). Multiplying it against the Siegel-Walfisz
  error \(NL^{-H}\) gives \(N^{3/2}L^{-H}/q\), which exceeds the trivial
  size \(O(N)\) of \(F_N\) once \(N^{1/2}\gg qL^H\) — eventually true for
  every fixed \(q\) and every fixed \(H\). So the argument does not just
  fail to reach Section 6's arc; run there, it produces no saving over the
  trivial bound at all.

So the obstruction is driven by arc *width*, which is set by the global
dissection parameter \(Q\), not by the size of \(q\). This is the opposite
of what a first reading suggests: one might expect small \(q\) to be the
"easy" end, since (17)'s own \(q\)-range is \(q\le L^B\) and \(2\le q\le L^B\)
sits entirely inside it. But that \(q\)-range restriction in (17) is paired
with a specific, narrow \(\beta\)-range tied to Section 5's own \(Q'\); once
\(q\) is fixed and the arc is instead Section 6's wider one, the
\(\beta\)-range attached to that same small \(q\) already exceeds where the
Siegel-Walfisz saving can survive. Small \(q\) on Section 6's dissection is
not a favorable case for (17) — it is, if anything, the case with the widest
arc of all (since \(\delta_q=Q/(qN)\) is largest at small \(q\)).

## 3. Why a "use the narrower arc instead" fix does not repair the splice

One might try to define an auxiliary quantity using Section 5's narrower
arc in place of \(I_{q,a}\) for these small \(q\), where (17) is genuinely
valid, and call that the desired bound. This does not bound
\(U_{(q)}\), \(Z_{(q)}\) — the actual \(q\)-summands of Section 6's
\(U_Q\), \(Z_Q\) that feed equation (23) — for two reasons:

- \(U_{(q)}\), \(Z_{(q)}\) are defined (Section 6, before (23)) as integrals
  over Section 6's actual arc \(I_{q,a}\), of half-width \(Q/(qN)\). An
  integral over a strictly smaller sub-arc is a different quantity; it
  omits the annulus between the two arc widths, where (17) supplies no
  information about \(R_{q,a}=F_N-P_{q,a}\) at all, and where, per Section
  2 above, \(F_N\) need not be close to \(P_{q,a}\) — the trivial bounds
  \(F_N=O(N)\) and \(P_{q,a}=O(N/\phi(q))\) are all that is available there
  absent a separate argument. There is no basis here for asserting the
  omitted annulus contributes negligibly.
- The disjointness of the arcs (Section 3's argument, "the circular distance
  between distinct reduced fractions is at least \(1/(qq')\); their radii
  sum to \(Q(q+q')/(qq'N)<1/(qq')\)") is proved for a single, fixed \(Q\)
  used for every modulus in the dissection at once. \(U_Q\), \(Z_Q\), and
  the bound (23) built from them, are structured around that one dissection
  throughout Sections 6-7. Substituting a narrower arc for some moduli and
  the original wide arc for others is not a dissection of this kind, and
  nothing in Sections 3, 6, or 7 supports combining pieces built on
  different arc systems into a bound on \(U_Q\) or \(Z_Q\) as those
  quantities are actually defined.

## 4. The role of (18), for completeness

(18), \((|F_N|^2-|P_{q,a}|^2)^2\le8|P_{q,a}|^2|R_{q,a}|^2+2|R_{q,a}|^4\), is
not where this splice fails. Given a pointwise bound on \(R_{q,a}\) over an
arc, pulling that bound out of the corresponding integral and multiplying
by \(\int_{I_{q,a}}|P_{q,a}|^2\) (for the \(U\)-type term) or by the arc's
measure (for the \(Z\)-type term) is mechanically sound, with no missing
cross terms or double-counting, and (18) itself is needed only to
reconstitute a bound on the combined quantity \(M_{Q'}\) from separate
bounds on \(U\) and \(Z\), not to bound \(U\) and \(Z\) individually. Indeed,
restricted honestly to Section 5's *own* dissection (arcs of width
\(Q'/(qN)\), the arcs (17) is actually proved on), this mechanism does
produce matching separate bounds
\(\ll_{B,H}N^3L^{-2H}\log(2Q')\) and \(\ll_{B,H}N^3Q'^2L^{-4H}\) for the two
pieces of what would be \(M_{Q'}\) on that dissection, reproducing (19)
exactly via (18). That derivation is correct as a fact about Section 5's
own construction. The error in the original attempt at this splice was
treating that fact as if it also bounded Section 6's \(U_{(q)}\),
\(Z_{(q)}\) for \(q\le Q'\), which — per Sections 1-3 above — it does not,
because those live on a different, much wider arc for the same \(q\).

## 5. Relation to RANK3_SCOPE.md

RANK3_SCOPE.md Section 2 already states that "(17)/(SW) does not reach this
range at all," arguing from a mismatch of \(q\)-*ranges*: (17)'s uniformity
is fixed at \(q\le L^B\) for fixed \(B\), while rank 3 needs
\(2\le q\le R_0\) with \(R_0\) growing like a power of \(N\), so for any
fixed \(B\), (17) covers only a vanishing initial segment of rank 3's range
by \(q\)-size. That argument leaves open, in principle, whether the
vanishing initial segment it does cover — \(2\le q\le L^B\) — could still be
closed by transplanting (17) into Section 6's actual construction there.
This document answers that residual question: no. The obstruction found
here is different in kind from RANK3_SCOPE's: it is not that \(q\) is too
large for (17), but that Section 6's arc for any fixed \(q\) is too wide for
(17), because arc width there is set by the global parameter
\(Q=\lfloor\sqrt N/3\rfloor\), not by \(q\). So even the sub-range where (17)
nominally applies to a modulus \(q\) in isolation does not transfer into
Section 6's \(U_Q\), \(Z_Q\) at that same \(q\), and rank 3's range
\(2\le q\le R_0\) has no sub-piece, however small, that this route closes.

## 6. Summary

Splicing (17)-(19)'s device onto Section 6's \(U_Q\), \(Z_Q\), so as to
bound \(U_{2\le q\le\lfloor L^B\rfloor}\) and \(Z_{2\le q\le\lfloor
L^B\rfloor}\) separately, does not work. The Siegel-Walfisz pointwise
estimate (17) is proved on the arcs of Section 5's own, narrower dissection
(parameter \(Q'=\lfloor L^B\rfloor\)); Section 6's \(U_Q\), \(Z_Q\) integrate
over the arcs of a different, much wider dissection (parameter
\(Q=\lfloor\sqrt N/3\rfloor\)), and for every fixed \(q\) — including the
smallest, \(q=2\) — that wider arc extends far past where (17)'s own proof
(the partial-summation bound needing to be a fixed power of \(L\), not of
\(N\)) survives. This holds uniformly over the whole claimed range
\(2\le q\le\lfloor L^B\rfloor\), not just at its upper end, and there is no
way to patch it by substituting a narrower arc, since \(U_Q\), \(Z_Q\) and
the disjointness that lets them decompose by \(q\)-block are all fixed to
the single dissection parameter \(Q=\lfloor\sqrt N/3\rfloor\) throughout
Sections 6-7. Nothing here contradicts (1) or (19), both of which are
proved entirely within Section 5's own, narrower dissection and never call
on Section 6's \(U_Q\) or \(Z_Q\); this document only rules out one specific
way of connecting the two constructions, matching and sharpening Section
6's own remark that "Formula (17) does not apply for all \(q\le Q\)" by
identifying arc width, not the size of \(q\), as the actual obstruction.
