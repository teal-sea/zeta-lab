# Route G: does a height-integrated, \(q\)-and-\(\chi\)-averaged fourth
# moment of Dirichlet \(L\)-functions exist in the literature?

**Scope and a note on method.** This document answers the literature
question RANK3_QUARTIC_TOOLS.md Section 3 leaves open (its own "wall"): is
there a named, unconditional theorem bounding
\[
 J(X,Y)\ :=\ \sum_{q\le X}\ \sum_{\chi\bmod q}^*\ \int_{|t|\le Y}
 |L(\tfrac12+it,\chi)|^4\,dt
\]
with a genuine power-saving over the trivial Cauchy-Schwarz-from-the-
second-moment bound, as opposed to Heath-Brown's classical fixed-point
fourth moment (\(Y=0\))? **This document has no live literature-search tool
in this environment** — the same restriction RANK3_QUARTIC_TOOLS.md
Section 3 records — but unlike that document, it does not stop at
reporting the absence of a search capability. What follows draws on this
model's own training-time knowledge of the analytic-number-theory
literature (moments of \(\zeta\) and of Dirichlet \(L\)-functions
specifically), presented and cited as such, not as the output of a
verified database lookup. Exact constants and exponents recalled below
that this document is not fully confident of are flagged as such; the
qualitative shape of every result cited (which aspect it averages over,
which it fixes, and whether the saving is power-type or log-type) is
stated with much higher confidence than any specific numerical exponent,
and the negative conclusion below does not depend on getting any exponent
exactly right.

Notation is UPPER_BOUND.md's, RANK3_ROUTE_D.md's, and
RANK3_QUARTIC_TOOLS.md's: \(F_N,K_N,\Lambda,\mu,\phi\) as in
UPPER_BOUND.md Section 1; \(P_{q,a}=(\mu(q)/\phi(q))K_N(\cdot-a/q)\),
\(R_{q,a}=F_N-P_{q,a}\), \(Z_{(q)}=\sum_a^*\int_{I_{q,a}}|R_{q,a}|^4\) as in
UPPER_BOUND.md Section 6; \(Q=\lfloor\sqrt N/3\rfloor\), \(R_0=Q/L\),
\(L=\log N\), as throughout this hunt. To avoid colliding with the hunt's
own use of \(Q\), the \(L\)-function-side modulus cutoff and height cutoff
are written \(X,Y\) rather than \(Q,T\). This document assumes
RANK3_QUARTIC_TOOLS.md, RANK3_MEAN_VALUE_TOOLS.md, and RANK3_ROUTE_D.md as
already established and does not re-derive their identities or
conclusions; in particular it does not re-argue RANK3_ROUTE_D.md Section
7's finding that no arc-transfer exists for \(Z_{(q)}\), or
RANK3_QUARTIC_TOOLS.md Section 2's finding that \(Z_{(q)}\) does not
vanish on non-squarefree \(q\) — both are used as given.

## 1. What exists near this shape, and exactly how each falls short

Three genuinely different unconditional theorems live near \(J(X,Y)\).
None of them *is* \(J(X,Y)\); each averages over one of \(\{q,\chi\}\) and
\(t\) but not both, or averages over both but only at the second moment.

**(a) Fixed height (\(Y=0\)), \(q\)-and-\(\chi\)-averaged, fourth moment.**
This is the family RANK3_QUARTIC_TOOLS.md Section 3 already names:
Heath-Brown, "The fourth power mean of Dirichlet's \(L\)-functions,"
*Analysis* 1 (1981), 25–32, proves
\(\sum_{q\le X}\sum_\chi^*|L(\frac12,\chi)|^4\ll X^{2+\epsilon}\)
unconditionally. This was sharpened to a genuine asymptotic with a
power-saving error term by K. Soundararajan, "The fourth moment of
Dirichlet \(L\)-functions," in *Analytic Number Theory* (W. Duke and Y.
Tschinkel, eds.), Clay Mathematics Proceedings 7 (2007), for \(q\) prime,
and then by M. Young, "The fourth moment of Dirichlet \(L\)-functions,"
*Annals of Mathematics* 173 (2011), 1–50, which gives, for \(q\) prime, an
asymptotic formula with an explicit power-saving error term (this document
recalls the saving as of size \(q^{-1/80+\epsilon}\) below the main term;
it is not fully confident of this exact exponent, only that Young's paper
is the sharp unconditional q-aspect result and that its error term carries
a genuine, named power saving, not merely a log saving). Subsequent work
by other authors has extended the \(q\)-aspect fourth moment beyond prime
\(q\) (toward prime-power and more general moduli); this document does not
have a reliable, literature-verified list of that later work available in
this environment and does not need one for the conclusion below, since
none of it — to this document's knowledge — integrates over \(t\). **Every
member of this family fixes \(t\) at (or near) the central point and
averages only over the family \((q,\chi)\).**

**(b) Fixed modulus, \(t\)-integrated, fourth moment.** For \(\zeta(s)\)
itself (\(q=1\)): Ingham (1926) proves the leading-order asymptotic
\(\int_0^T|\zeta(\frac12+it)|^4\,dt\sim\frac1{2\pi^2}T(\log T)^4\).
Heath-Brown, "The fourth power moment of the Riemann zeta function,"
*Proc. London Math. Soc.* (3) 38 (1979), 385–422, supplies a power-saving
error term, \(O(T^{7/8+\epsilon})\), against the \(T(\log T)^4\) main
term. Y. Motohashi's spectral explicit formula for the fourth moment
(*Acta Math.* 170 (1993), 181–220, and the book *Spectral Theory of the
Riemann Zeta-Function*, Cambridge Tracts 127, 1997) expresses the error
term exactly as a sum over Maass cusp forms plus Eisenstein and residue
terms, and this — combined with further estimates on that spectral sum by
Ivić and others — sharpens the power-saving error term well below
Heath-Brown's \(7/8\) (this document recalls the improved exponent as
somewhere near \(2/3\), and does not commit to an exact value). The same
methods extend, for a single *fixed* Dirichlet character \(\chi\pmod q\)
with \(q\) fixed, to \(\int_{|t|\le T}|L(\frac12+it,\chi)|^4\,dt\sim
c(\chi)\,T(\log T)^4\) with a power-saving error term as \(T\to\infty\).
**Every member of this family fixes \(q\) (or \(\chi\)) and averages only
over the height \(t\); none of the sources this document recalls tracks
how the implied constant or the error term depends on \(q\) as \(q\to
\infty\) jointly with \(T\) — because none of them needed to, having fixed
\(q\) from the outset.**

**(c) Joint \((q,t)\)-averaged, but only the *second* moment.** The
classical (additive-dual) large sieve inequality for Dirichlet
polynomials, combined with the multiplicative (character) large sieve —
material in Montgomery and Vaughan, *Multiplicative Number Theory I*,
Chapter 7 and its notes, and in Iwaniec and Kowalski, *Analytic Number
Theory*, Chapter 7 (the large-sieve inequality for \(L\)-functions,
Theorem 7.34 and surrounding material) — does genuinely average jointly
over \(q\le X\), \(\chi\bmod q\), **and** \(t\in[-Y,Y]\), giving a bound
of shape
\[
 \sum_{q\le X}\sum_\chi^*\int_{|t|\le Y}|L(\tfrac12+it,\chi)|^2\,dt
 \ \ll\ (X^2+Y)(XY)^\epsilon
\tag{G1}
\]
(the precise shape of the right side varies by source and by how the
approximate functional equation is truncated; this document states it
schematically rather than claiming one exact citation-level form). This is
the *second*-moment analogue of what RANK3_MEAN_VALUE_TOOLS.md Section 6
already priced for (BDH) against \(U_{(q)}\), applied here in the
\(L\)-function variable rather than the arithmetic-progression variable —
the same underlying mechanism (the character large sieve), the same
moment order (two), the same limitation already on record: **it is a
second moment, and RANK3_ROUTE_D.md Section 7 already shows \(Z_{(q)}\)
does not reduce to a second-moment-type quantity, structurally, the way
\(U_{(q)}\) does.**

## 2. None of (a), (b), (c) composes into a genuine joint fourth moment

This is the substantive negative finding, and it does not rest on any
single exponent recalled above.

- **(a) and (c) cannot be combined to integrate over \(t\).** (a) says
  nothing at all about \(t\ne0\) — it is not a statement with a "\(t\)"
  parameter that could be widened, it is a theorem about the single point
  \(t=0\), proved (in Young's case) by a delicate shifted-convolution /
  spectral argument specific to that point. There is no way to substitute
  a range of \(t\) into (a) and recover a joint theorem; doing so would
  require redoing the proof with \(t\) as a new free parameter, which
  neither this document nor (to its knowledge) any published paper does.
- **(b) and (c) cannot be combined to average over \(q\).** Symmetrically,
  (b)'s implied constants and error terms are proved for one fixed
  character (or \(q=1\)); nothing in the cited sources tracks their
  dependence on \(q\) well enough to sum over \(q\le X\), \(\chi\bmod q\)
  afterward. Summing an untracked-in-\(q\) bound over \(\asymp X^2\)
  characters gives no bound at all, not merely a weak one.
- **Composing via Cauchy-Schwarz reproduces exactly the excluded trivial
  bound.** The one route that genuinely does combine all three aspects at
  once is: bound the fourth moment by \(\sup_{|t|\le Y}|L(\tfrac12+it,
  \chi)|^2\) times the second moment (c). The supremum is controlled
  unconditionally only by the convexity bound (functional equation plus
  Phragmén-Lindelöf), \(L(\tfrac12+it,\chi)\ll(q(1+|t|))^{1/4+\epsilon}\)
  — this is *precisely* "the trivial (Cauchy-Schwarz via the second
  moment) bound" the assignment names and asks for something beating, not
  a candidate for beating it. Nothing in (a), (b), or (c) supplies a
  sub-convexity bound uniform enough, or a genuinely joint fourth-moment
  argument, to do better.

**Finding.** To this document's knowledge, and subject to the caveat in
the Scope paragraph above about the absence of a live literature search in
this environment, **no unconditional theorem of the shape \(J(X,Y)\), with
a genuine power-saving over the trivial bound and uniform jointly in \(X\)
and \(Y\), is established in the literature.** This is not "no such
theorem could exist" — nothing here rules that out — it is "this document,
using the specific published results it can name and their specific
proof mechanisms, finds none, for a reason that is about how those proofs
work (each is built to exploit cancellation in exactly one aspect,
Section 2 above) and not only about a citation gap."

## 3. What would need to exist, stated precisely

A tool that could actually help \(Z_{(q)}\) would have to be a single
theorem — not a composition of (a), (b), (c) — proving, for some
\(\delta>0\),
\[
 J(X,Y)=\sum_{q\le X}\sum_\chi^*\int_{|t|\le Y}|L(\tfrac12+it,\chi)|^4\,dt
 \ \ll\ (\text{main term})+O\big((X^2Y)^{1-\delta+\epsilon}\big),
\]
uniformly in both \(X\) and \(Y\) simultaneously, by a method that
genuinely exploits cancellation across the family \((q,\chi,t)\) as one
object — for instance a spectral (Motohashi-type) explicit formula
extended to also average over the character aspect (rather than fixing
\(\chi\) as (b) does), or a shifted-convolution argument in the style of
Young's proof of (a) but with the approximate-functional-equation length
allowed to grow with \(Y\) as well as \(X\) (rather than fixing \(Y=0\) as
(a) does). This document does not find such a method named anywhere in
the sources it can cite, and regards producing one as a research-level
open problem in its own right — combining a shifted-convolution / spectral
argument across two aspects simultaneously is exactly the kind of step
that has historically taken a specialized paper (occasionally a career) per
single aspect (compare the twenty-five years and several papers between
Heath-Brown (1981) and Young (2011) for (a) alone, or between Ingham
(1926) and Motohashi (1993) for (b) alone) — not a reason by itself to
believe it is false or impossible, but a reason this document does not
expect to find it simply by looking harder in the same places.

**A further uniformity mismatch, independent of existence.** Even granting
such a theorem, what \(Z_{(q)}\) needs is not a single \(J(X,Y)\) at one
pair \((X,Y)\), but a *\(q\)-dependent* height cutoff: the arc \(I_{q,a}\)
has half-width \(\asymp Q/(qN)\) in the frequency variable \(\beta\), which
the standard explicit-formula heuristic (the same one RANK3_QUARTIC_TOOLS.md
Section 3 invokes to reach \(J\) at all) translates to a height range
\(T_q\asymp Q/q\) that *shrinks* as \(q\) grows, reaching \(T_q\asymp L\) at
\(q=R_0\). A tool for \(Z_{(q)}\) would need the joint theorem uniform down
to these small, \(q\)-dependent height windows — an extra uniformity
requirement on top of joint existence, of the same character as the one
RANK3_MEAN_VALUE_TOOLS.md Section 5 flags for (BV) (uniform down to small
\(q\) is not automatic just because a theorem is stated "for \(q\) up to
some large range"). None of (a), (b), (c) above, nor the hypothetical
theorem just described, is normally stated with this kind of down-to-\(O(1)\)
uniformity in the height variable; the classical \(t\)-aspect theorems (b)
are asymptotic statements as \(T\to\infty\) for *fixed* other parameters,
not results proved to be sharp or even nontrivial at bounded \(T\).

## 4. Squarefree restriction and the arc-transfer: both remain separate gaps

**Squarefree restriction.** Nothing about the character-sum machinery
underlying (a), (b), or the hypothetical joint theorem in Section 3 is
intrinsically restricted to squarefree \(q\): \(\sum_\chi^*\) (primitive
characters mod \(q\)) is a well-defined sum for every \(q\ge1\), and the
classical theorems in family (a) are proved for prime \(q\) (trivially
squarefree) with extensions toward more general — not necessarily
squarefree — moduli by later authors, as noted in Section 1. So a
hypothetical joint theorem of the shape in Section 3 is not structurally
barred from covering non-squarefree \(q\), unlike a Möbius/Ramanujan-sum
weighted tool of the kind (D7)/(D11) use for \(U_{(q)}\), which is
squarefree-supported by construction (RANK3_ROUTE_D.md Section 4). This
matters because of RANK3_QUARTIC_TOOLS.md Section 2's finding: for
non-squarefree \(q\), \(P_{q,a}\equiv0\) and \(R_{q,a}=F_N\) identically,
so \(Z_{(q)}\)'s non-squarefree part is the fourth moment of \(F_N\)
itself with no bias-subtraction — translated through the explicit formula
near \(a/q\), this is still governed by the full character group mod
\(q\) (primitive and imprimitive characters both contribute to
\(\psi(t;q,b)\)'s decomposition regardless of \(\mu(q)\)), so a joint
theorem covering general \(q\) is not structurally mismatched to this
part the way a squarefree-only tool would be. This is a genuine
"good news" observation relative to \(U_{(q)}\)'s situation, but it is
conditional on Section 3's hypothetical theorem existing at all, which
Section 2 already finds it does not.

**Arc-transfer.** This document does not find, in any of (a), (b), (c),
or in the general shape of how fourth-moment theorems for \(L\)-functions
are normally proved, anything resembling an arc-transfer argument. This is
not a gap specific to \(Z_{(q)}\)'s literature search — moment theorems
for \(L\)-functions are not usually proved through a minor-arc/major-arc
circle-method dissection at all; they bound an integral or sum over the
whole critical line (or a whole dyadic range of \(t\)), with no
counterpart to "the arc-restricted piece versus the full-circle piece"
that RANK3_ROUTE_D.md Section 7 shows is missing for \(Z_{(q)}\).
Consequently, even a fully successful proof of the hypothetical theorem in
Section 3 would still need RANK3_ROUTE_D.md Section 7's transfer step
supplied from *elsewhere* — this document confirms, from the
\(L\)-function-moment side rather than re-deriving RANK3_ROUTE_D.md's own
argument, that the transfer step is not something this literature
supplies either, so it remains **a second, independent gap on top of
Section 3's existence gap, not one this document narrows.**

## 5. Pricing: why there is no power of \(N\) to report

RANK3_MEAN_VALUE_TOOLS.md Section 5 priced (BDH) against \(U_{(q)}\) by
taking a real, citable theorem with a known explicit strength and pushing
it through the identity, landing at a concrete order (\(N^{5/2}\)). That
exercise requires an actual theorem to push through. Section 2 above finds
none exists for \(J(X,Y)\), and Section 2's three bullet points explain,
mechanism by mechanism, why (a), (b), and (c) cannot be substituted for
one — not merely that each individually falls short by some tracked
factor, the way (BV) and (BDH) individually did for \(U_{(q)}\) in
RANK3_MEAN_VALUE_TOOLS.md Sections 2–5. There is consequently no
computation of the shape "(E1)–(E2)" in RANK3_MEAN_VALUE_TOOLS.md Section
5 to perform here: composing (a), (b), (c) does not yield a bound smaller
than the trivial one at all (Section 2's third bullet), so there is no
non-trivial exponent of \(N\) to extract and compare against CHHL's
\(N^{5/2}\) benchmark. The honest content of the pricing step, for this
route, is that it returns **exactly the trivial bound already on record**
(the same \(O(N^3)\)-type ceiling UPPER_BOUND.md's unconditional Theorem
(1) already supplies, and which RANK3_QUARTIC_TOOLS.md Section 2's direct
measurement of \(Z^*_{(q)}\) shows is not visibly beaten by anything
checked so far) — not a bound that falls short by a specific, nameable
amount the way (BDH)'s route did for \(U_{(q)}\).

## 6. Where this leaves rank 3's fourth moment

Combined with RANK3_QUARTIC_TOOLS.md and RANK3_ROUTE_D.md Section 7:

- No named unconditional theorem for the height-integrated,
  \(q\)-and-\(\chi\)-averaged fourth moment \(J(X,Y)\) is found (Sections
  1–2), and the obstruction is structural (each nearby known theorem is
  built to exploit exactly one aspect) as well as a citation gap.
- What such a theorem would need to look like, and why it is a
  research-level open problem rather than an assembly of known pieces, is
  stated precisely in Section 3, including a further joint-uniformity
  requirement (down to \(q\)-dependent, shrinking height windows
  \(T_q\asymp Q/q\)) that is not automatic even granting existence.
- A hypothetical such theorem would **not** be structurally barred from
  covering \(Z_{(q)}\)'s non-squarefree part (Section 4, first half) —
  unlike a Möbius-weighted tool — but this is moot given Section 2's
  finding that no such theorem exists to begin with.
- The arc-transfer gap RANK3_ROUTE_D.md Section 7 already identifies is
  confirmed, from the \(L\)-function-moment literature's side, to be a
  second, independent gap that this route does not supply either (Section
  4, second half).
- There is no power of \(N\) better than the trivial bound to report
  (Section 5): this route, unlike the (BDH) route RANK3_MEAN_VALUE_TOOLS.md
  priced for \(U_{(q)}\), does not reach CHHL's \(N^{5/2}\) benchmark or
  any other named order strictly between the trivial bound and the target
  \(N^{2+\epsilon}\); it reaches the trivial bound and stops there.

This document is a literature-landscape argument, built from this model's
own training-time knowledge of moments of \(\zeta\) and of Dirichlet
\(L\)-functions rather than a live-verified search (flagged plainly in the
Scope paragraph and not hidden in any of the citations above), together
with one piece of exact structural reasoning (Section 4, first half, on
why squarefreeness is not an intrinsic barrier to a hypothetical joint
theorem) that follows directly from UPPER_BOUND.md's own definitions and
RANK3_QUARTIC_TOOLS.md Section 2. It assumes and establishes nothing about
zeros of \(L\)-functions or the Riemann Hypothesis, and does not weaken
the definitions of \(Z_{(q)}\), \(R_0\), or any quantity in
UPPER_BOUND.md.
