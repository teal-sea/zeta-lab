# Does the Siegel-Walfisz argument split, at small denominators, into separate bounds for \(U_Q\) and \(Z_Q\)?

This is a derivation check on a polylog-sized range of denominators, not a
proof attempt and not a claim about RH. It does not close rank 3 of the doors
table (RESULTS.md, "The doors"; priced in RANK3_SCOPE.md), because the range
it reaches, \(2\le q\le\lfloor L^B\rfloor\) for a fixed \(B\), is a bounded
power of \(\log N\), while rank 3 runs up to \(R_0\sim N^{1/2}/(3L)\), a
positive power of \(N\). RANK3_SCOPE.md Section 2 already states this gap in
one line ("(17) covers only a vanishing initial segment of \(2\le q\le R_0\),
and Section 6 does not attempt even that"); this document is exactly that
attempt, worked out on the segment RANK3_SCOPE.md left untried, and it finds
a split answer: yes for the mixed moment, no for the fourth moment, and the
reason for the split is structural, not a matter of pushing the same
computation harder.

## 1. Which two objects, at which radius

UPPER_BOUND.md Section 3, equation (7), defines the arcs \(I_{q,a}\) and their
radius \(\delta_q=Q/(qN)\) in terms of a parameter \(Q\) chosen once per
section. Section 5 sets \(Q=\lfloor L^B\rfloor\) for a fixed \(B\), proves
(17) uniformly for \(q\le Q\) on exactly these arcs, and closes (19). Section
6 then **resets** \(Q=\lfloor\sqrt N/3\rfloor\) and defines \(U_Q\), \(Z_Q\)
(just before (23)) as sums over the arcs \(I_{q,a}\) at *this* wider \(Q\).
The same letter \(Q\) names two different radii; the task at hand is to check
whether the narrow-arc estimate (17)-(19) can be spliced onto the wide-arc
objects \(U_Q\), \(Z_Q\), restricted to \(q\le L^B\), and following the
document's own notation convention for restricting these sums by denominator
range (\(U_{q>R_0}\) in (26), \(Z_{q>R_0}\) in (28)), write
\[
 U_{2\le q\le L^B}=\sum_{2\le q\le L^B}\sum_a^*\int_{I_{q,a}}|P_{q,a}|^2|R_{q,a}|^2,
\qquad
 Z_{2\le q\le L^B}=\sum_{2\le q\le L^B}\sum_a^*\int_{I_{q,a}}|R_{q,a}|^4,
\]
with \(I_{q,a}\) the **wide** (square-root) arc, radius \(\sqrt N/(3qN)\).

This choice of reading matters, and the alternative is worth ruling out
explicitly. If instead \(U_{2\le q\le L^B}\), \(Z_{2\le q\le L^B}\) meant the
same sums over the **narrow** arcs (radius \(L^B/(qN)\), Section 5's own
arcs), the question would already be answered: that is exactly the
computation Section 5 performs to reach (19), since (18) integrated over
those arcs with the pointwise bound from (17) *is* the proof of (19), and
splitting it into a \(P^2R^2\) piece and an \(R^4\) piece changes nothing
about the two terms already displayed there (Section 3 below reproduces
this). Reading the question that way would make it a restatement of work
already in the text. The wide-arc reading is the one that says something new,
because \(U_Q\), \(Z_Q\) at \(Q=\lfloor\sqrt N/3\rfloor\) are the objects
Section 6 and (23) actually use, and (17) was never proved on arcs that wide.
The rest of this document uses the wide-arc reading.

For \(2\le q\le L^B\), since \(L^B=o(\sqrt N)\) for every fixed \(B\), the
narrow arc sits strictly inside the wide arc at the same center: writing
\(J_{q,a}=\{\beta:|\beta|\le L^B/(qN)\}\) for the piece (17) controls,
\(J_{q,a}\subset I_{q,a}\) for all large \(N\). Split each wide-arc integral
into the core \(J_{q,a}\) and the leftover annulus \(I_{q,a}\setminus
J_{q,a}\); this is an exact decomposition of the same integrand over a
disjoint union of domains, not an approximation. The rest of this note bounds
each piece.

## 2. The core: (17)-(18) reproduce (19)'s two terms, separately, for free

On \(J_{q,a}\), (17) gives \(R_{q,a}(\beta)=F_N(a/q+\beta)-P_{q,a}(\beta)
=O_{B,H}(NL^{-H})\), uniformly in \(q\le L^B\), \(a\), and \(\beta\in
J_{q,a}\), for every fixed \(H\). This bounds \(P_{q,a}^2R_{q,a}^2\) and
\(R_{q,a}^4\) directly, without needing (18) at all — (18) is only needed
once \(R_{q,a}\) is *not* already small, which is the annulus's problem,
handled in Section 3:
\[
 \int_{J_{q,a}}|P_{q,a}|^2|R_{q,a}|^2\ll_{B,H}N^2L^{-2H}\int_{I_{q,a}}|P_{q,a}|^2,
\qquad
 \int_{J_{q,a}}|R_{q,a}|^4\ll_{B,H}N^4L^{-4H}|J_{q,a}|.
\]
Summing over \(2\le q\le L^B\), \(a\), using \(\sum_{q,a}\int_{I_{q,a}}|P_{q,a}|^2
\ll N\log(2L^B)\) (the estimate right before (19), restricted to \(q\ge2\))
and \(\sum_{q,a}|J_{q,a}|\ll(L^B)^2/N\) (the arc-disjointness bound of
Section 3, applied at the narrow radius) gives
\[
 U^{\rm core}_{2\le q\le L^B}\ll_{B,H}N^3L^{-2H}\log(2L^B),\qquad
 Z^{\rm core}_{2\le q\le L^B}\ll_{B,H}N^3L^{2B}L^{-4H}.
\]
These are exactly the two terms of (19) (with \(Q=L^B\)), separated rather
than added — unsurprising, since (19) is proved by exactly this pointwise
bound on \(R_{q,a}\), and \(8U_Q+2Z_Q\ge M_Q\) is how (18) turns a bound on
\(R\) into a bound on \(M_Q\) in the first place. So on the core alone,
nothing is lost or gained by separating: the two pieces of (19) already *are*
separate bounds for (narrow-arc) \(U\) and \(Z\). The open question is only
the leftover annulus.

## 3. The annulus for \(U\): survives, using \(P\)'s own decay

On the annulus, (17) does not apply, so \(R_{q,a}=F_N-P_{q,a}\) must be
bounded via (18)'s style split \(|R_{q,a}|^2\le2|F_N|^2+2|P_{q,a}|^2\) (the
same elementary step used before (25)), giving
\[
 U^{\rm ann}_{2\le q\le L^B}\le2\sum_{q,a}\int_{\rm ann}|P_{q,a}|^2|F_N|^2
 +2\sum_{q,a}\int_{\rm ann}|P_{q,a}|^4 .
\]
Two ingredients are available, both already in the text. First, Vaughan's
(V) applies on the whole wide arc \(I_{q,a}\) for \(q\le L^B\) (its
hypothesis \(|\alpha-a/q|\le q^{-2}\) holds since \(\sqrt N/(3qN)\le q^{-2}\)
once \(q\le3\sqrt N\), true here), and for \(q\) as small as a fixed power
of \(L\), its dominant term is \(Nq^{-1/2}\) (the other two terms are smaller
by a positive power of \(N\) once \(q\ll N^{2/5}\), which \(L^B\) certainly
is), so \(\sup_{I_{q,a}}|F_N|\ll Nq^{-1/2}L^{5/2}\), *depending on* \(q\).
Second, the elementary kernel bound \(|K_N(\beta)|\le\min(N,(2\|\beta\|)^{-1})\)
already used for \(H_Q\) in Section 4 gives, by direct integration from the
inner radius \(L^B/(qN)\) outward,
\[
 \int_{\rm ann}|K_N|^2\ll qN/L^B,\qquad\int_{\rm ann}|K_N|^4\ll(qN/L^B)^3,
\]
hence \(\int_{\rm ann}|P_{q,a}|^2\ll qN/(\phi(q)^2L^B)\) and
\(\int_{\rm ann}|P_{q,a}|^4\ll q^3N^3/(\phi(q)^4L^{3B})\), term by term in
\(q\), not merely on average.

Combining the \(q\)-dependent sup from (V) with the \(q\)-dependent kernel
tail, term by term:
\[
 \int_{\rm ann}|P_{q,a}|^2|F_N|^2\ll(Nq^{-1/2}L^{5/2})^2\cdot
 \frac{qN}{\phi(q)^2L^B}=\frac{N^3L^{5-B}}{\phi(q)^2}.
\]
Summing over \(a\) (\(\phi(q)\) terms) and then \(q\le L^B\), using
\(\sum_{q\le x}1/\phi(q)\ll\log x\), gives \(\sum_{q,a}\int_{\rm ann}|P|^2|F_N|^2
\ll N^3L^{5-B}\log L\). The \(P^4\) term is smaller (it inherits a full
\(L^{-3B}\) from the kernel tail against a bounded-average-order sum
\(\sum_q(q/\phi(q))^3\ll L^B\), net \(\ll N^3L^{-2B}\)). So
\[
 U^{\rm ann}_{2\le q\le L^B}\ll_B N^3L^{5-B}\log L .
\]
This **shrinks as \(B\) grows**, because both ingredients that produced it —
Vaughan's \(q^{-1/2}\) decay and the kernel's tail decay from the inner
radius \(L^B/(qN)\) — respond to how far out the good core reaches. Combined
with the core bound of Section 2, for every target saving \(H'>0\), first
fix \(B\) large enough that \(N^3L^{5-B}\log L\ll N^3L^{-2H'}\), then fix any
\(H\ge H'\) so the core term is at least as small: this gives
\[
 U_{2\le q\le L^B}\ll_{H'}N^3L^{-2H'+o(1)}\quad\text{for every fixed }H'>0,
\]
matching, up to the \(\log L\) bookkeeping, the strength (19) reaches for
the combined \(M_Q\) at \(Q=L^B\). **The mixed moment survives the splice.**

## 4. The annulus for \(Z\): does not survive, and cannot be pushed through by raising \(B\)

The same attempt for \(Z\) fails, and fails for a reason that does not go
away as \(B\to\infty\). Write \(|R_{q,a}|^4\le8(|F_N|^4+|P_{q,a}|^4)\) (the
step used before (28)). The \(P^4\) piece is the same small term as above,
\(\ll_B N^3L^{-2B}\)-type. The \(F_N^4\) piece is the obstruction:
\[
 \sum_{q,a}\int_{\rm ann}|F_N|^4\le\Big(\sup_{\mathbb T}|F_N|\Big)^2
 \sum_{q,a}\int_{\rm ann}|F_N|^2\le\Big(\sup_{\mathbb T}|F_N|\Big)^2\int_{\mathbb T}|F_N|^2,
\]
using that the annuli for distinct \((q,a)\) are disjoint (Section 3) to
replace their union by the whole circle. Both factors on the right are
already in the text: \(\sup_{\mathbb T}|F_N|\le\psi(N)\ll N\) trivially
(Chebyshev, valid everywhere, and for these small, fixed \(q\) this is at
least as good as (V), whose first term \(Nq^{-1/2}L^{5/2}\) carries an extra
\(L^{5/2}\) that the trivial bound does not), and
\(\int_{\mathbb T}|F_N|^2=d_N\ll NL\) (used already before (20)). So
\[
 \sum_{q,a}\int_{\rm ann}|F_N|^4\ll N^2\cdot NL=N^3L.
\]
This bound involves neither \(B\) nor \(H\): the trivial sup and the total
\(L^2\) mass \(d_N\) are both fixed quantities that do not know where the
SW-good core ends. Raising \(B\) pushes the core further out and shrinks the
*width* of the annulus, but neither ingredient used to bound the annulus's
\(F_N^4\) content responds to that width — the sup bound is pointwise and
the \(d_N\) bound is a bulk total over the *entire* circle, not something
that shrinks as the excluded core grows. So
\[
 Z^{\rm ann}_{2\le q\le L^B}\ll N^3L,\qquad\text{for every fixed }B,
\]
and this is the governing term: it is not \(o(N^3L^{-2H})\) for any \(H>0\),
so it does not match (19)'s strength, and no larger choice of \(B\) repairs
it. **The fourth moment does not survive the splice.**

## 5. Why the two moments split apart

The mixed moment has one leg, \(P_{q,a}\), that is a fully explicit function
(a normalized Dirichlet kernel), so its mass on any sub-region of an arc —
in particular the annulus outside the SW-good core — is computable directly
from \(|K_N(\beta)|\le\min(N,(2\|\beta\|)^{-1})\), the same elementary
estimate Section 4 already uses for \(H_Q\), and that mass decays as a
negative power of the core's own radius \(L^B/(qN)\): raising \(B\) shrinks
it as fast as wanted. The fourth moment's leading term has *no* such leg:
both factors of \(|F_N|^4\) are the unknown arithmetic object itself, and the
only tools on hand for it outside the SW-good zone are a pointwise bound
(Vaughan's (V), which Section 6 and RANK3_SCOPE.md Section 2 both note is no
better than trivial at fixed small \(q\)) and a bulk \(L^2\)-mass identity
(\(d_N\)) that is not localized to any particular range of \(q\). Multiplying
the best pointwise bound by the best bulk bound gives a number that cannot
see \(B\) at all. This is the same asymmetry Section 7 already exhibits at
\(q=1\): \(U_1\) has an exact convolution/Parseval identity (29) turning it
into \(\sum\Delta(t)^2\), which (SW) then bounds by \(O_H(N^3L^{-2H})\); no
analogous identity or bound is exhibited anywhere in UPPER_BOUND.md or
RANK3_SCOPE.md for a \(Z\)-side object at \(q=1\) or at any \(q\ge2\). The
computation above is the same gap, one layer further out.

## 6. What this does and does not settle

The splice of (17)-(19) onto Section 6's wide-arc moments, restricted to
\(2\le q\le L^B\) for a fixed \(B\), gives a separate bound for \(U\)
matching (19)'s strength (choosing \(B\) as large as the target saving
requires), and fails to give any useful separate bound for \(Z\) — the best
bound reached here for \(Z\), \(O(N^3L)\), exceeds \(N^3\), let alone the
\(O_\epsilon(N^{2+\epsilon})\) that (23) would need. Both conclusions rest
only on tools already present in UPPER_BOUND.md Sections 3-6: (17), (18),
(V), the kernel estimate before (13), and Parseval; nothing here assumes a
stronger unconditional input than the source text already uses.

This does not close rank 3. Even the successful half, for \(U\), reaches
only \(2\le q\le L^B\), a fixed power of \(\log N\), against rank 3's full
range up to \(R_0\sim N^{1/2}/(3L)\) — a vanishing fraction of it, in the
sense RANK3_SCOPE.md Section 2 already names. It also does not move the
total bound (23), independent of that range gap: RANK3_SCOPE.md Section 4
shows rank 1's own reached strength, \(O_H(N^3L^{-2H})\) for the \(q=1\)
term \(U_1\), already caps what (23) can reach, and the \(U\)-bound reached
here is of that same order, so closing it changes nothing about the sum.
Nothing here bears on RH.
