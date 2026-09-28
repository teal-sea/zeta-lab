# Rank 3's polynomial range, probed: \(\lfloor L^B\rfloor<q\le R_0\)

This is an investigation, not a proof attempt, of one sub-question
RANK3_SCOPE.md leaves open. RANK3_SCOPE.md Section 2 shows that none of the
three tools UPPER_BOUND.md assembles — Siegel-Walfisz (17), Vaughan's bound
(V), the additive large sieve (LS) used dyadically in (24)-(26) — reaches
\(U_{(q)}\), \(Z_{(q)}\) at a useful strength anywhere in \(2\le q\le R_0\).
The question here is narrower and specific: for \(\lfloor L^B\rfloor<q\le
R_0\), any *fixed* \(B\) (so this excludes both the tiny range (17) already
reaches and the range near \(q=1\) that RANK3_SCOPE.md treats as tied to rank
1), is there **some other** unconditional estimate — a different large-sieve
weighting, a different arc-splitting by denominator, or a different tool
altogether — that bounds \(U_{(q)}\), \(Z_{(q)}\) summed or maxed over this
range?

Two things are brought in below that are not in UPPER_BOUND.md or
RESULTS.md: the Bombieri–Vinogradov theorem and the Barban–Davenport–
Halberstam theorem (BDH), both classical, unconditional, standard results
about primes in arithmetic progressions on average over the modulus. Neither
name occurs in either source document (checked directly). Everything else —
the definitions of \(U_{(q)}\), \(Z_{(q)}\), \(P_{q,a}\), \(R_{q,a}\), the
identity (29)-(30) at \(q=1\), and the estimates (13)-(28) — is taken as
already established there and used, not re-derived. This document has no
access to outside literature beyond what its author already knows; where
that knowledge runs out, it says so rather than guessing a citation.

## 1. Two readings of the question, and why they are not the same

\(U_Q=\sum_{q\le Q}U_{(q)}\), \(Z_Q=\sum_{q\le Q}Z_{(q)}\) exactly, by
disjointness of the arcs (RANK3_SCOPE.md Section 1). What (23) actually needs
is the **sum**
\[
 S_U(B)=\sum_{\lfloor L^B\rfloor<q\le R_0}U_{(q)},\qquad
 S_Z(B)=\sum_{\lfloor L^B\rfloor<q\le R_0}Z_{(q)},
\tag{P.1}
\]
bounded by \(O_\epsilon(N^{2+\epsilon})\); nothing in (23) needs any
individual \(U_{(q)}\) or \(Z_{(q)}\) bounded on its own. A bound on
\(\max_{\lfloor L^B\rfloor<q\le R_0}U_{(q)}\) would imply a bound on
\(S_U(B)\) only after multiplying by the range length \(R_0\), which is far
too lossy to be useful; so the max-reading is a strictly harder question than
what (23) needs, and the two get different answers below. Both are asked
because the assignment names both.

## 2. The current decomposition already spends a full power of \(N\) on a term neither large sieve nor Vaughan is asked to touch

Both (25) (for \(U\)) and (28) (for \(Z\)) bound \(|R_{q,a}|^2\) or
\(|R_{q,a}|^4\) by expanding the triangle inequality: \(|R_{q,a}|^2\le
2|F_N|^2+2|P_{q,a}|^2\), \(|R_{q,a}|^4\le8(|F_N|^4+|P_{q,a}|^4)\). Both
expansions produce a term built from \(P_{q,a}\) alone, with no \(F_N\) in
it — a term that is not RANK3_SCOPE.md's "tool" question at all, since no
estimate for the prime-counting side is needed to bound it: it is a fact
about \(K_N\). Here is its size in this range, computed directly from what
(13)-(16) already establish, with no import.

**Lemma.** For every arc \(I_{q,a}\) in the construction (7) (i.e. for every
\(q\le Q\)),
\[
 \int_{I_{q,a}}|K_N(\beta)|^4\,d\beta=\Theta(N^3),
\tag{P.2}
\]
with absolute implied constants.

*Proof.* Upper bound: \(|K_N(\beta)|\le\min(N,(2\|\beta\|)^{-1})\), and
\(\delta_q\ge1/N\) always since \(Q\ge1\), \(q\le Q\). Split the arc at
\(|\beta|=1/N\):
\[
 \int_{I_{q,a}}|K_N|^4\,d\beta
 \le2\int_0^{1/N}N^4\,d\beta+2\int_{1/N}^{\delta_q}(2\beta)^{-4}\,d\beta
 =2N^3+\tfrac1{24}(N^3-\delta_q^{-3})\le\tfrac{49}{24}N^3.
\]
Lower bound: for \(|\beta|\le1/(2N)\), \(|N\beta|\le1/2\) so
\(|K_N(\beta)|=|\sin(\pi N\beta)/\sin(\pi\beta)|\ge(2/\pi)N\cdot(1-O(1/N))\)
for \(N\) large (the sine-ratio ranges between \(1\) at \(\beta=0\) and
\(\sin(\pi/2)/(\pi/2)=2/\pi\) at the endpoint, and \(\sin(\pi\beta)\ge2\beta\)
here); hence \(\int_{|\beta|\le1/(2N)}|K_N|^4\,d\beta\ge c\,N^3\) for an
absolute \(c>0\) and all large \(N\), and \(1/(2N)\le\delta_q\) always. \(\square\)

Consequently, for every \(q\), summing the self-term over the \(\phi(q)\)
reduced residues,
\[
 \sum_a\int_{I_{q,a}}|P_{q,a}|^4=\frac{\mu(q)^2}{\phi(q)^3}\cdot\Theta(N^3).
\tag{P.3}
\]
(The extra \(\phi(q)^{-1}\) against (P.2)'s \(\phi(q)^{-4}\) comes from
summing \(\phi(q)\) equal terms.) Summing over the target range and using
(15), \(1/\phi(q)\le\zeta(2)(1+\log q)/q\), so \(1/\phi(q)^3\ll(1+\log
q)^3/q^3\):
\[
 \sum_{\lfloor L^B\rfloor<q\le R_0}\frac{\mu(q)^2}{\phi(q)^3}
 \ll\sum_{q>L^B}\frac{(1+\log q)^3}{q^3}
 =O_\epsilon(L^{-2B+\epsilon})\quad\text{for every }\epsilon>0,
\tag{P.4}
\]
(the tail of a convergent series with an \((1+\log q)^3\ll_\epsilon
q^\epsilon\) bound absorbed). So the self-term contributes
\[
 O_\epsilon(N^3L^{-2B+\epsilon})
\tag{P.5}
\]
to \(S_U(B)\) and (with a larger absolute constant) to \(S_Z(B)\), for every
fixed \(B\) and every \(\epsilon>0\). This is not small in the sense (23)
needs: it is \(N^3\) with an arbitrary but *fixed* log-power discount, never
a saving of any power of \(N\) — the same shape as rank 1's own reached
bound \(O_H(N^3L^{-2H})\) (UPPER_BOUND.md Section 7). **This piece of the
existing decomposition, alone, already exceeds the \(N^{2+\epsilon}\) target
throughout the polynomial range, for every fixed \(B\), before any large
sieve or Vaughan estimate is applied to the cross term.** No tool named in
UPPER_BOUND.md is aimed at this term — (24)-(28) are all applied to the
\(F_N\)-side, not the \(P_{q,a}\)-side — and none is needed to see that it
fails here: (P.2) is a fact about \(K_N\) alone.

## 3. Running the cited large-sieve argument itself down to \(q=\lfloor L^B\rfloor\)

Section 2 leaves open whether some other splitting of (24)-(26) could do
better on the cross term even though the self-term already fails; the
answer does not depend on that, but it is worth recording that the cited
tool, run as far as it goes, does not either. RANK3_SCOPE.md Section 2
computes that the single dyadic block \(R=1\) (\(q=2\)) already costs
\(O(N^3L^3)\) via (25). The same telescoping argument that proves (26), applied to the blocks
\(R=2^j\lfloor L^B\rfloor\), \(j=0,1,2,\dots\), up to \(R_0\) instead of
starting at \(R_0\), sums the per-block bound (25),
\(U_{R<q\le\min(2R,Q)}\ll w(Q)^2N^3L/R^2\), over this geometric sequence of
blocks. Since the terms decay geometrically in \(j\), the sum is dominated
by its first term, and using \(w(Q)\ll L\) by (15),
\[
 \sum_{\lfloor L^B\rfloor<q\le R_0}U_{(q)}
 \ll w(Q)^2N^3L\sum_{j\ge0}(2^j\lfloor L^B\rfloor)^{-2}
 \ll w(Q)^2N^3L^{1-2B}
 \ll N^3L^{3-2B},
\tag{P.6}
\]
exactly the mechanism RANK3_SCOPE.md's Section 2 identifies for the single
block at \(q=2\), run one level further down instead of stopping at \(q=2\). So the cited tool, pushed as
far into the polynomial range as it will go, gives the same order as
Section 2's finding above: \(O(N^3L^{3-2B})\), a fixed log-power saving off
\(N^3\) and no saving of any power of \(N\), for every fixed \(B\). Extending
the dyadic descent past \(R_0\) is not blocked by anything specific to
\(R_0\) — \(R_0\) was chosen for the \(q>R_0\) regime, not because the
argument breaks at that point — but it does not reach the target either,
for the identical reason (P.5) does not.

Both (P.5) and (P.6) hold throughout the whole range \(\lfloor
L^B\rfloor<q\le R_0\), not only near its lower edge: the dyadic sum in
(P.6) and the tail sum in (P.4) are each dominated by their term at
\(q\approx L^B\) regardless of where the range's upper endpoint (\(R_0\) or
\(Q\)) is placed, since the summands decay geometrically (or as a
convergent power series) in \(q\). So neither finding is an artifact of
stopping at \(R_0\); raising the upper cutoff would not change either
order.

## 4. A cheap, unconditional fact about the whole fourth moment, and why it does not help \(Z\) either

For \(Z\), one might hope to avoid (28)'s weak point — Vaughan's \(N^{4/5}\)
term, which RANK3_SCOPE.md Section 2 shows is at its worst on exactly the
lower part of this range — by bounding \(\sum_a\int_{I_{q,a}}|F_N|^4\)
directly, the way (24)-(25) bound \(\sum_a\int_{I_{q,a}}|F_N|^2\) via (LS),
rather than through Vaughan's pointwise sup. This does not obviously help,
for an elementary reason independent of any large sieve or zero estimate.
Writing \(r(m)=\sum_{1\le n\le N-1}\Lambda(n)\Lambda(m-n)\ge0\) for
\(2\le m\le2N\) (with the convention \(\Lambda(n)=0\) outside \([1,N]\)),
Parseval gives \(\int_{\mathbb T}|F_N|^4=\sum_mr(m)^2\). Cauchy-Schwarz on
the sum defining \(r(m)\) gives \(r(m)\le d_N\ll NL\) (Chebyshev), and
summing over \(m\) first, \(\sum_mr(m)=\big(\sum_n\Lambda(n)\big)^2=
\psi(N)^2=O(N^2)\) (Chebyshev again). Hence
\[
 \int_{\mathbb T}|F_N|^4=\sum_mr(m)^2\le\Big(\max_mr(m)\Big)\sum_mr(m)
 =O(N^3L).
\tag{P.7}
\]
This bound uses nothing beyond Cauchy-Schwarz and \(d_N\ll NL\), already
cited in UPPER_BOUND.md Section 6. It shows the **whole-circle** fourth
moment is itself only \(O(N^3L)\) — the same order as the target the
individual arcs would need to beat, not smaller — so bounding
\(\sum_a\int_{I_{q,a}}|F_N|^4\) by any fraction of (P.7) gives nothing
useful unless that fraction is shown to be a genuinely small (\(N^{-1+
\epsilon}\)-order) share of the total, which is exactly the kind of
concentration statement (28)'s Vaughan-sup argument attempts and
RANK3_SCOPE.md Section 2 already shows fails on the lower part of this
range. A large-sieve treatment of \(F_N\) directly, in place of Vaughan's,
would have to supply that concentration statement itself; nothing computed
here supplies it, and this document does not find it supplied elsewhere.

## 5. The exact-identity route (Route D), and what it actually needs

RANK3_SCOPE.md's Route D observes that Section 7's identity (29)-(30) for
\(U_1\) plausibly generalizes, per residue class, to a per-\((q,a)\) object
built from \(\Delta(t;q,a)=\psi(t;q,a)-t/\phi(q)\), and that turning such an
identity into a bound "needs a uniform estimate for \(\Delta(t;q,a)\) at
moduli growing like a power of \(N\)" — the same requirement as Route A.
This section asks what "uniform" needs to mean, using the one place the
construction actually carries this out: \(q=1\).

At \(q=1\), Section 7 states the mechanism exactly: (SW) gives
\(\max_{t\le N}|\Delta(t)|\ll_HNL^{-H}\) *pointwise in \(t\)*, and feeding
this into the exact identity (29) — a sum over \(N\) values of \(t\) — costs
\[
 \sum_{t=1}^N\Delta(t)^2\le N\max_{t\le N}\Delta(t)^2\ll_HN^3L^{-2H},
\tag{P.8}
\]
which is exactly Section 7's stated bound and exactly the reason it is "a
power of \(N\) worse" than (31)'s target. This is not a weakness of (SW)'s
strength in \(q\); it is what happens to *any* pointwise-in-\(t\) bound once
it is squared and trivially summed over \(N\) values of \(t\). Reaching
(31) needs cancellation summed over \(t\), not a uniform pointwise bound
propagated through the sum.

This generalizes directly: whatever tool supplies control on
\(\Delta(t;q,a)\) — (SW) up to \(q\le L^B\), or, hypothetically, some
tool reaching further into \(q\) — if that control is pointwise in \(t\)
(a bound on \(\max_t|\Delta(t;q,a)|\), however strong in \(q\)), then
composing it with a Route-D identity by the same trivial route as (P.8)
costs a full power of \(N\) again, regardless of the strength in \(q\). What
Route D actually needs is a tool that already controls
\(\sum_{t\le N}\Delta(t;q,a)^2\) or \(\int_1^N\Delta(t;q,a)^2\,dt\) — an
aggregate *in \(t\)*, not only a pointwise-in-\(t\), bound.

**This is where Bombieri–Vinogradov and Barban–Davenport–Halberstam enter,
and where they fall short of what is needed.** Both are aggregate-*in-\(q\)*
statements:

- The Bombieri–Vinogradov theorem states that for every fixed \(A>0\) there
  is \(B'=B'(A)\) with
  \(\sum_{q\le Q}\max_{y\le N}\max_{(a,q)=1}|\psi(y;q,a)-y/\phi(q)|
  \ll_AN/L^A\) for \(Q\le\sqrt N/L^{B'}\) — a range that comfortably
  contains \(R_0\sim\sqrt N/(3L)\) for suitable \(B'\).
- The Barban–Davenport–Halberstam theorem, in its classical unconditional
  form, controls \(\sum_{q\le Q}\sum_a^*(\psi(N;q,a)-N/\phi(q))^2\)
  (a mean square, not a max) on average over \(q\), for \(Q\) at least up to
  \(\sqrt N\) and, in refined forms this document cannot cite a precise
  range for from memory alone, considerably further.

Both aggregate over \(q\) (and, for Bombieri–Vinogradov, take a max over
\(a\) and over \(t\le N\) rather than summing over \(a\)); neither is stated
as an aggregate *over \(t\)* — neither bounds \(\sum_{t\le N}\Delta(t;q,a)^2\)
or its integral analogue for a fixed \(q\), summed or mean-squared over the
residues \(a\), the object Route D's identity would actually produce.
Whether such a "\(t\)-integrated Barban–Davenport–Halberstam" estimate —
something of the shape
\[
 \sum_{L^B<q\le R_0}\frac{\mu(q)^2}{\phi(q)^2}\sum_a^*
 \int_1^N\Delta(t;q,a)^2\,dt\ \ll_\epsilon\ N^{2+\epsilon}
\tag{P.9}
\]
(the \(\mu(q)^2/\phi(q)^2\) weight matching how \(P_{q,a}\) itself is
weighted, by analogy with (29)-(31)'s conversion of \(\sum_t\Delta(t)^2\)
into \(32U_1\)) — is a known unconditional theorem, a known false
statement, or simply unexamined, is not something this document can settle:
it is not in UPPER_BOUND.md or RESULTS.md, and this attempt has no access to
outside literature to search for it. This is the wall this investigation
reaches. Naming it this precisely is itself the result of the investigation,
not a proof that no such estimate exists.

## 6. What this changes about RANK3_SCOPE.md's picture, and what it does not

RANK3_SCOPE.md's Route A frames the missing ingredient as "a per-modulus
uniformity... valid for individual moduli growing like \(N^{1/2}\)," and
notes its only exhibited closing route (Section 7's, at \(q=1\)) assumes
RH, calling this "circular with respect to this hunt's own stated target."
Section 5 above sharpens this along the sum-reading, \(S_U(B)\),
\(S_Z(B)\), specifically:

- The obstruction Route D actually meets is not, in the first instance, a
  need for RH-strength control *at each individual \(q\)*. It is a need for
  an aggregate-in-\(q\)-*and*-\(t\) mean-square estimate, of the same
  general kind Bombieri–Vinogradov and Barban–Davenport–Halberstam already
  supply unconditionally (their entire interest is that they give
  GRH-strength savings *on average*, without assuming GRH) — just not, so
  far as this document can determine, in the \(t\)-integrated shape (P.9)
  needs. This is a different, and on its face less obviously
  RH-dependent, kind of gap than Route A's per-modulus framing suggests.
- This also answers, provisionally, RANK3_SCOPE.md Route A's open question
  of whether an averaged-in-\(q\) estimate "would even plug into the
  arc-by-arc structure": since \(U_Q=\sum_qU_{(q)}\) exactly, an aggregate
  bound like (P.9) — if it existed and if Route D's identity were carried
  out to connect it to \(U_{(q)}\), \(Z_{(q)}\) precisely — would plug in
  directly, with no need for per-arc processing; (18) and (23)'s arc-by-arc
  form is how the *current* proof is organized, not a requirement on any
  proof of a bound on the sum.
- This does **not** resolve the max-reading, \(\max_qU_{(q)}\): an
  aggregate bound over \(q\) says nothing about any single summand, so the
  max-reading reduces to Route A's original, per-modulus, RH-tied question
  exactly as RANK3_SCOPE.md states it. The sum-reading and the max-reading
  genuinely differ here.
- Nor does it touch \(q=1\): (P.9)-style aggregation is over *many* moduli,
  and gives no separate handle on the single term \(q=1\), which sits
  outside the range \(\lfloor L^B\rfloor<q\le R_0\) in question here and is
  RANK3_SCOPE.md's rank 1, unaffected by anything in this document.

## 7. Would closing this range (if it could be closed) move the reached bound?

By the same argument as RANK3_SCOPE.md Section 4: no, on its own. Rank 1's
established bound, \(O_H(N^3L^{-2H})\), remains the weakest link among the
three named constraints regardless of what happens in this range, since
(23) sums all three rather than taking their minimum. Sections 2-3 above
give an additional, concrete reason this range's *own* contribution, at the
lower edge \(q\approx L^B\), sits at exactly the same order,
\(O(N^3L^{O(B)})\) — so even if (P.9) or an equivalent were found and
proved, the shortfall it would remove is the same shape and, absent
progress on rank 1, the same order as what already limits the construction.

## 8. Summary

For the sum-reading \(S_U(B)\), \(S_Z(B)\): two structurally different
routes were checked and both fail throughout \(\lfloor L^B\rfloor<q\le
R_0\), for every fixed \(B\), by direct computation from tools already in
UPPER_BOUND.md — (P.5)-(P.6) for the currently-used decomposition and
large-sieve descent, (P.7) for a direct large-sieve treatment of \(F_N\)'s
fourth moment. A third, more promising direction — an aggregate-in-\((q,t)\)
mean-square estimate of Barban–Davenport–Halberstam type, (P.9) — is named
precisely, is not ruled out by anything derived here, and is not something
this document, working without outside literature access, can confirm
exists. That is the wall. For the max-reading, \(\max_qU_{(q)}\),
\(\max_qZ_{(q)}\): this reduces to RANK3_SCOPE.md's Route A/D per-modulus
question and is exactly as tied to an unconditional Siegel-Walfisz-strength
uniformity (or RH) as RANK3_SCOPE.md already found, unaffected by anything
new here.
