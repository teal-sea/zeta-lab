# Route D's arc-transfer step is dispensable: a zero-cost replacement, and why dyadic large sieve doesn't need to (or manage to) do its job

This document answers one question, precisely scoped: RANK3_ROUTE_D.md §6 shows
that the direct, per-arc transfer bound used in its equation (D11) — the
generalization of UPPER_BOUND.md's (30) from \(q=1\) to general \(q\) — costs
\(O(N^3)\) once summed over \(2\le q\le R_0\), as large as the unconditional
baseline (1), regardless of any estimate for \(\Delta(t;q,b)\). The question
posed is whether UPPER_BOUND.md's dyadic large-sieve method (24)-(27), which
solves an analogous problem for \(q>R_0\), can be adapted to bring that
transfer cost down, ideally to \(O(N^{2+\epsilon})\).

**The answer is not an adaptation.** The transfer step does not need a better
bound; it needs to be deleted. The quantity RANK3_ROUTE_D.md's §4 spends an
\(O(N^3)\)-costing inequality bounding is already bounded, for free and
exactly, by monotonicity of integration — a fact that holds independently of
\(\Delta(t;q,b)\), of the large sieve, and of \(q\). Once this is used
instead, \(\sum_{q=2}^{R_0}U_{(q)}\)'s only remaining unproved dependence is
exactly \(\sum_{q=2}^{R_0}\mu(q)^2\sum_b^*T(q,b)\) — RANK3_SCOPE.md's Route A,
untouched here — plus an explicit term this document bounds by
\(O(NL^6)\), negligible against any target of size \(N^{2+\epsilon}\) or
larger. §5 below explains why the dyadic large-sieve mechanism specifically
does not fit this quantity even when asked to, which is a separate fact from
its being unnecessary.

No estimate for \(\Delta(t;q,b)\) is attempted or assumed anywhere below,
matching RANK3_ROUTE_D.md's own scope and the assignment's instruction.

## 1. The quantity at issue, restated

Notation is RANK3_ROUTE_D.md's throughout: \(q\ge2\), \(a\) a reduced residue
mod \(q\), \(P_{q,a}(\alpha)=(\mu(q)/\phi(q))K_N(\alpha-a/q)\),
\(R_{q,a}=F_N-P_{q,a}\), both defined as finite exponential sums on all of
\(\mathbb T=\mathbb R/\mathbb Z\), and
\[
 I_{q,a}=\{\alpha\in\mathbb T:\|\alpha-a/q\|\le\delta_q\},\quad\delta_q=Q/(qN),
\]
the arc from UPPER_BOUND.md (7). RANK3_ROUTE_D.md's equation (D10)-adjacent
text defines, exactly as the assignment names it,
\[
 T_N(q,a):=\int_{\mathbb T}|P_{q,a}|^2|R_{q,a}|^2\,d\beta,
\]
and UPPER_BOUND.md's \(U_{(q)}\) (the quantity that actually enters the
sufficient bound (23) via \(U_Q=\sum_{q\le Q}U_{(q)}\)) is
\[
 U_{(q)}=\sum_{a\bmod q}^*\int_{I_{q,a}}|P_{q,a}|^2|R_{q,a}|^2\,d\alpha.
\]
The transfer quantity the assignment names is
\(\sum_{a}^*\big[T_N(q,a)-\int_{I_{q,a}}|P_{q,a}|^2|R_{q,a}|^2\big]\), summed
over \(2\le q\le R_0\). RANK3_ROUTE_D.md §4 bounds this quantity, per \((q,a)\),
by \(\dfrac{\mu(q)^2q^2N^2}{4Q^2\phi(q)^2}\int_{\mathbb T}|R_{q,a}|^2\), which
after summing over \(a\) and \(q\le R_0\) is the \(O(N^3)\) term §6 identifies.

## 2. Monotonicity: the trivial bound that makes the transfer step unnecessary

**Lemma.** For every \(q\ge1\) and every reduced \(a\bmod q\),
\[
 0\ \le\ \int_{I_{q,a}}|P_{q,a}|^2|R_{q,a}|^2\,d\alpha\ \le\ T_N(q,a).
\tag{T1}
\]

*Proof.* \(I_{q,a}\subset\mathbb T\), and the integrand \(|P_{q,a}|^2|R_{q,a}|^2\)
is real-valued and nonnegative everywhere on \(\mathbb T\) (it is a product of
two squared moduli of finite exponential sums, defined at every point, not
only on the arc). Integrating a nonnegative function over a subset of its
domain cannot exceed integrating it over the whole domain. \(\square\)

This is not asymptotic, not conditional on anything about \(\Delta(t;q,b)\),
and does not use any property of \(P_{q,a}\) or \(R_{q,a}\) beyond
nonnegativity of the integrand and \(I_{q,a}\subseteq\mathbb T\). It holds at
every \(N,q,a\), including \(q=1\). §6 of this document checks it numerically
against direct evaluation of \(F_N,K_N\) at several small \((N,q,a)\); it
holds in every case, as it must.

**Corollary.** Summing (T1) over the \(\phi(q)\) reduced residues \(a\),
\[
 U_{(q)}\ \le\ \sum_{a\bmod q}^*T_N(q,a).
\tag{T2}
\]

The right side of (T2) is exactly the quantity RANK3_ROUTE_D.md's equation
(D10) already bounds — and (D10) is derived (via (D7), the one-sided
Cauchy-Schwarz bound (D8), and the \(\rho_2(q)\) correction (D3)) *before*
RANK3_ROUTE_D.md's §4 introduces the arc-transfer step at all. Nothing in the
derivation of (D10) uses the transfer inequality; (D10) is a self-contained
bound on \(\sum_a^*T_N(q,a)\), reproduced here:
\[
 \sum_{a\bmod q}^*T_N(q,a)\ \le\ 2\mu(q)^2\sum_{b\bmod q}^*T(q,b)
 +\frac{2\mu(q)^2\rho_2(q)^2N}{\phi(q)}.
\tag{D10}
\]
Combining (T2) with (D10) directly:
\[
 \boxed{\ U_{(q)}\ \le\ 2\mu(q)^2\sum_{b\bmod q}^*T(q,b)
 +\frac{2\mu(q)^2\rho_2(q)^2N}{\phi(q)}.\ }
\tag{T3}
\]
(T3) is exactly RANK3_ROUTE_D.md's boxed (D11) **with its third term —
the transfer term \(O(q^2N^3L/(Q^2\phi(q)))\) — removed**, and it is a
strictly stronger (or, in the degenerate case, equal) bound: (D11) is
obtained from (T3) by adding a nonnegative quantity to its right side, which
can only weaken an upper bound, never repair one. There is consequently
nothing to adapt: the transfer step contributes an unnecessary and, once
summed over \(q\), dominant slack term to an inequality that is already true
without it.

## 3. What this removes from the O(N^3) in RANK3_ROUTE_D.md §6

§6's computation is a bound on \(\sum_{q=2}^{R_0}\) of (D11)'s third term
alone; it does not touch (D11)'s first two terms (those are the diagonal
Parseval quantity and the \(\rho_2\) correction, both present in (T3)
unchanged). Since (T3) has no third term, that entire computation —
\(\sum_{q=2}^{R_0}O(q^2N^3L/(Q^2\phi(q)))\asymp N^3\) — is not a cost of
bounding \(\sum_{q=2}^{R_0}U_{(q)}\) via (T3). Summing (T3) over
\(2\le q\le R_0\):
\[
 \sum_{q=2}^{R_0}U_{(q)}\ \le\
 2\sum_{q=2}^{R_0}\mu(q)^2\sum_{b\bmod q}^*T(q,b)
 +2N\sum_{q=2}^{R_0}\frac{\mu(q)^2\rho_2(q)^2}{\phi(q)}.
\tag{T4}
\]

## 4. The surviving explicit term is \(O(NL^6)\), not \(O(N^3)\)

The second sum in (T4) is bounded using only tools already present in
UPPER_BOUND.md and RANK3_ROUTE_D.md. By (D3), \(\rho_2(q)\ll L\log(2q)\), so
\(\rho_2(q)^2\ll L^2\log^2(2q)\). By UPPER_BOUND.md (15),
\(q/\phi(q)\le\zeta(2)(1+\log q)\), hence \(1/\phi(q)\le\zeta(2)(1+\log q)/q\).
Since \(\mu(q)^2\le1\),
\[
 \sum_{q=2}^{R_0}\frac{\mu(q)^2\rho_2(q)^2}{\phi(q)}
 \ll L^2\sum_{q=2}^{R_0}\frac{\log^2(2q)(1+\log q)}{q}
 \ll L^2\sum_{q=2}^{R_0}\frac{\log^3(2q)}{q}.
\]
By the standard comparison \(\sum_{2\le q\le x}\log^3(2q)/q\ll\log^4(2x)\)
(partial summation against \(\int_2^x(\log2t)^3\,dt/t=[(\log2t)^4/4]_2^x\)),
and \(R_0=Q/L\), \(Q=\lfloor\sqrt N/3\rfloor\), so \(\log(2R_0)\ll L\):
\[
 \sum_{q=2}^{R_0}\frac{\mu(q)^2\rho_2(q)^2}{\phi(q)}\ll L^2\cdot L^4=L^6.
\]
Therefore
\[
 \boxed{\ 2N\sum_{q=2}^{R_0}\frac{\mu(q)^2\rho_2(q)^2}{\phi(q)}\ \ll\ NL^6.\ }
\tag{T5}
\]
This is smaller than \(N^{1+\epsilon}\) for every fixed \(\epsilon>0\) and
sufficiently large \(N\); it is negligible against the target
\(N^{2+\epsilon}\), let alone against the \(O(N^3)\) this document removes.

Combining (T4) and (T5):
\[
 \boxed{\ \sum_{q=2}^{R_0}U_{(q)}\ \le\
 2\sum_{q=2}^{R_0}\mu(q)^2\sum_{b\bmod q}^*T(q,b)\ +\ O(NL^6).\ }
\tag{T6}
\]

The only unproved dependence left in (T6) is
\(\sum_{q=2}^{R_0}\mu(q)^2\sum_b^*T(q,b)\), which is exactly a
\(\Delta(t;q,b)\)-uniformity statement summed over \(q\le R_0\) — RANK3_SCOPE.md's
Route A, not attempted here per the assignment's own scope. What (T6)
establishes is that **the transfer step contributes no separate obstruction
on top of Route A**: RANK3_ROUTE_D.md §6's claim that Route D "surfaces a
second, independent requirement" beyond Route A's uniform estimate does not
survive replacing its transfer step with (T1)-(T3). The requirement was an
artifact of that specific (avoidable) step, not a property of \(U_{(q)}\) or
of the identity (D7) itself.

## 5. Why the dyadic large-sieve method does not adapt to this quantity — and does not need to

The assignment asks, in the alternative, for a precise reason if dyadic large
sieve does not adapt to the transfer quantity. It does not, and the reason is
a mismatch between what (24)-(27) is built to bound and what the transfer
quantity is.

(24)-(27) bounds, for a dyadic block \(R<q\le\min(2R,Q)\), the sum
\(\sum_{q,a\text{ in block}}\int_{I_{q,a}}|P_{q,a}|^2|R_{q,a}|^2\) directly on
the arcs, by: (i) enlarging every arc in the block to the single common
interval \(|\beta|\le Q/(RN)\) (valid because every \(q\) in the block has
comparable size, so \(\delta_q=Q/(qN)\) is comparable across the whole block);
(ii) applying the additive large sieve (LS) *at a fixed* \(\beta\), to the
set of points \(\{a/q:R<q\le2R\}\), which are genuinely \((4R^2)^{-1}\)-spaced
and therefore admissible LS inputs; and (iii) integrating the resulting
\(\beta\)-uniform bound over the (now common, small) enlarged interval. The
mechanism is fundamentally about a *sum over many centers at one shared
\(\beta\)*, bounded by how well-spaced those centers are.

The transfer quantity, by contrast, is
\(\sum_a^*\big[T_N(q,a)-\int_{I_{q,a}}|P_{q,a}|^2|R_{q,a}|^2\big]
=\sum_a^*\int_{\mathbb T\setminus I_{q,a}}|P_{q,a}|^2|R_{q,a}|^2\,d\beta\):
for a *single* modulus \(q\), an *integral over \(\beta\)* of the complement
of one arc. There is no second index to space out and no shared \(\beta\) to
fix — LS has nothing to act on here, because LS bounds a sum of squared
values of a fixed exponential polynomial evaluated at well-separated points,
and this quantity is not of that shape at all: it is one center, integrated
over the part of the circle its own arc excludes. Grouping \(q\) into dyadic
blocks does not change this, because the object being bounded does not
involve other moduli in the block; it is defined per \(q\) before any sum
over a block is taken. Handing this quantity to the (24)-(27) machine has no
well-defined entry point, independent of whether the resulting bound would be
good enough.

This is a different fact from the one in §§2-4: those show the transfer
quantity need not be bounded at all (for the purpose \(U_{(q)}\) needs, upper
bounding by monotonicity dominates), which is why the type-mismatch above is
not an obstruction to anything — it only rules out the one route the
assignment named as a first guess, in favor of the route that already works.

**Distinct from Route B, which is a genuine, still-open obstruction.** A
different question — applying (24)-(27)'s method *directly* to bound
\(U_{(q)}\) itself for \(q\le R_0\) (bypassing the Parseval identity (D7)
entirely, rather than using it and discarding the transfer step) — is exactly
RANK3_SCOPE.md §3's "Route B," and RANK3_SCOPE.md §2 already shows it fails:
the per-block estimate (25) does not save anything at small block size, and
the single block \(R=1\) (i.e. \(q=2\)) alone costs
\(O(w(Q)^2N^3L)=O(N^3L^3)\) by (25), exceeding target by a full power of
\(N\). That failure is genuine and is not resolved by anything in this
document — it is a separate question from the transfer step addressed here,
which concerns going from the *already-derived* identity-based bound (D10) to
the arc-restricted quantity, not replacing the identity with an LS argument
from scratch.

## 6. Numeric check

`rank3_arc_transfer_probe.py` evaluates \(F_N,K_N,P_{q,a},R_{q,a}\) as finite
exponential sums (no asymptotics, no model assumptions) at \(N=120\) for six
\((q,a)\) pairs, computing the full-circle integral \(T_N(q,a)\) exactly (a
uniform grid with more than twice the maximum frequency present recovers the
DC Fourier coefficient exactly, by orthogonality) and the arc integral by
numerical quadrature over the actual interval \(I_{q,a}\) at
\(Q=\lfloor\sqrt N/3\rfloor\). The Lemma (T1) holds in all six cases (e.g.
\(q=2,a=1\): arc \(\approx9452.6\le\) full circle \(\approx10385.5\)); results
are in `results_rank3_arc_transfer_probe.json`. The same script independently
cross-checks RANK3_ROUTE_D.md's exact identity (D7) — summing
\(\int_{\mathbb T}|K_N|^2|R^{(1)}_{q,a}|^2\) over \(a\) against
\(\Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)\) computed from \(T(q,b)\),
\(X(b,b')\) via (D5)-(D6) — at four \((N,q)\) pairs, matching to numerical
precision in every case. This confirms the definitions used above agree with
RANK3_ROUTE_D.md's, which is what makes reusing (D10) directly (§2) valid
rather than merely plausible.

## 7. Where this leaves rank 3

RANK3_ROUTE_D.md §8 recorded two requirements for closing rank 3 by Route D: a
uniform \(\Delta(t;q,b)\) estimate (Route A, relocated) and "a non-crude,
large-sieve-style transfer argument in place of the direct (30)-style bound."
This document removes the second requirement outright, at every \(q\), by
showing the direct (30)-style bound should not have been used to go from
(D10) to \(U_{(q)}\) in the first place — monotonicity already supplies that
step for free, and (T6) shows the resulting total cost over \(2\le q\le R_0\)
beyond Route A is \(O(NL^6)\), far under any target of size \(N^{2+\epsilon}\)
or larger. What remains open for rank 3's \(U\)-side is exactly
\(\sum_{q=2}^{R_0}\mu(q)^2\sum_b^*T(q,b)\) — Route A's uniform estimate,
undiminished but also not multiplied by any further obstruction from the
identity-to-arc step. This document says nothing about \(Z_{(q)}\)
(RANK3_ROUTE_D.md §7 already shows the arc-transfer idea does not apply there
for an unrelated, structural reason: \(Z\)'s integrand carries no
\(|P_{q,a}|^2\) factor and so has no reason to decay away from the arc, so
even the trivial monotonicity direction used here, while still true for
\(Z\), does not by itself make \(Z_{(q)}\)'s full-circle version a useful
proxy — the full-circle route to \(Z\) is not attempted here or in
RANK3_ROUTE_D.md), about rank 1, or about the RESULTS.md doors table's
overall ranking, which RANK3_SCOPE.md §4 already shows rank 3's closure
cannot move on its own regardless of what happens here.

This document is algebraic bookkeeping (monotonicity of integration of a
nonnegative function, plus the elementary sum estimate in §4) around
RANK3_ROUTE_D.md's and UPPER_BOUND.md's existing unconditional construction;
it assumes and establishes nothing about zeros of \(L\)-functions or the
Riemann Hypothesis, and does not attempt any part of the \(\Delta(t;q,b)\)
uniformity question.
