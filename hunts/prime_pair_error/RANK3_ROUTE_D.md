# Route D carried out: the per-\((q,a)\) generalization of identity (29)-(30)

This document carries out RANK3_SCOPE.md's Route D: the exact analogue, for
general modulus \(q\) and reduced residue \(a\bmod q\), of UPPER_BOUND.md's
Parseval identity (29) and its arc-transfer bound (30). Everything derived
below is exact algebra (Parseval/orthogonality) plus explicit,
non-asymptotic inequalities; no new estimate for \(\Delta(t;q,a)\)-type
quantities is claimed or attempted, since RANK3_SCOPE.md §2-3 already show
that estimate (Route A) is the missing input and is not supplied by
(SW)/(V)/(LS). This is exactly the boundary RANK3_SCOPE.md draws: "the
identity half is plausible... nothing in the text suggests an obstruction to
writing it down. But converting that identity into a bound... still needs a
uniform estimate."

**A note on sources.** This attempt's worktree does not contain
`RANK3_POLYRANGE.md`; only its guessed weight, as quoted in this document's
own assignment — \(\mu(q)^2/\phi(q)^2\), summed over \(a\), "not derived and
may be wrong" — was available to check against. §5 below checks it against
what is actually derived here. If `RANK3_POLYRANGE.md` exists elsewhere with
content beyond that one guess, it was not read to produce this document, and
whoever next holds both should reconcile them.

## 1. Setup

Recall from UPPER_BOUND.md §§3,6: for \(q\ge1\), \(a\) a reduced residue mod
\(q\), and \(\beta\) with \(\|\beta\|\le\delta_q=Q/(qN)\),
\[
 P_{q,a}(\beta)=\frac{\mu(q)}{\phi(q)}K_N(\beta),\qquad
 R_{q,a}(\beta)=F_N(a/q+\beta)-P_{q,a}(\beta),
\]
\[
 U_{(q)}=\sum_{a\bmod q}^*\int_{\|\beta\|\le\delta_q}|P_{q,a}(\beta)|^2|R_{q,a}(\beta)|^2\,d\beta,
\qquad
 Z_{(q)}=\sum_{a\bmod q}^*\int_{\|\beta\|\le\delta_q}|R_{q,a}(\beta)|^4\,d\beta,
\tag{D0}
\]
the star meaning \(a\) ranges over the \(\phi(q)\) reduced residues; both
\(U_{(q)}\) and \(Z_{(q)}\) are read off \(F_N\) and \(K_N\) alone, with no
prime-pair content assumed. \(F_N,K_N,\Lambda,\psi\) are as in
UPPER_BOUND.md §1; \(L=\log N\).

**Orthogonality decomposition.** For \(n\ge1\), \(\exp1(n\cdot a/q)\) depends
on \(n\) only through \(n\bmod q\), so grouping the sum defining \(F_N\) by
residue class,
\[
 F_N(a/q+\beta)=\sum_{b\bmod q}\exp1(ab/q)\,S_b(\beta),\qquad
 S_b(\beta)=\sum_{\substack{n=1\\n\equiv b\,(q)}}^N\Lambda(n)\exp1(n\beta),
\tag{D1}
\]
exactly, for every \(q,a,\beta\) — this is the identity named in the
assignment, and it costs nothing beyond regrouping a finite sum.

**Coprime/non-coprime split.** Split the outer sum in (D1) by
\(\gcd(b,q)\). For \((b,q)=1\), (SW)'s content is
\(\psi(t;q,b)=t/\phi(q)+O_{B,H}(NL^{-H})\) uniformly for \(q\le L^B\); the
natural model for \(S_b\) coming from that same heuristic (density
\(1/\phi(q)\) among all \(n\le N\), not just those \(\equiv b\)) is
\(K_N(\beta)/\phi(q)\), exactly the model UPPER_BOUND.md's own paragraph
before (17) uses. Define, for \((b,q)=1\),
\[
 D_b(\beta)=S_b(\beta)-\frac{K_N(\beta)}{\phi(q)}
           =\sum_{n=1}^N\Big(\Lambda(n)\mathbf 1_{n\equiv b(q)}-\frac1{\phi(q)}\Big)\exp1(n\beta).
\tag{D2}\]
For \(\gcd(b,q)>1\), \(S_b\) is a residual: \(\Lambda(n)\ne0\) only at prime
powers, and \(\gcd(n,q)>1\) forces \(n=p^k\) with \(p\mid q\); each such
prime contributes \(\sum_{p^k\le N}\log p\le L\), and \(q\) has
\(\omega(q)\le\log_2q\) prime factors, so
\[
 \rho_2(q):=\sum_{\substack{n\le N\\ \gcd(n,q)>1}}\Lambda(n)
           =\sum_{p\mid q}\ \sum_{p^k\le N}\log p
           \le\omega(q)L\ll L\log(2q),
\tag{D3}
\]
the same quantity UPPER_BOUND.md's paragraph before (17) bounds ("\(O(L\log(2q))\)
from prime powers whose prime divides \(q\)"). Since the sets \(\{n\le N:
n\equiv b(q)\}\) for distinct non-coprime \(b\) partition \(\{n\le N:
\gcd(n,q)>1\}\), \(\sum_{b:(b,q)>1}|S_b(\beta)|\le\rho_2(q)\) for every
\(\beta\) (triangle inequality inside each \(S_b\), then summing the
disjoint ranges).

**Consistency check: (D1) reproduces \(P_{q,a}\).** Summing the coprime part
of (D1) with the model in place of \(S_b\),
\[
 \sum_{b\bmod q}^*\exp1(ab/q)\frac{K_N(\beta)}{\phi(q)}
 =\frac{K_N(\beta)}{\phi(q)}\sum_{b\bmod q}^*\exp1(ab/q)
 =\frac{K_N(\beta)}{\phi(q)}c_q(a)
 =\frac{\mu(q)}{\phi(q)}K_N(\beta),
\]
using \(c_q(a)=\mu(q)\) for \((a,q)=1\) (classical: write
\(\mathbf1_{(b,q)=1}=\sum_{d\mid\gcd(b,q)}\mu(d)\) and sum over \(b\bmod q\);
only \(d=q\) survives since \((a,q)=1\)). This is exactly \(P_{q,a}\) as
already defined in UPPER_BOUND.md — the given \(P_{q,a}\) is precisely what
falls out of modeling every coprime \(S_b\) by \(K_N/\phi(q)\) and summing
against the character-like weight \(\exp1(ab/q)\); it is not a separate
ansatz. Consequently
\[
 R_{q,a}(\beta)=\underbrace{\sum_{b\bmod q}^*\exp1(ab/q)D_b(\beta)}_{R^{(1)}_{q,a}(\beta)}
              +\underbrace{\sum_{\substack{b\bmod q\\(b,q)>1}}\exp1(ab/q)S_b(\beta)}_{R^{(2)}_{q,a}(\beta)},
\qquad|R^{(2)}_{q,a}(\beta)|\le\rho_2(q).
\tag{D4}
\]

**The per-residue remainder.** For \((b,q)=1\) and integer \(0\le t\le N\),
define, exactly as named in the assignment (the dummy index is written \(b\)
here, not \(a\), because \(a\) already names the arc center in \(P_{q,a}\)):
\[
 \Delta(t;q,b)=\psi(t;q,b)-\frac t{\phi(q)},\qquad
 \psi(t;q,b)=\sum_{\substack{n\le t\\n\equiv b(q)}}\Lambda(n).
\]
At \(q=1\) there is one residue \(b=0\), \(\phi(1)=1\), and
\(\Delta(t;1,0)=\psi(t)-t=\Delta(t)\), UPPER_BOUND.md's own notation; every
identity below reduces to (29)-(30) exactly at \(q=1\), checked at the end
of §3.

## 2. The exact per-residue identity: (29), one copy per residue

Fix \((b,q)=1\). \(K_N D_b\) is the coefficient-wise convolution of
\(\mathbf1_{[1,N]}\) with \(d_b(n):=\Lambda(n)\mathbf1_{n\equiv b(q)}-1/\phi(q)\)
(both supported on \(1\le n\le N\)); its coefficient at \(\exp1(m\beta)\) is
\(\sum_{n=\max(1,m-N)}^{\min(N,m-1)}d_b(n)\), which for \(2\le m\le N+1\) is
\(\sum_{n=1}^{m-1}d_b(n)=\Delta(m-1;q,b)\), and for \(N+2\le m\le2N\) is
\(\Delta(N;q,b)-\Delta(m-N-1;q,b)\) — the identical computation
UPPER_BOUND.md performs in the proof of (29), with \(\Lambda(n)-1\) replaced
by \(d_b(n)\). Parseval and the same completed square (an identity in the
partial sums alone, so it transfers verbatim) give, for every \((b,q)=1\),
\[
 T(q,b):=\int_{\mathbb T}|K_N D_b|^2
 =\sum_{t=1}^N\Delta(t;q,b)^2+\sum_{t=1}^{N-1}[\Delta(N;q,b)-\Delta(t;q,b)]^2
 =\frac{N+1}2\Delta(N;q,b)^2+2\sum_{t=1}^{N-1}\Big[\Delta(t;q,b)-\frac{\Delta(N;q,b)}2\Big]^2.
\tag{D5}
\]
\(T(q,b)\) is a genuine, exact per-residue copy of (29): at \(q=1\),
\(T(1,0)=T_N\).

The same computation on two residues \(b\ne b'\) gives the real,
exact bilinear cross term
\[
 X(b,b'):=\int_{\mathbb T}K_ND_b\,\overline{K_ND_{b'}}
 =\sum_{t=1}^N\Delta(t;q,b)\Delta(t;q,b')
  +\sum_{t=1}^{N-1}[\Delta(N;q,b)-\Delta(t;q,b)][\Delta(N;q,b')-\Delta(t;q,b')],
\tag{D6}
\]
with \(X(b,b)=T(q,b)\); \(X\) is an inner product
\(\langle K_ND_b,K_ND_{b'}\rangle_{L^2(\mathbb T)}\), so
\((X(b,b'))_{b,b'}\) is a real symmetric positive-semidefinite Gram matrix
and \(|X(b,b')|\le\sqrt{T(q,b)T(q,b')}\) by Cauchy-Schwarz. No identity of
this kind exists in either source document for \(q\ge2\); (D5)-(D6) are new.

## 3. The exact identity for \(U_{(q)}\)'s coprime-driven part, summed over \(a\)

By (D4), \(K_NR^{(1)}_{q,a}=\sum_{b}^*\exp1(ab/q)K_ND_b\), so
\[
 \int_{\mathbb T}|K_N|^2|R^{(1)}_{q,a}|^2
 =\sum_{b,b'}^*\exp1\!\big(a(b-b')/q\big)X(b,b').
\]
Summing over the \(\phi(q)\) reduced residues \(a\) and using
\(\sum_a^*\exp1(a(b-b')/q)=c_q(b-b')\) (the Ramanujan sum already defined in
UPPER_BOUND.md §2, with \(c_q(0)=\phi(q)\)):
\[
 \boxed{\ \sum_{a\bmod q}^*\int_{\mathbb T}|K_N|^2|R^{(1)}_{q,a}|^2\,d\beta
 =\underbrace{\phi(q)\sum_{b\bmod q}^*T(q,b)}_{\Sigma_{\rm diag}(q)}
 +\underbrace{\sum_{\substack{b\ne b'\bmod q}}^*c_q(b-b')X(b,b')}_{\Sigma_{\rm cross}(q)}.\ }
\tag{D7}
\]
This is **exact** — pure Parseval and character orthogonality, no
approximation anywhere — and it is the per-\((q,a)\) analogue of (29) the
task asks for. At \(q=1\) there is only \(b=b'=0\), \(\Sigma_{\rm
cross}(1)=0\) (empty sum), \(\Sigma_{\rm diag}(1)=\phi(1)T(1,0)=T_N\): (D7)
reduces to (29) exactly, with the single arc \(a=1\).

For \(q\ge2\), \(\Sigma_{\rm cross}(q)\) has no counterpart at \(q=1\): it
is a real number of either sign (the left side is \(\ge0\), so
\(\Sigma_{\rm cross}(q)\ge-\Sigma_{\rm diag}(q)\), but nothing here pins its
sign further). A cancellation-free upper bound is available from the Gram
property of \(X\): \(|c_q(k)|\le\phi(q)\) trivially (a sum of \(\phi(q)\)
unit-modulus terms), and
\[
 \sum_{b\ne b'}^*|X(b,b')|\le\sum_{b\ne b'}^*\sqrt{T(q,b)T(q,b')}
 \le\Big(\sum_b^*\sqrt{T(q,b)}\Big)^2-\sum_b^*T(q,b)
 \le(\phi(q)-1)\sum_b^*T(q,b)
\]
(Cauchy-Schwarz twice), so \(|\Sigma_{\rm cross}(q)|\le\phi(q)(\phi(q)-1)\sum_b^*T(q,b)\), and
\[
 \Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)\ \le\ \phi(q)^2\sum_{b\bmod q}^*T(q,b).
\tag{D8}
\]
(D8) assumes no cancellation in \(\Sigma_{\rm cross}\) at all; whether the
true value of \(\Sigma_{\rm cross}(q)\) is close to \(0\) (as the
diagonal-only guess in §5 below implicitly assumes) or close to its
Cauchy-Schwarz ceiling is not determined by UPPER_BOUND.md or RESULTS.md —
both are consistent with the exact identity (D7).

## 4. Assembling \(U_{(q)}\): the \(R^{(2)}\) correction and the arc transfer

By \((x+y)^2\le2x^2+2y^2\), \(|R^{(2)}_{q,a}|\le\rho_2(q)\) pointwise, and
\(\int_{\mathbb T}|K_N|^2=N\):
\[
 \int_{\mathbb T}|K_N|^2|R_{q,a}|^2
 \le2\int_{\mathbb T}|K_N|^2|R^{(1)}_{q,a}|^2+2\rho_2(q)^2N.
\]
Summing over \(a\) and applying (D8):
\[
 \sum_{a\bmod q}^*\int_{\mathbb T}|K_N|^2|R_{q,a}|^2\,d\beta
 \le2\phi(q)^2\sum_{b\bmod q}^*T(q,b)+2\phi(q)\rho_2(q)^2N.
\tag{D9}
\]
Multiplying by \((\mu(q)/\phi(q))^2=|P_{q,a}|^2/|K_N(\beta)|^2\) gives the
full-circle analogue of \(T_N\) at \((q,a)\), summed over \(a\); note the
\(\phi(q)^2\) in (D8)-(D9) cancels the \(1/\phi(q)^2\) exactly:
\[
 \sum_a^*T_N(q,a):=\sum_a^*\int_{\mathbb T}|P_{q,a}|^2|R_{q,a}|^2\,d\beta
 \le2\mu(q)^2\sum_{b\bmod q}^*T(q,b)+\frac{2\mu(q)^2\rho_2(q)^2N}{\phi(q)}.
\tag{D10}
\]
**Arc transfer, generalizing (30).** On \(\|\beta\|>\delta_q=Q/(qN)\),
\(|K_N(\beta)|\le(2\|\beta\|)^{-1}<qN/(2Q)\), so \(|P_{q,a}(\beta)|^2\le
\mu(q)^2q^2N^2/(4Q^2\phi(q)^2)\) there, giving, exactly as in (30),
\[
 0\le T_N(q,a)-\int_{\|\beta\|\le\delta_q}|P_{q,a}|^2|R_{q,a}|^2
 \le\frac{\mu(q)^2q^2N^2}{4Q^2\phi(q)^2}\int_{\mathbb T}|R_{q,a}|^2\,d\beta.
\]
Exactly, \(\int_{\mathbb T}|R_{q,a}|^2=\sum_{n=1}^N|\Lambda(n)\exp1(na/q)-\mu(q)/\phi(q)|^2
\le\sum_n(\Lambda(n)+1)^2\le2d_N+2N\ll NL\) (Chebyshev, as UPPER_BOUND.md
§2 uses for \(d_N\)), uniformly in \(a\) and \(q\). Summing over the
\(\phi(q)\) values of \(a\) and combining with (D10):
\[
 \boxed{\ U_{(q)}\ \le\ 2\mu(q)^2\sum_{b\bmod q}^*T(q,b)
 \ +\ O\!\left(\frac{\mu(q)^2\rho_2(q)^2N}{\phi(q)}\right)
 \ +\ O\!\left(\frac{q^2N^3L}{Q^2\phi(q)}\right).\ }
\tag{D11}
\]
This is the requested exact-identity-plus-explicit-error-term result for
\(U_{(q)}\): (D7) is exact, (D8) is a one-sided but fully explicit
Cauchy-Schwarz bound, (D3) and the transfer step are explicit and of the
same shape as (30). At \(q=1\): \(\mu(1)^2=1\), \(\phi(1)=1\),
\(\rho_2(1)=0\) (no prime divides \(1\)), and (D11) reads
\(U_1\le2T_N+O(N^2L)\), matching (29)-(30) up to the factor of 2 coming
from using \((x+y)^2\le2x^2+2y^2\) instead of expanding exactly — using the
exact expansion at \(q=1\) (no \(R^{(2)}\) term exists there) removes that
factor and reproduces (30) exactly. Two further facts fall out for free:
since \(\mu(q)=0\) for non-squarefree \(q\), (D11) gives \(U_{(q)}=0\)
**identically** for every non-squarefree \(q\) — \(U_{(q)}\) for \(q\le
R_0\) is supported only on the squarefree \(q\) in that range, a
simplification not stated in RANK3_SCOPE.md.

## 5. What weight this identity actually carries — checking the guess

RANK3_POLYRANGE.md's guess, as quoted in this document's assignment, is
that the conversion carries weight \(\mu(q)^2/\phi(q)^2\), summed over
\(a\), by direct analogy with (29)-(31)'s \(1\cdot\sum_t\Delta(t)^2\to32U_1\)
(i.e., \(q=1\) has \(\mu(1)^2/\phi(1)^2=1\)). Three distinct weights appear
in the computation above, and they disagree with each other, so "the"
weight is not a single number without specifying which quantity it
multiplies:

- **If \(\Sigma_{\rm cross}(q)\) is discarded assuming it is genuinely
  negligible** (an assumption not derived here, and not decidable from
  UPPER_BOUND.md/RESULTS.md — see end of §3), the diagonal piece alone in
  (D7) carries weight \(\mu(q)^2/\phi(q)\) on \(\sum_b^*T(q,b)\)
  — **one power of \(\phi(q)\)**, not two.
- **Without assuming any cancellation** — the only bound actually proved
  here, (D11) — the weight on \(\sum_b^*T(q,b)\) is \(2\mu(q)^2\), i.e.
  \(O(1)\), with **no** \(\phi(q)\) in the denominator at all: the
  \(\phi(q)^2\) from the Cauchy-Schwarz ceiling on \(\Sigma_{\rm cross}\)
  in (D8) exactly cancels the \(1/\phi(q)^2\) in \(|P_{q,a}|^2\).
- The guessed weight, \(\mu(q)^2/\phi(q)^2\), is smaller than *both* of
  these by at least one further power of \(\phi(q)\) (relative to the
  diagonal-only weight) or two further powers (relative to the proved,
  cancellation-free weight).

So the guess is not merely undetermined, it is optimistic against what this
derivation actually establishes: reaching \(\mu(q)^2/\phi(q)^2\) would
require \(\Sigma_{\rm cross}(q)\) to cancel the diagonal term down by a
full extra factor of \(\phi(q)\) beyond assuming it is simply negligible.
Nothing in UPPER_BOUND.md or RESULTS.md supplies or suggests such a
cancellation; it is a new claim, not implied by the \(q=1\) analogy the
guess was built on (at \(q=1\) there is no cross term to cancel anything,
so the analogy is silent on this point by construction). Whether
\(\Sigma_{\rm cross}(q)\) is in fact small is exactly as open as the
\(\Delta(t;q,b)\)-uniformity question RANK3_SCOPE.md's Route A already
names; this document does not resolve it either way, and the sources give
no way to.

## 6. A cost the identity carries that RANK3_SCOPE.md did not have: the transfer step, summed over \(q\)

RANK3_SCOPE.md's Route D discussion (§3) says building the identity would
only "relocate" Route A's missing uniform estimate, not add a new cost.
That undercounts one item, visible only once the identity is written down:
even granting a hypothetical uniform bound making every \(\sum_b^*T(q,b)\)
in (D11) as small as the target requires, the **transfer term**
\(O(q^2N^3L/(Q^2\phi(q)))\) in (D11), summed over the actual rank-3 range
\(2\le q\le R_0\) with \(Q=\lfloor\sqrt N/3\rfloor\), \(R_0=Q/L\), already
costs more than the whole target budget on its own. By (15),
\(q^2/\phi(q)=q\cdot(q/\phi(q))\le\zeta(2)q(1+\log q)\), so
\[
 \sum_{q=2}^{R_0}\frac{q^2}{\phi(q)}\ll\sum_{q=2}^{R_0}q(1+\log q)\ll R_0^2\log(2R_0).
\]
With \(R_0=Q/L\), \(Q\asymp\sqrt N\): \(R_0^2\log(2R_0)\asymp
(N/L^2)\cdot(L/2)=N/(2L)\), so
\[
 \sum_{q=2}^{R_0}O\!\left(\frac{q^2N^3L}{Q^2\phi(q)}\right)
 \ll\frac{N^3L}{Q^2}\cdot\frac N{L}
 =\frac{N^4L}{Q^2L}\cdot\frac1{1}
 \asymp N^3,
\]
using \(Q^2\asymp N\). That is, the crude sup-bound transfer step used here
(the direct generalization of (30)'s method) costs \(O(N^3)\) once summed
over \(2\le q\le R_0\) — **no saving over the trivial bound at all**, the
same order as the unconditional baseline (1) already proves by a completely
different route. This holds independent of anything assumed about
\(\Delta(t;q,b)\): the obstruction is the transfer step itself, not the
main term. The reason (30)'s version of this step was harmless at \(q=1\)
is that it was never summed over \(q\); (24)-(27)'s dyadic large-sieve
argument is exactly the kind of *non-crude* transfer that avoids this
blow-up for \(q>R_0\), by averaging across a whole dyadic block rather than
bounding each arc's tail by its own supremum. Route D, carried out with the
naive per-arc transfer, would need an analogous refinement for \(q\le
R_0\) — this is additional to, not a restatement of, Route A's
\(\Delta(t;q,b)\)-uniformity requirement, and neither document names it.

## 7. As far as possible for \(Z_{(q)}\)

\(Z_{(q)}=\sum_a^*\int_{\rm arc}|R_{q,a}|^4\) carries **no** \(|P_{q,a}|^2\)
weight (UPPER_BOUND.md §6, and the assignment's own definition), unlike
\(U_{(q)}\). This changes the picture in two independent ways.

**No K_N-convolution, so no telescoping.** The reduction in §2 that turned
\(D_b\)'s coefficients into partial sums \(\Delta(t;q,b)\) came entirely
from convolving with \(K_N\) (whose coefficients are the constant \(1\) on
\([1,N]\), turning a coefficient sequence into its partial sums under
convolution). \(Z_{(q)}\) has no such factor: its full-circle analogue is a
4th moment of \(D_b\) **itself**, not of \(K_ND_b\). Repeating (D4) and
Parseval on \(R^{(1)}_{q,a}=\sum_b^*\exp1(ab/q)D_b\),
\[
 \int_{\mathbb T}|R^{(1)}_{q,a}|^4
 =\sum_{b_1,b_2,b_3,b_4}^*\exp1\!\big(a(b_1{+}b_2{-}b_3{-}b_4)/q\big)\,Y(b_1,b_2,b_3,b_4),
\]
\[
 Y(b_1,b_2,b_3,b_4)=\sum_{\substack{n_1,n_2,n_3,n_4=1\\n_1+n_2=n_3+n_4}}^N
 d_{b_1}(n_1)d_{b_2}(n_2)d_{b_3}(n_3)d_{b_4}(n_4),
\]
exact by the same "\(\int_{\mathbb T}\exp1(k\beta)=\mathbf1_{k=0}\)"
argument. Summing over \(a\) produces a 4-index Ramanujan-sum weight
\(c_q(b_1+b_2-b_3-b_4)\) exactly as \(c_q(b-b')\) appeared in (D7). This is
the exact per-\((q,a)\) generalization the task asks for, as far as it
goes: it reduces \(Z_{(q)}\)'s coprime part to a Ramanujan-sum-weighted sum
of the quadruple additive-convolutions \(Y\) of the sequences \(d_b\).
Unlike (D5), \(Y\) does **not** reduce to a sum of squares of
\(\Delta(t;q,b)\): the constraint \(n_1+n_2=n_3+n_4\) is a genuine additive
condition on four independent indices, not a diagonal telescoping identity,
because there is no kernel factor turning \(d_b\) into its own partial
sums. This is a structural fact about the definition of \(Z\), not a gap in
this derivation: at \(q=1\), \(Y(0,0,0,0)=\int_{\mathbb T}|F_N-K_N|^4\) is
exactly \(Z_{(1)}\)'s full-circle analogue, and RANK3_SCOPE.md §1 already
records that no identity for \(Z_{(1)}\) exists in either source document.
This document does not supply one either, for \(q=1\) or any \(q\ge2\); it
exhibits the same difficulty, parametrized over \(q\) and \(b\), rather
than resolving it.

**No arc-transfer analogue either.** The transfer step in §4 worked because
\(U_{(q)}\)'s integrand carries the factor \(|P_{q,a}|^2=|K_N|^2\cdot
(\mu(q)/\phi(q))^2\), which decays like \(q^2N^2/Q^2\) away from the arc and
so makes the full-circle-minus-arc discrepancy small once \(Q\) is large
enough. \(Z_{(q)}\)'s integrand, \(|R_{q,a}|^4\), carries no such factor:
\(R_{q,a}=F_N-P_{q,a}\) has no reason to be small away from the arc (indeed
\(F_N\) itself need not be small there), so bounding
\(\int_{\mathbb T}|R_{q,a}|^4\) does not bound
\(\int_{\rm arc}|R_{q,a}|^4\) the way it did for \(U\). This matches
UPPER_BOUND.md's own practice: (28)'s bound on \(Z_{q>R_0}\) never goes
through a full-circle identity, it stays on the actual arcs and uses (V)
directly. So even setting aside the non-reduction of \(Y\), a full-circle
route to \(Z_{(q)}\) would need a second, unrelated argument this document
does not supply, and neither source names one.

The \(R^{(2)}\) correction for \(Z\) is straightforward by the same method
as §4: \((x+y)^4\le8(x^4+y^4)\) (the same constant UPPER_BOUND.md uses at
(28)) and \(|R^{(2)}_{q,a}|\le\rho_2(q)\) give
\(\int_{\mathbb T}|R^{(2)}_{q,a}|^4\le\rho_2(q)^4\), hence
\(\sum_a^*\int_{\mathbb T}|R_{q,a}|^4\le8\sum_a^*\int_{\mathbb T}|R^{(1)}_{q,a}|^4+8\phi(q)\rho_2(q)^4\);
this is the one piece of \(Z_{(q)}\)'s treatment that is fully closed here,
and it is the smaller of the two obstructions above.

## 8. Where this leaves rank 3

The identity half of Route D, which RANK3_SCOPE.md §3 said was plausible
but unwritten, is now written down exactly for \(U_{(q)}\) — (D7) — and as
far as the definition of \(Z\) permits for \(Z_{(q)}\) (the quadruple-sum
reduction above, which does not close). RANK3_SCOPE.md §3's conclusion that
Route D "does not lower the cost of Route A; it only relocates where the
missing input would be used" needs one addition: it also surfaces a second,
independent requirement (§6) — a non-crude, large-sieve-style transfer
argument in place of the direct \((30)\)-style bound, since the latter
costs \(O(N^3)\) once summed over \(2\le q\le R_0\) regardless of how well
\(\Delta(t;q,b)\) is controlled. Neither requirement is met here or costed
to completion by either source document. RANK3_SCOPE.md §4's conclusion —
that closing rank 3 alone cannot move the bound reached, because rank 1's
\(O_H(N^3L^{-2H})\) is the current bottleneck in (23) regardless of what
happens to ranks 2 or 3 — is unaffected by anything in this document: no
identity or bound derived here touches rank 1, \(M_Q\), \(I_Q\), or the
unconditional total (1).

This document is algebraic bookkeeping (Parseval, orthogonality, Cauchy-Schwarz)
around the existing unconditional construction in UPPER_BOUND.md; it assumes
and establishes nothing about zeros of \(L\)-functions or the Riemann
Hypothesis.
