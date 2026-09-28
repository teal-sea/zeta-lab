# Farey-block baseline repair

2026-09-12. Base: science commit 3b0fc2e3c97b46cc1fde6af0ff3dd856898d95fb. Review status is recorded in FRONTIER_INDEPENDENT_REVIEW.md.

**Status.** The argument below proves the residual fourth-moment baseline
\[
 \sum_{\substack{q\asymp Q\\q\le\sqrt N}}\sum_{a\bmod q}^{*}
 \int_{|\theta|\le 1/(q\sqrt N)}
 |F_N(a/q+\theta)-(\mu(q)/\phi(q))K_N(\theta)|^4\,d\theta
 \ll \frac{N^3(\log N)^9}{Q}
 \tag{A}
\]
for \(1\le Q\le N^{2/5}\), with harmless changes to absolute constants. In particular it covers the \(Q=N^{o(1)}\) blocks in SHARP_EXPONENT.md section 1.2. Its proof needs no arithmetic-progression variance estimate.

This supersedes the faulty character-orthogonality and primitive-reduction argument for equation (4) in that section. It also withdraws the inference from those calculations that this route is closed by all available input. An upper bound from one tool is not a lower bound, an optimality statement, or a general obstruction. Nothing here proves a stronger exponential saving or advances the RH endpoint.

All displayed arguments are handwritten derivations for independent review. They are not kernel-checked proofs.

## 1. Definitions and inherited inputs

Let \(N\ge 16\) be an integer, \(L=\log N\), and
\[
 F_N(\alpha)=\sum_{1\le n\le N}\Lambda(n)e(n\alpha),
 \qquad K_N(\theta)=\sum_{1\le n\le N}e(n\theta),
 \qquad e(t)=e^{2\pi it}.
\]
Prime powers are included. Write
\[
 {\cal Q}_Q=\{q\in\mathbb N:Q\le q<2Q,\ q\le\sqrt N\},
 \qquad
 R_{q,a}(\theta)=F_N(a/q+\theta)-\frac{\mu(q)}{\phi(q)}K_N(\theta)
\]
for reduced residues \(a\bmod q\). Arcs are interpreted on \(\mathbb R/\mathbb Z\).

The inherited arithmetic estimates are:

1. \(\sum_{n\le N}\Lambda(n)^2\ll NL\), from Chebyshev's estimate and \(\Lambda(n)\le L\).
2. Vaughan's rational-approximation bound
\[
 |F_N(\alpha)|\ll
 \left(\frac{N}{\sqrt q}+N^{4/5}+\sqrt{Nq}\right)L^4,
 \qquad
 (\!a,q\!)=1,\quad |\alpha-a/q|\le q^{-2}.
 \tag{V}
\]
This is the bound used in UPPER_BOUND.md for its minor-arc estimate and in SHARP_EXPONENT.md section 1.1. The draft inherits that standard input; it does not reverify a source edition.
3. Only Appendix A uses the primitive multiplicative large sieve in the form
\[
 \sum_{d\le D}\frac d{\phi(d)}
 \sum_{\chi\bmod d}^{\rm primitive}
 \left|\sum_{M<n\le M+H}u_n\chi(n)\right|^2
 \ll (H+D^2)\sum_{M<n\le M+H}|u_n|^2.
 \tag{LS}
\]
The correctly restricted primitive-character form is recorded as (LS*) in RANK3_CONDUCTOR_SUM.md. The interval version follows from the same large-sieve theorem with an arbitrary starting index. The appendix also inherits the Gallagher lemma already stated in SHARP_EXPONENT.md section 1.2.

These are local source and definition pointers, not new literature claims.

## 2. Bounded overlap and Parseval prove the required second moment

Distinct reduced fractions in one block have circular separation at least
\[
 \left\|\frac aq-\frac{a'}{q'}\right\|_{\mathbb R/\mathbb Z}
 \ge\frac1{qq'}\ge\frac1{4Q^2}.
\]
Every arc in the block has radius at most \(1/(Q\sqrt N)\). Consequently the number covering any point is bounded by an absolute constant, since
\[
 1+\frac{2/(Q\sqrt N)}{1/(4Q^2)}
 =1+\frac{8Q}{\sqrt N}\le9.
\]
Enlarging the constant handles endpoints and the finitely many small cases. Pairwise disjointness is neither asserted nor required. Parseval gives
\[
 \sum_{q\in{\cal Q}_Q}\sum_a^*
 \int_{|\theta|\le1/(q\sqrt N)}
 |F_N(a/q+\theta)|^2\,d\theta
 \ll\int_0^1|F_N(\alpha)|^2\,d\alpha
 \ll NL.
 \tag{B}
\]

We also need the elementary uniform dyadic bound
\[
 \sum_{X\le m<2X}\frac1{\phi(m)}\ll1,\qquad X\ge\tfrac12.
 \tag{C}
\]
Indeed,
\[
 \frac m{\phi(m)}=\sum_{d\mid m}\frac{\mu(d)^2}{\phi(d)},
 \qquad
 \sum_{d\ge1}\frac{\mu(d)^2}{d\phi(d)}
 =\prod_p\left(1+\frac1{p(p-1)}\right)<\infty.
\]
Therefore \(\sum_{m<2X}m/\phi(m)\ll X\); divide by \(m\ge X\). The case \(X=1/2\), if the half-open interval contains no integer, is immediate.

For the model term, with each integral bounded by the full-circle integral of \(|K_N|^2\),
\[
 \begin{split}
 \sum_{q\in{\cal Q}_Q}\sum_a^*
 \int_{|\theta|\le1/(q\sqrt N)}
 \left|\frac{\mu(q)}{\phi(q)}K_N(\theta)\right|^2d\theta
 &\le N\sum_{q\in{\cal Q}_Q}\frac{\mu(q)^2}{\phi(q)}\\
 &\ll N.
 \end{split}
 \tag{D}
\]
Combining (B) and (D) with \(|u-v|^2\le2|u|^2+2|v|^2\) proves
\[
 \boxed{\quad
 \sum_{q\in{\cal Q}_Q}\sum_a^*
 \int_{|\theta|\le1/(q\sqrt N)}|R_{q,a}(\theta)|^2\,d\theta
 \ll NL.\quad}
 \tag{E}
\]

## 3. Vaughan converts (E) to the fourth-moment baseline

Since \(q\le\sqrt N\), the arc radius satisfies \(1/(q\sqrt N)\le q^{-2}\). For \(Q\le N^{2/5}\) and \(q\asymp Q\), all three terms of (V) are \(O(N/\sqrt Q)\). Also
\[
 \left|\frac{\mu(q)}{\phi(q)}K_N(\theta)\right|
 \le\frac N{\phi(q)}
 \ll \frac{NL}{Q}.
\]
It follows that
\[
 \sup_{\substack{q\in{\cal Q}_Q,\ a\bmod q\ {\rm reduced}\\
                  |\theta|\le1/(q\sqrt N)}}
 |R_{q,a}(\theta)|^2
 \ll\frac{N^2L^8}{Q}.
\]
Multiplication by (E) proves (A). The restriction \(Q\le N^{2/5}\) keeps Vaughan's \(N^{4/5}\) term within this particular expression; for larger blocks one must retain that term. The \(N^{o(1)}\) range under discussion satisfies the restriction for all sufficiently large \(N\).

This proves an available upper bound. It gives no lower bound of the same order and no statement that a different estimate cannot improve it.

## 4. Exact corrections to the AP-variance argument

### 4.1 The principal term is present

For a clipped finite interval \(I\subseteq[1,N]\), let \(H=\#I\),
\[
 S_{\chi,q}(I)=\sum_{n\in I}\Lambda(n)\chi(n),\qquad
 \Delta_b(I)=\sum_{\substack{n\in I\\n\equiv b\bmod q}}\Lambda(n)
             -\frac{H}{\phi(q)}1_{(b,q)=1}.
\]
Character orthogonality gives exactly
\[
 \sum_{b\bmod q}^{*}|\Delta_b(I)|^2
 =\frac1{\phi(q)}
 \left(
   |S_{\chi_0,q}(I)-H|^2+
   \sum_{\chi\ne\chi_0}|S_{\chi,q}(I)|^2
 \right).
 \tag{F}
\]
For the sum over all residues, add
\[
 \sum_{(b,q)>1}
 \left|\sum_{\substack{n\in I\\n\equiv b\bmod q}}\Lambda(n)\right|^2.
\]
Thus the principal-character term in the purported identity preceding equation (4) of SHARP_EXPONENT.md cannot be omitted. This is the same issue explicitly corrected in section 2 of RANK3_CONDUCTOR_SUM.md.

### 4.2 Full additive orthogonality requires the appropriate extension

For reduced \(a\),
\[
 \sum_b e(ab/q)\Delta_b(I)
 =\sum_{n\in I}\Lambda(n)e(an/q)-\frac{\mu(q)}{\phi(q)}H.
\]
For nonreduced \(a\), the model coefficient on the right is \(c_q(a)/\phi(q)\), where \(c_q\) is the Ramanujan sum, rather than \(\mu(q)/\phi(q)\). One may bound the reduced sum by the sum over all \(a\) of this extended transform and then use
\[
 \sum_{a\bmod q}\left|\sum_b e(ab/q)\Delta_b(I)\right|^2
 =q\sum_{b\bmod q}|\Delta_b(I)|^2.
 \tag{G}
\]
The extension is legitimate for an upper bound, but it changes the definition outside the reduced residues. The same fixed-\(\mu(q)\) residual is not represented by this identity for all \(a\).

### 4.3 Repeated conductors are not removed by a logarithmic bookkeeping cost

A primitive character of fixed conductor \(d\) induces a character for every multiple \(q\) of \(d\). Before handling the missing prime-power coefficients, its weight in a dyadic AP variance is
\[
 W_Q(d)=\sum_{\substack{Q\le q<2Q\\d\mid q}}\frac1{\phi(q)}.
 \tag{H}
\]
For fixed \(d\), this has a positive lower bound of order \(1/d\) as \(Q\) grows: use \(1/\phi(q)\ge1/(2Q)\) and count the multiples of \(d\). For example, \(W_Q(d)\ge1/(4d)\) for \(Q\) sufficiently large compared with \(d\). It is not \(O((\log Q)/Q)\).

Consequently a primitive large sieve with conductor bound \(2Q\), followed by a claimed global factor \(1/Q\), does not establish equation (4). Correctly counting imprimitive repetitions leaves small-conductor terms to estimate. The different reduced-additive estimate (E) does not imply the asserted AP variance estimate and does not repair that assertion.

### 4.4 Endpoints and the meaning of the conclusion

Gallagher must be applied to the finite coefficient sequence supported on \(1\le n\le N\). Its interval sum is clipped to that support, and the main-model coefficient is the actual count \(H\). With interval length \(h\), the integrating variable runs over a support contained in \([1-h,N]\); neither replacing it by \([0,N]\) nor always subtracting \(h\) is an exact identity without an additional error estimate.

A zero-free upper restriction on \(\beta\) supplies an upper envelope for \(N^{2(\beta-1)}\). It does not establish a zero at the envelope or a lower bound for a variance. In particular the inference written with a lower-bound sign after a zero-free upper bound in SHARP_EXPONENT.md section 1.2 is not valid as stated. No claim here settles what an additional zero-density estimate can achieve. The broad assertion that density estimates add nothing near \(\sigma=1\), and the universal route-closure conclusion built from it, remain unsupported by the displayed calculations.

## Appendix A. A Gauss-first Gallagher proof of the same baseline

This appendix is unnecessary for (A). It explains why retaining reduced numerators and their Gauss factors gives a valid large-sieve route after the false AP-variance reduction is dropped.

Set \(h=Q\sqrt N/2\) and \(I_t=(t,t+h]\cap[1,N]\), interpreted as the integers in that interval; put \(H_t=\#I_t\). Since \(q\ge Q\), each required frequency interval is contained in \(|\theta|\le1/(2h)\). Gallagher bounds the left side of (E) by
\[
 \ll h^{-2}\int_{\mathbb R}
       \sum_{q\in{\cal Q}_Q}\sum_a^*|A_{q,a}(t)|^2\,dt,
 \quad
 A_{q,a}(t)=
 \sum_{n\in I_t}\Lambda(n)e(an/q)-\frac{\mu(q)}{\phi(q)}H_t.
 \tag{I}
\]
All interval sums vanish outside \([1-h,N]\).

### A.1 Exact reduced-numerator diagonalization

Remove from \(A_{q,a}\) the prime powers not coprime to \(q\), obtaining \(A^{\rm cop}_{q,a}\). The Gauss expansion over characters modulo \(q\), followed by orthogonality over reduced \(a\), gives
\[
 \sum_a^*|A^{\rm cop}_{q,a}(t)|^2
 =
 \frac1{\phi(q)}
 \left[
  \mu(q)^2|S_{\chi_0,q}(I_t)-H_t|^2+
  \sum_{\chi\ne\chi_0}|\tau_q(\bar\chi)|^2|S_{\chi,q}(I_t)|^2
 \right].
 \tag{J}
\]
The twisting identity
\(\tau_{q,a}(\bar\chi)=\chi(a)\tau_q(\bar\chi)\) requires only \((a,q)=1\), not primitivity. This is the correction in RANK3_COMPOSITE_CROSS_TERM.md section 1.

If \(\chi\bmod q\) is induced by a primitive \(\chi^*\bmod d\), then
\[
 \tau_q(\chi)
 =\mu(q/d)\chi^*(q/d)\tau_d(\chi^*).
 \tag{K}
\]
In particular its squared modulus is \(d\) when \(q=dm\), \(m\) is squarefree, and \((m,d)=1\); it is zero otherwise. For completeness, (K) follows by writing
\[
 1_{(n,q)=1}\chi^*(n)
 =\chi^*(n)
   \sum_{\substack{e\mid(n,\operatorname{rad}(q))\\(e,d)=1}}\mu(e).
\]
For a term \(e\), substitute \(n=ek\); \(q/e\) is a multiple of \(d\). Splitting the resulting exponential sum into primitive periods of length \(d\) produces a vanishing geometric sum unless \(q/e=d\). The only possible surviving term is \(e=q/d\), giving (K). This proof also handles nonsquarefree \(q\); only the nonzero cases carry a conductor weight.

### A.2 Prime-power errors are harmless here

For every \(t\) and every inducing character,
\[
 |S_{\chi,q}(I_t)-S_{\chi^*,d}(I_t)|
 \le B_q,\qquad
 B_q:=\sum_{\substack{p^k\le N\\p\mid q}}\log p
 \le \omega(q)L\ll L^2.
\]
The noncoprime additive part is bounded by \(B_q\) as well. Character orthogonality also yields
\[
 \sum_{\chi\bmod q}|\tau_q(\chi)|^2=\phi(q)^2.
\]
Thus applying \(|u+v|^2\le2|u|^2+2|v|^2\) before summing, both the induction errors and the removed noncoprime terms have integrated cost
\[
 \ll (N+h)\sum_{q\in{\cal Q}_Q}\phi(q)B_q^2
 \ll NQ^2L^4.
 \tag{L}
\]
After the factor \(h^{-2}\) this is \(O(L^4)\), which is \(O(NL)\).

### A.3 The conductor factor now matches the primitive large sieve

Retaining the Gauss factor, the total weight of a primitive character of conductor \(d\) is at most
\[
 \frac d{\phi(d)}
 \sum_{\substack{Q/d\le m<2Q/d\\(m,d)=1}}
 \frac{\mu(m)^2}{\phi(m)}
 \ll \frac d{\phi(d)}
 \tag{M}
\]
by (C). This is exactly the weight in (LS), up to an absolute constant. It is not the weight (H) of the AP variance.

For a fixed \(t\), apply (LS) to the coefficients
\(\Lambda(n)1_{n\in I_t}\), with conductor bound \(2Q\). The sequence lies in an interval of length at most \(h+1\). Integrating and using
\(\int_{\mathbb R}1_{n\in I_t}\,dt=h\) gives
\[
 \begin{split}
 \int\sum_{d\le2Q}\frac d{\phi(d)}
       \sum_{\chi^*\bmod d}^{\rm primitive}
       \left|\sum_{n\in I_t}\Lambda(n)\chi^*(n)\right|^2dt
 &\ll (h+1+4Q^2)h\sum_{n\le N}\Lambda(n)^2\\
 &\ll Nh^2L,
 \end{split}
 \tag{N}
\]
because \(Q\le\sqrt N\) ensures \(Q^2\ll h\). The principal conductor can be omitted from this line; its centered version is dealt with next.

### A.4 Keep and bound the centered principal term

After the same prime-power removal, the principal interval expression is
\[
 S_1(I_t)-H_t,\qquad S_1(I_t)=\sum_{n\in I_t}\Lambda(n).
\]
Its modulus weight is \(\sum_{q\in{\cal Q}_Q}\mu(q)^2/\phi(q)\ll1\). Cauchy and \(H_t\le h+1\) yield
\[
 \begin{split}
 \int|S_1(I_t)-H_t|^2dt
 &\le2(h+1)h\sum_{n\le N}\Lambda(n)^2
       +2(N+h)(h+1)^2\\
 &\ll Nh^2L.
 \end{split}
 \tag{O}
\]
This estimate uses no short-interval prime number theorem. Equations (I) through (O) give \(O(NL+L^4)=O(NL)\), reproducing (E).

## Appendix B. A separate scope note on the old constructive sequence attempt

This does not reopen the settled Theorem B in RESULTS.md and REFEREE.md. That theorem uses a Mellin-pole contradiction to obtain an unbounded sequence and does not depend on the later constructive proposal.

THEOREM_B_SEQUENCE.md section 3 instead claims an absolutely convergent zero expansion for \(I(x)\). Its displayed residue coefficient is
\[
 \frac{\rho-1}{2\rho(\rho+1)}.
\]
For large \(|\operatorname{Im}\rho|\), this has size \(\asymp1/|\operatorname{Im}\rho|\), not \(O(|\operatorname{Im}\rho|^{-2})\). The numerator was lost in the stated absolute-convergence argument; the accompanying use of an \(O(\log T)\) zero count on a dyadic range also confuses a unit-height count with the count up to height \(T\).

Therefore the claimed absolute convergence and the constructive resonance derivation based on it are not established. A controlled truncated or sufficiently smoothed explicit formula is needed before discussing isolation of a witness zero or simultaneous phases. This is a limitation of that additional constructive route, not a criticism of the established nonconstructive lower bound.
