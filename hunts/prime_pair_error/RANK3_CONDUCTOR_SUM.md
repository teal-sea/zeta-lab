# Rank 3's mixed moment over the complete modulus range, organized by conductor

2026-09-11. This document finishes the estimate that
`RANK3_COMPOSITE_CROSS_TERM.md` section 5 left as its one remaining step:
carry the exact conductor-weighted identity (CT0) over the complete range
\(2\le q\le R_0\), and read off an unconditional bound for the rank-3 mixed
moment \(\sum_{2\le q\le R_0}U_{(q)}\) of `UPPER_BOUND.md` (23). Along the way
it corrects the Barban-Davenport-Halberstam statement that
`RANK3_MEAN_VALUE_TOOLS.md` section 1 records and
`RANK3_POLYRANGE_TINT_CHECK.md` section 3 uses, because as written that
statement has no Siegel-Walfisz floor and its \(Q=1\) case is stronger than
what RH would give.

**Result, stated first.** For every fixed \(A>0\), unconditionally,
\[
 \boxed{\ \sum_{q=2}^{R_0}U_{(q)}
 \ \le\ 4(C_3-1)\,T_N
 \ +\ O_A\!\big(N^3L^{-A}\big)
 \ +\ O\!\big(N^2L^2(\log\log N)^2\big),
 \qquad C_3=\prod_p\Big(1+\frac1{(p-1)^3}\Big)=2.3009\ldots\ }
\tag{K}
\]
where \(T_N\) is the \(q=1\) quantity of `UPPER_BOUND.md` (29) and
\(L=\log N\). Since \(T_N\ll_HN^3L^{-2H}\) by (SW) at \(q=1\)
(`UPPER_BOUND.md` section 7), this gives
\(\sum_{2\le q\le R_0}U_{(q)}\ll_AN^3L^{-A}+N^2L^{2+o(1)}\) for every fixed
\(A\). In the other direction, the single modulus \(q=2\) already gives
\[
 \sum_{q=2}^{R_0}U_{(q)}\ \ge\ U_{(2)}\ \ge\ \tfrac12T_N-O(N^2L).
\tag{K'}
\]
So the rank-3 mixed moment is pinned two-sidedly to rank 1's own quantity:
its bound is the same order as rank 1's, and any fixed power saving on it,
\(\sum_{2\le q\le R_0}U_{(q)}\ll N^{3-\delta}\), forces
\(\zeta(s)\ne0\) for \(\operatorname{Re}s>1-\delta/2\) (section 5). The
composite-modulus cancellation of `RANK3_COMPOSITE_CROSS_TERM.md` is used
in full and does exactly what it can: it makes the character part of the sum
smaller than the principal part, which is the part no averaging over \(q\)
can remove. Section 6 records what this does to the budget (23): the whole
\(U\)-side is now bounded at rank 1's order, and the only component of (23)
without any estimate is the fourth moment \(Z_{q\le R_0}\).

Everything here is derived, one route, with a finite check in section 7.
Nothing here is evidence about the zeros of \(\zeta\) or of any
\(L\)-function; the one implication involving zeros (section 5) is a
deduction from a hypothetical bound, in the same form `UPPER_BOUND.md`
section 1 already states for the total.

## 1. Inputs, all already on this branch or classical

Notation is `RANK3_ROUTE_D.md`'s and `RANK3_CROSS_TERM_CANCELLATION.md`'s:
\(Q=\lfloor\sqrt N/3\rfloor\), \(R_0=Q/L\), \(U_{(q)}\), \(T_N(q,a)\),
\(R^{(1)}_{q,a},R^{(2)}_{q,a}\), \(\rho_2(q)\), \(\Sigma_{\rm diag}(q)\),
\(\Sigma_{\rm cross}(q)\), \(E(q)\), and for a character \(\chi\bmod q\),
\(\psi(t,\chi)=\sum_{n\le t}\Lambda(n)\chi(n)\) and
\(M_\chi=\int_{\mathbb T}|K_NL(\chi)|^2\). By the same Parseval computation
as (D5), for every character,
\[
 M_\chi=\sum_{t=1}^N|\psi(t,\chi)|^2+\sum_{t=1}^{N-1}|\psi(N,\chi)-\psi(t,\chi)|^2
 \ \le\ 3\sum_{t=1}^N|\psi(t,\chi)|^2+2N|\psi(N,\chi)|^2.
\tag{1}
\]

- (T2), `RANK3_ARC_TRANSFER.md`: \(U_{(q)}\le\sum_a^*T_N(q,a)\), by
  monotonicity of a nonnegative integrand. No transfer term.
- (D10), `RANK3_ROUTE_D.md`, in its pre-(D8) form: since
  \(R_{q,a}=R^{(1)}_{q,a}+R^{(2)}_{q,a}\) with \(|R^{(2)}_{q,a}|\le\rho_2(q)\),
  \[
   \sum_a^*T_N(q,a)\le\frac{2\mu(q)^2}{\phi(q)^2}\big(\Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)\big)
   +\frac{2\mu(q)^2\rho_2(q)^2N}{\phi(q)}.
  \tag{2}
  \]
- (CT0), `RANK3_COMPOSITE_CROSS_TERM.md`, for squarefree \(q\):
  \[
   \Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)
   =\frac{E(q)}{\phi(q)}+\frac1{\phi(q)}\sum_{\chi\ne\chi_0}\operatorname{cond}(\chi)M_\chi.
  \tag{3}
  \]
  This is the exact identity, before any of the conductor weights is
  discarded. Nothing below replaces \(\operatorname{cond}(\chi)\) by \(q\).
- (CC-E), `RANK3_CROSS_TERM_CANCELLATION.md`, in the form
  \(\sqrt{E(q)}\le\sqrt{T_N}+\rho_2(q)\sqrt N\), hence
  \(E(q)\le2T_N+2\rho_2(q)^2N\). (Proof: \(\varepsilon=(F_N-K_N)-S^{(2)}\)
  with \(|S^{(2)}|\le\rho_2(q)\) pointwise, and the triangle inequality in
  \(L^2(|K_N|^2d\beta)\).)
- (D3): \(\rho_2(q)\ll L\log(2q)\). (15) of `UPPER_BOUND.md`:
  \(q/\phi(q)\le\zeta(2)(1+\log q)\).
- Non-squarefree \(q\) contribute \(U_{(q)}=0\) (\(\mu(q)=0\)). So every sum
  over \(q\) below runs over squarefree \(q\).
- The large sieve for primitive characters (Iwaniec and Kowalski, *Analytic
  Number Theory*, Theorem 7.13; Davenport, *Multiplicative Number Theory*,
  Chapter 27): for any complex \(a_n\),
  \[
   \sum_{q\le Q}\frac q{\phi(q)}\sum_{\chi\ \mathrm{prim}\bmod q}
   \Big|\sum_{n\le t}a_n\chi(n)\Big|^2\le(t+Q^2)\sum_{n\le t}|a_n|^2.
  \tag{LS*}
  \]
  With \(a_n=\Lambda(n)\) the right side is \((t+Q^2)d_t\), \(d_t\le t\log t\).
- Siegel-Walfisz in character form (Davenport, Chapter 22): for fixed \(B\),
  every nonprincipal \(\chi\) of conductor \(q\le(\log x)^B\) has
  \(\psi(x,\chi)\ll_Bx\exp(-c_B\sqrt{\log x})\), ineffectively. Hence, for
  fixed \(B,H\), uniformly for \(1\le t\le N\) and every such \(\chi\),
  \[
   |\psi(t,\chi)|\ll_{B,H}NL^{-H},
  \tag{SW\(\chi\)}
  \]
  by treating \(t\le NL^{-H}\) trivially (\(|\psi(t,\chi)|\le\psi(t)\ll t\))
  and using \(\log t\asymp L\) above that point. This is the same device
  `UPPER_BOUND.md` section 1 uses for (SW).

## 2. The Barban-Davenport-Halberstam range, corrected

`RANK3_MEAN_VALUE_TOOLS.md` section 1 records (BDH) as
\(D(x,Q)=\sum_{q\le Q}\sum_a^*(\psi(x;q,a)-x/\phi(q))^2\ll Qx\log x\)
"uniformly for \(1\le Q\le x\)", and `RANK3_POLYRANGE_TINT_CHECK.md`
section 3 applies it at every \(Q\) from \(\lfloor L^B\rfloor\) upward.
At \(Q=1\) that statement reads \((\psi(x)-x)^2\ll x\log x\), which is
stronger than the \(x\log^4x\) that RH itself gives (`UPPER_BOUND.md`
section 7), so it cannot be the unconditional theorem. The theorem
(Davenport, Chapter 29) is stated for \(x(\log x)^{-A}\le Q\le x\); below
that range it carries a floor. The floor is visible from the character
decomposition, which is also the computation this document needs, so here
it is in full.

By orthogonality, \(\psi(x;q,a)=\phi(q)^{-1}\sum_\chi\bar\chi(a)\psi(x,\chi)\),
and \(\sum_a^*\bar\chi(a)=0\) for \(\chi\ne\chi_0\), so for every \(q\)
\[
 \sum_{a\bmod q}^*\Big(\psi(x;q,a)-\frac x{\phi(q)}\Big)^2
 =\frac{(\psi(x,\chi_0)-x)^2}{\phi(q)}+\frac1{\phi(q)}\sum_{\chi\ne\chi_0}|\psi(x,\chi)|^2.
\tag{4}
\]
The first term is the **principal contribution**: \(\psi(x,\chi_0)-x=
(\psi(x)-x)-r_q(x)\) with \(0\le r_q(x)\le\rho_2(q)\), so it is
\((\psi(x)-x)^2/\phi(q)\) up to \(O(\rho_2(q)(|\psi(x)-x|+\rho_2(q))/\phi(q))\).
It is present at every modulus and it does not shrink as \(q\) grows. Summed
over \(q\le Q\) with the weight \(1/\phi(q)\) it contributes
\((\psi(x)-x)^2\log(2Q)\), and unconditionally that is
\(\ll_Ax^2(\log x)^{-A}\log(2Q)\) and nothing better without a zero-free
strip.

Each nonprincipal \(\chi\bmod q\) is induced by a unique primitive
\(\chi^*\bmod q^*\), \(q^*\mid q\), \(q^*\ge2\), and
\(\psi(x,\chi)=\psi(x,\chi^*)-\sum_{n\le x,(n,q)>1}\Lambda(n)\chi^*(n)\), the
correction being at most \(\rho_2(q)\) in modulus. Organizing the second term
of (4) by conductor and summing over \(q\le Q\), the weight on
\(|\psi(x,\chi^*)|^2\) is \(\sum_{q\le Q,\,q^*\mid q}1/\phi(q)\le
\phi(q^*)^{-1}\sum_{d\le Q/q^*}1/\phi(d)\ll\phi(q^*)^{-1}\log(2Q/q^*)\).
Split at \(q^*\le(\log x)^B\): (SW\(\chi\)) with \(t=x\) gives
\(\ll x^2(\log x)^{2B-2H}\) for that part. Above it, partial summation of
(LS*) against the weight \(\log(2Q/q^*)/\phi(q^*)\) gives, block by block,
\(\sum_{Q'\ \mathrm{dyadic}}(x+Q'^2)x\log x\,\log(2Q/Q')/Q'\ll
x^2(\log x)^{2-B}+Qx\log x\), the first term coming from the block just
above \((\log x)^B\). Altogether, for every fixed \(A\) and every
\(1\le Q\le x\),
\[
 \boxed{\ D(x,Q)\ \ll_A\ Qx\log x\ +\ x^2(\log x)^{-A}.\ }
\tag{BDH\(^\prime\)}
\]
The second term is the correction. It is not removable by any choice of
\(Q\): it is the principal contribution plus the conductors just above the
Siegel-Walfisz range, and both are exactly rank 1's kind of obstruction.

**Consequence for `RANK3_POLYRANGE_TINT_CHECK.md` section 3.** That
section's running sum should read \(F(Q)\ll QN^2L+N^3L^{-A}\), not
\(QN^2L\). Carried through its own Abel summation against
\(w(q)=\mu(q)^2/\phi(q)^2\), the floor picks up the weight
\(W(A)\asymp(\log\log N)^2L^{-2B}\), and the corrected conclusion is
\[
 S(N,B)\ \ll_A\ N^2L^{1-B}(\log\log N)^2+N^3L^{-A}(\log\log N)^2.
\]
The boxed claim there, \(S(N,B)=O_\epsilon(N^{2+\epsilon})\), does not
follow, and cannot: by (4), \(S(N,B)\ge\sum_{A<q\le R_0}\mu(q)^2\phi(q)^{-3}
\sum_{t\le N}(\psi(t,\chi_0)-t)^2\gg L^{-2B}\sum_{t\le N}(\psi(t)-t)^2
-O(NL^{2-2B})\), and section 5 shows \(\sum_{t\le N}(\psi(t)-t)^2\ll
N^{3-\delta}\) is a zero-free half-plane. So that box was an RH-strength
statement resting on the uncorrected range. The document's numerical
section 4, which found \(S(N,1)/N^2\) rising with \(N\), is consistent with
the corrected form and was right not to read its own data as confirming
the box. `RANK3_CROSS_TERM_CANCELLATION.md` section 5 and
`RANK3_MEAN_VALUE_TOOLS.md` (E1)-(E2) inherit the same correction: the
prime-\(q\) sub-sum is \(O_A(N^3L^{-A})+O(N^2L^{2+o(1)})\), not
\(O_\epsilon(N^{2+\epsilon})\), and (E2)'s \(N^{5/2}\) is
\(N^{5/2}+N^3L^{-A}\). None of the *identities* in those documents is
affected; only the bounds that consumed (BDH) below its range.

## 3. The exact decomposition of \(\sum_a^*T_N(q,a)\)

Insert (3) into (2). For squarefree \(q\ge2\),
\[
 \sum_a^*T_N(q,a)\ \le\
 \underbrace{\frac{2E(q)}{\phi(q)^3}}_{\text{principal}}
 +\underbrace{\frac2{\phi(q)^3}\sum_{\chi\ne\chi_0}\operatorname{cond}(\chi)M_\chi}_{\text{characters}}
 +\underbrace{\frac{2\rho_2(q)^2N}{\phi(q)}}_{\text{remainder}}.
\tag{5}
\]
This is (2) with (CT0) substituted and nothing discarded. Writing the
character part by conductor: for \(\chi\) induced by \(\chi^*\bmod q^*\),
the coefficient sequences of \(K_NL(\chi)\) and \(K_NL(\chi^*)\) differ by
at most \(\rho_2(q)\) in every entry (the \(2N-1\) entries are partial sums
of \(\Lambda(n)\chi(n)\) and their complements, by (1)), so by the triangle
inequality in \(\ell^2\),
\[
 M_\chi\le\big(\sqrt{M_{\chi^*}}+\rho_2(q)\sqrt{2N}\big)^2\le2M_{\chi^*}+4N\rho_2(q)^2,
\tag{6}
\]
where \(M_{\chi^*}\) is the moment (1) of the primitive character itself.
Section 7 checks (6) at \(q\in\{6,10,15\}\); the measured ratio of the two
sides is below \(0.46\).

## 4. The sum over \(2\le q\le R_0\)

**The principal part.** By (CC-E) in the form \(E(q)\le2T_N+2\rho_2(q)^2N\),
\[
 \sum_{q=2}^{R_0}\frac{2\mu(q)^2E(q)}{\phi(q)^3}
 \le4T_N\sum_{\substack{q\ge2\\ q\ \mathrm{squarefree}}}\frac1{\phi(q)^3}
 +4N\sum_{q\ge2}\frac{\mu(q)^2\rho_2(q)^2}{\phi(q)^3}
 =4(C_3-1)\,T_N+O(NL^2),
\tag{7}
\]
since \(\sum_{q\ \mathrm{sqfree}}\phi(q)^{-3}=\prod_p(1+(p-1)^{-3})=C_3\)
and \(\sum_q\log^2(2q)(1+\log q)^3/q^3\) converges. The \(q=2\) term alone
is \(2E(2)/1\le4T_N+O(NL^2)\), and \(C_3-1=1.3009\ldots\) is dominated by it.
This is the part of rank 3 that is rank 1 in disguise: the principal
character of every modulus carries a copy of \(T_N\), and the weights
\(\phi(q)^{-3}\) sum to a constant rather than decaying to zero over the
range. No cancellation identity touches it, because (3) already isolates
it exactly.

**The character part, reorganized by conductor.** By (6),
\[
 \sum_{q=2}^{R_0}\frac{2\mu(q)^2}{\phi(q)^3}\sum_{\chi\ne\chi_0}\operatorname{cond}(\chi)M_\chi
 \le4\sum_{q=2}^{R_0}\frac{\mu(q)^2}{\phi(q)^3}\sum_{\substack{q^*\mid q\\ q^*\ge2}}q^*
 \sum_{\chi^*\ \mathrm{prim}\bmod q^*}M_{\chi^*}
 +8N\sum_{q=2}^{R_0}\frac{\mu(q)^2\rho_2(q)^2}{\phi(q)^3}\sum_{q^*\mid q}q^*\phi(q^*).
\]
The last sum is at most \(q^2\), so the second term is
\(\ll NL^2\sum_{q\le R_0}\log^2(2q)(1+\log q)^3/q\ll NL^8\). In the first,
swap the order: a conductor \(q^*\) is counted once for every squarefree
multiple \(q=q^*d\le R_0\) with \((d,q^*)=1\), so its total weight is
\[
 \sum_{\substack{q\le R_0\\ q^*\mid q}}\frac{\mu(q)^2}{\phi(q)^3}
 =\frac{\mu(q^*)^2}{\phi(q^*)^3}\sum_{\substack{d\le R_0/q^*\\ (d,q^*)=1}}\frac{\mu(d)^2}{\phi(d)^3}
 \le\frac{C_3}{\phi(q^*)^3}.
\]
Therefore
\[
 \text{character part}\ \le\ 4C_3\,\Psi+O(NL^8),\qquad
 \Psi:=\sum_{2\le q^*\le R_0}\frac{q^*}{\phi(q^*)^3}\sum_{\chi^*\ \mathrm{prim}\bmod q^*}M_{\chi^*}.
\tag{8}
\]
This is the reorganization the task asked for: every primitive character
appears once, with weight \(q^*/\phi(q^*)^3\asymp(q^*)^{-2}\) up to
\(\log\log\), **before** anything is bounded. Discarding
\(\operatorname{cond}(\chi)\le q\) first, as (CT2) does, would instead put
weight \(\asymp1/q\) on every modulus containing the character, and the
same conductor would be counted once per multiple; that is the \(\log\log q\)
bookkeeping `RANK3_COMPOSITE_CROSS_TERM.md` section 5 worried about, and it
never arises here.

**Small conductors, \(2\le q^*\le A:=\lfloor L^B\rfloor\).** By (1) and
(SW\(\chi\)), \(M_{\chi^*}\le5N\max_{t\le N}|\psi(t,\chi^*)|^2\ll_{B,H}N^3L^{-2H}\)
for every primitive \(\chi^*\) of conductor \(\le A\), and there are
\(\le\phi(q^*)\) of them mod \(q^*\), so
\[
 \Psi_{\le A}\ll_{B,H}N^3L^{-2H}\sum_{q^*\le A}\frac{q^*}{\phi(q^*)^2}
 \ll N^3L^{-2H}\sum_{q^*\le A}\frac{(1+\log q^*)^2}{q^*}
 \ll N^3L^{-2H}(\log\log N)^3.
\tag{9}
\]

**Large conductors, \(A<q^*\le R_0\).** Fix \(t\le N\) and put
\(g_t(q^*)=(q^*/\phi(q^*))\sum_{\chi^*}|\psi(t,\chi^*)|^2\ge0\), so that
(LS*) reads \(G_t(Q):=\sum_{q^*\le Q}g_t(q^*)\le(t+Q^2)t\log t\). The weight
\(q^*/\phi(q^*)^3=g\)-weight times \(1/\phi(q^*)^2\), and
\(1/\phi(q)^2\le W(q):=K(\log\log(q+16))^2/q^2\) with \(K\) absolute
(Rosser-Schoenfeld, \(\phi(q)\gg q/\log\log q\)), \(W\) decreasing. Abel
summation from \(A\) with \(F(Q)=G_t(Q)-G_t(A)\in[0,G_t(Q)]\):
\[
 \sum_{A<q^*\le R_0}\frac{q^*}{\phi(q^*)^3}\sum_{\chi^*}|\psi(t,\chi^*)|^2
 \le W(R_0)G_t(R_0)+\sum_{Q=A+1}^{R_0-1}\big(W(Q)-W(Q+1)\big)G_t(Q)
\]
\[
 \ll(\log\log N)^2\Big[\frac{(t+R_0^2)t\log t}{R_0^2}
 +\sum_{Q>A}\frac{(t+Q^2)t\log t}{Q^3}\Big]
 \ll(\log\log N)^2\Big[\frac{t^2L}{A^2}+tL^2\Big].
\tag{10}
\]
The \(t^2L/A^2\) term is the block of conductors just above \(A\), where
(LS*) saves nothing because \(A^2\ll t\); the \(tL^2\) term is the sum of
\(1/Q\) up to \(R_0\). Applying (10) to the two sums in (1), once summed over
\(t\le N\) and once at \(t=N\) with the factor \(2N\):
\[
 \Psi_{>A}\ll(\log\log N)^2\big[N^3L^{1-2B}+N^2L^2\big].
\tag{11}
\]

**The remainder.** \(2N\sum_q\mu(q)^2\rho_2(q)^2/\phi(q)\ll NL^6\) is (T5).

**Assembly.** (T2), (5), (7), (8), (9), (11) and (T5) give
\[
 \sum_{q=2}^{R_0}U_{(q)}\le4(C_3-1)T_N
 +O_{B,H}\big(N^3L^{-2H}(\log\log N)^3\big)
 +O\big(N^3L^{1-2B}(\log\log N)^2\big)
 +O\big(N^2L^2(\log\log N)^2\big)+O(NL^8).
\]
Given \(A\), take \(B=A+1\), \(H=A\); this is (K). With \(T_N\ll_HN^3L^{-2H}\)
from `UPPER_BOUND.md` section 7, every term but the last two is
\(O_A(N^3L^{-A})\). Constants have not been optimized: the factor 4 in (7)
is two applications of \((x+y)^2\le2x^2+2y^2\) that an \(\ell^2\) triangle
inequality would reduce to \(1+\eta\).

## 5. The lower bound, and what a power saving would mean

At \(q=2\): \(\phi(2)=1\), \(P_{2,1}=-K_N\), and the coefficient of
\(R_{2,1}=F_N(\tfrac12+\beta)+K_N(\beta)\) at \(n\) is
\(\Lambda(n)(-1)^n+1=-(\Lambda(n)-1)+2\Lambda(n)\mathbf1_{2\mid n}\). So
\(K_NR_{2,1}=-K_N(F_N-K_N)+2K_N\mathcal E\) with
\(\mathcal E(\beta)=\sum_{2^k\le N}\log2\cdot\exp1(2^k\beta)\),
\(|\mathcal E|\le L\), and
\[
 T_N(2,1)=\int_{\mathbb T}|K_N|^2|R_{2,1}|^2\ge\big(\sqrt{T_N}-2L\sqrt N\big)^2\ge\tfrac12T_N-4NL^2.
\]
The arc restriction costs, exactly as in `UPPER_BOUND.md` (30) with
\(\delta_2=Q/(2N)\): \(T_N(2,1)-U_{(2)}\le(N/Q)^2\int_{\mathbb T}|R_{2,1}|^2
\le(N/Q)^2(2d_N+2N)\ll N^2L\). Hence (K'). Section 7 measures
\(U_{(2)}/T_N\) at \(N\) up to \(2\times10^4\): it is above \(1\) and
decreasing toward it, and (K') holds at every \(N\) tried.

Now suppose \(\sum_{2\le q\le R_0}U_{(q)}\ll N^{3-\delta}\) for one fixed
\(0<\delta<1\). By (K'), \(T_N\ll N^{3-\delta}\), so
\(\sum_{t\le N}\Delta(t)^2\ll N^{3-\delta}\) with \(\Delta(t)=\psi(t)-t\).
For \(\sigma>1-\delta/2\), Cauchy-Schwarz on dyadic blocks gives
\(\int_X^{2X}|\Delta(x)|x^{-\sigma-1}dx\le X^{-\sigma-1}\sqrt{X\int_X^{2X}\Delta^2}
\ll X^{-\sigma-1}\sqrt{X\cdot X^{3-\delta}}=X^{1-\delta/2-\sigma}\), summable
over dyadic \(X\). So \(\int_1^\infty\Delta(x)x^{-s-1}dx\) converges
absolutely and is holomorphic in \(\operatorname{Re}s>1-\delta/2\), and
by \(-\zeta'/\zeta(s)=s/(s-1)+s\int_1^\infty\Delta(x)x^{-s-1}dx\)
(`CORRECTED_RH_BRIDGE.md` (20)), \(\zeta\) has no zero there. This is the
same deduction `UPPER_BOUND.md` section 1 makes for the total at exponent
\(2+\epsilon\) and `RESULTS.md` section 18 makes for Theorem B, applied at
exponent \(3-\delta\). It says nothing about whether such a strip exists;
it prices the improvement.

So (K) is the order this route can reach, and the reason is not the
cancellation of \(\Sigma_{\rm cross}\), which (3) handles exactly, nor the
imprimitive characters, which (8) handles exactly; it is the principal
character, present at every modulus with non-decaying total weight
\(4(C_3-1)\).

## 6. Effect on the complete error budget (23)

`UPPER_BOUND.md` (23): \(E(N)\le32U_Q+8Z_Q+4I_Q+O(N^2L^3)\), with
\(U_Q=U_1+\sum_{2\le q\le R_0}U_{(q)}+U_{q>R_0}\). Now
\[
 U_1\ll_HN^3L^{-2H}\ \text{(section 7 there)},\qquad
 \sum_{2\le q\le R_0}U_{(q)}\ll_AN^3L^{-A}+N^2L^{2+o(1)}\ \text{(this document)},\qquad
 U_{q>R_0}\ll N^2L^5\ \text{((27))}.
\]
So the entire mixed moment is bounded, unconditionally, for every fixed \(A\):
\[
 \boxed{\ 32U_Q\ll_AN^3L^{-A}+N^2L^5.\ }
\tag{12}
\]
The row "Other moments with \(q\le R_0\): no adequate estimate here" of
`UPPER_BOUND.md` section 8 is, on the \(U\)-side, now filled at rank 1's
order, and the composite squarefree moduli are included. What this does to
the total:

- **Nothing to the total order.** (23) still contains \(8Z_{q\le R_0}\),
  including \(q=1\), for which no identity and no estimate exist
  (`RANK3_ROUTE_D.md` section 7: no telescoping, no arc transfer); its
  trivial bound is \(Z_Q\le\sup|R|^2\sum_{q,a}\int_{I_{q,a}}|R_{q,a}|^2\ll N^3L\).
  So (23) yields \(E(N)\ll N^3L\), weaker than (1). The route through (23)
  cannot beat (1) until \(Z_{q\le R_0}\) is bounded below \(N^3L^{-C}\).
- **Even then it would not beat (1).** If \(Z_{q\le R_0}\) were bounded at
  rank 1's order, (23) would give \(E(N)\ll_AN^3L^{-A}+N^{13/5}L^6\), which
  is (1) again. A power saving on the total through (23) needs a power
  saving on \(U_1\), and by (K') equivalently on \(\sum_{2\le q\le R_0}U_{(q)}\),
  and section 5 prices that as a zero-free strip. This sharpens
  `RANK3_SCOPE.md` section 4, which said rank 3's closure was invisible in
  the final exponent while rank 1 stood: rank 3's \(U\)-side and rank 1 are
  one quantity, so the two cannot be closed separately at all.
- **The one live component is \(Z_{q\le R_0}\)**, and it is live in both
  directions: it has no upper bound below the trivial one and, unlike the
  \(U\)-side, no lower bound of the form (K') is written down for it here.

## 7. Finite checks

`rank3_conductor_sum_probe.py`, results in
`results_rank3_conductor_sum_probe.json`, numpy only, a few seconds:

- \(C_3=\prod_p(1+(p-1)^{-3})\) over primes below \(2\times10^5\):
  \(2.30096\ldots\); \(4(C_3-1)=5.2038\ldots\).
- The \(q=2\) pin at \(N\in\{120,10^3,5\times10^3,2\times10^4\}\):
  \(T_N\), the full-circle \(T_N(2,1)\) by the exact coefficient formula, the
  same quantity on an \(8N\)-point grid (agreeing to display precision), and
  the arc-restricted \(U_{(2)}\) at \(Q=\lfloor\sqrt N/3\rfloor\).
  \(U_{(2)}\ge\tfrac12T_N-4NL^2\) holds at every \(N\);
  \(U_{(2)}/T_N=7.73,\ 4.48,\ 1.67,\ 1.14\), decreasing toward \(1\) as the
  \(2K_N\mathcal E\) term loses weight. At \(N=120\) the full-circle value
  \(10385\) reproduces `results_rank3_arc_transfer_probe.json`.
- Conductor bookkeeping at \(N=3000\), \(q\in\{6,10,15\}\): every
  nonprincipal \(\chi\bmod q\) against the primitive \(\chi^*\) inducing it;
  the ratio \(M_\chi/(2M_{\chi^*}+4N\rho_2(q)^2)\) is at most \(0.46\), so
  (6) holds with room; the characters mod \(15\) are seen with conductors
  \(3\) (one), \(5\) (three) and \(15\) (three), as the reorganization in
  (8) requires.

These check identities, an inequality and one measured ratio at small
\(N\); they do not test any asymptotic statement.

## 8. Scope

This document is bookkeeping (orthogonality, induction of characters,
Abel summation) around two classical unconditional theorems, (LS*) and
Siegel-Walfisz, applied to identities already established on this branch.
It corrects one cited range and the three bounds that rested on it, and it
establishes an unconditional bound of rank 1's order for the rank-3 mixed
moment together with the matching lower bound. It proves no power saving
anywhere, claims none, and establishes nothing about the zeros of \(\zeta\)
or of any \(L\)-function.
