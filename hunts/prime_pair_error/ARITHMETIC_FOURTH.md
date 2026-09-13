# Vaughan blocks with the signed minor-arc kernel

2026-09-09. Base: `2da62eb9842db72d4f6bad09c6f13efe384d6ab7`.
This is the next arithmetic estimate for the original CHHL total error.
The level-set attempt in PR #209 is separate and unchanged.

**Outcome.** The complete critical Type II block estimate does not improve.
Two parts of the attempted integrated estimate do have smaller proved costs:
the proper-power divisor part of \(v_n\) costs
\(O_\epsilon(N^{12/5+\epsilon})\), and the
paired Möbius-label part of the large-prime block costs \(O(N^{11/5}L^5)\).
The remaining signed, prime-weighted four-Möbius sum is explicit below.
Trying to cancel it by solving for one Möbius variable leaves at most one
term whenever two specified large primes differ in the controlling block.
This supplies no cancellation. Absolute-value completion instead gives a
worse bound, with its precise cost in Section 6.

These are written arguments, with finite algebra checks. They are not a
formal proof or a novelty claim. No new upper bound for total \(E(N)\) is
claimed.

## 1. Exact arithmetic identity and blocks

Throughout \(N\ge36\) is an integer, \(L=\log N\),
\(U=V=\lfloor N^{2/5}\rfloor\), and \(Q=\lfloor\sqrt N/3\rfloor\).
No parameters are changed. Let \({\bf1}(n)=1\) and let \(\delta\) be the
identity for Dirichlet convolution. From
\({\bf1}*\Lambda=\log\) and \(\mu*{\bf1}=\delta\),
\[
\begin{split}
\Lambda={}&\Lambda_{\le V}+\mu_{\le U}*\log
 -\mu_{\le U}*{\bf1}*\Lambda_{\le V}
 +\mu_{>U}*{\bf1}*\Lambda_{>V}.                 \tag{1}
\end{split}
\]
Indeed, the second term minus the third is
\(\mu_{\le U}*{\bf1}*\Lambda_{>V}\). Adding the last term gives
\(\Lambda_{>V}\). The identity holds coefficient by coefficient, including
at 1, at the two truncation endpoints, and at every proper prime power.

Write the corresponding Fourier sums as
\[
 F_N=S_0+T_{\log}-T_{\rm prod}+T_{\rm II}.       \tag{2}
\]
The two Type I formulas, with their actual coefficients, are
\[
 T_{\log}=\sum_{d\le U}\mu(d)\sum_{a\le N/d}\log a\,e(da\alpha),
\quad
 T_{\rm prod}=\sum_{t\le UV}a_t\sum_{b\le N/t}e(tb\alpha),
\quad a_t=\sum_{\substack{dc=t\\d\le U,c\le V}}\mu(d)\Lambda(c).
                                                               \tag{3}
\]
Here \(e(x)=\exp(2\pi ix)\), \(S_0=\sum_{n\le V}\Lambda(n)e(n\alpha)\),
and
\[
 T_{\rm II}=\sum_{\substack{m>U,n>V\\mn\le N}}\mu(m)v_n e(mn\alpha),
 \qquad v_n=\sum_{\substack{d\mid n\\d>V}}\Lambda(d).       \tag{4}
\]
Use the disjoint dyadic intervals \((M,2M]\), \(M=2^jU\), and
\((K,2K]\), \(K=2^lV\), \(j,l\ge0\). Keep only nonempty blocks and put
\[
 B_{M,K}=\sum_{\substack{M<m\le2M, K<n\le2K\\mn\le N}}
             \mu(m)v_ne(mn\alpha),\qquad X=MK.
                                                               \tag{5}
\]
Thus \(X<N\), \(M\ge U\), \(K\ge V\); the number \(J\) of blocks is
\(O(L^2)\). We particularly try to improve the blocks
\[
       M=U,\qquad N/8\le UK\le N/2,                         \tag{6}
\]
with dyadic \(K\). This is the short Möbius-factor endpoint
\(M\asymp N^{2/5},K\asymp N^{3/5}\), at total product scale \(N\).
All other blocks remain in the final budget.

## 2. Exact minor kernel and the r=0 term

The major arcs are exactly those of `UPPER_BOUND.md`: reduced \(a/q\),
\(q\le Q\), with circular radius \(Q/(qN)\). They are disjoint since
\(2Q^2<N\). Define \(\mathcal K_Q(r)=\int_{\mathfrak m_Q}e(r\alpha)d\alpha\).
Integrating each major interval, then subtracting from the full circle,
proves
\[
 \mathcal K_Q(0)=1-\frac{2Q}{N}\sum_{q\le Q}\frac{\phi(q)}q,
                                                               \tag{7}
\]
and, for every nonzero integer \(r\),
\[
 \mathcal K_Q(r)=-\sum_{q\le Q}c_q(r)
       \frac{\sin(2\pi rQ/(qN))}{\pi r}.                    \tag{8}
\]
The arc at zero wraps around the endpoint, so it is included once. The
Ramanujan sum is \(c_q(r)=\sum_{a\bmod q}^*e(ar/q)\). It is real and even.

For any one of the actual blocks, expand before taking absolute values:
\[
 \int_{\mathfrak m_Q}|B_{M,K}|^4
 =\sum_{\substack{(m_i,n_i)\text{ in the block}\\1\le i\le4}}
    \prod_{i=1}^4\mu(m_i)v_{n_i}\,
    \mathcal K_Q(m_1n_1+m_2n_2-m_3n_3-m_4n_4).            \tag{9}
\]
All four constraints \(m_in_i\le N\) remain.
Let \(b_t=\sum_{mn=t\text{ in block}}\mu(m)v_n\),
\(a_s=\sum_{t+u=s}b_tb_u\), and \(A_r=\sum_s a_{s+r}a_s\), with zero
extension outside the support. Then (9) is
\[
 \mathcal K_Q(0)A_0+2\sum_{r=1}^{2N}\mathcal K_Q(r)A_r,
 \qquad A_0=\sum_sa_s^2=\int_{\mathbb T}|B_{M,K}|^4.       \tag{10}
\]
Thus the \(r=0\) term is separated without deleting the signed off-diagonal
sum. In particular \(r=0\) is not just the pairwise-equal index family.

## 3. The proper-power divisor part of v costs less than the block benchmark

Split (4) exactly as \(v_n=w_n+h_n\), where
\[
 w_n=\sum_{\substack{p>V\\p\mid n}}\log p,
 \qquad
 h_n=\sum_{\substack{a\ge2, p^a>V\\p^a\mid n}}\log p.   \tag{11}
\]
This partitions the divisors on which \(\Lambda\) is nonzero; it does not
replace \(\Lambda\) by a primes-only function. The names refer to the
divisor inside \(v_n\): proper powers of the total argument \(mn\) can
also occur in the \(w_n\) block, for example \(m=n=p>V\). They remain
in the exact identity (1). For the Type II support,
\[
 n\le N/(U+1)<(V+1)^2.
\]
Indeed \((U+1)^3>N^{6/5}>N\). Hence \(w_n\) has at most one contributing
prime, and it cannot occur to the second power in \(n\). When \(w_n>0\),
write uniquely \(n=p\ell\), \(p>V\), with
\(\ell\le N/((U+1)(V+1))<N^{1/5}<V\) for \(N\ge36\).

An elementary reciprocal bound handles the full remaining proper-power part:
\[
 \sum_{\substack{p, a\ge2\\p^a>V}}p^{-a}\ll V^{-1/2}.   \tag{12}
\]
For \(p\le\sqrt V\), the geometric tail beyond \(V\) is at most \(2/V\)
per prime, with at most \(\sqrt V\) primes. For \(p>\sqrt V\), it is at
most \(2/p^2\), whose sum is \(O(V^{-1/2})\). Therefore
\(\sum_{K<n\le2K}h_n\ll KV^{-1/2}L\).

Let \(B_h\) be (5) with \(v_n\) replaced by \(h_n\), and let \(c_t\)
be its Fourier coefficients. Counting the original pairs, still with the
sharp cutoff, gives
\[
 \sum_t|c_t|\ll XV^{-1/2}L,\qquad
 |c_t|\le\tau(t)L\ll_\epsilon N^\epsilon L.
\]
Here the usual divisor bound follows directly from
\(\tau(t)=\prod_{p^a\parallel t}(a+1)\): for all sufficiently large primes
\(a+1\le p^{\epsilon a}\); the finitely many smaller primes contribute a
constant after taking the supremum of \((a+1)p^{-\epsilon a}\).
Thus
\[
 \|B_h\|_2^2\le\max|c_t|\sum_t|c_t|
       \ll_\epsilon XV^{-1/2}N^\epsilon L^2,
\]
and the elementary convolution bound gives
\[
 \boxed{\int_{\mathfrak m_Q}|B_h|^4
 \le\int_{\mathbb T}|B_h|^4
 \ll_\epsilon X^3V^{-3/2}N^\epsilon L^4
 \ll_\epsilon N^{12/5+\epsilon}.}                         \tag{13}
\]
The final \(\epsilon\) absorbs logarithms by starting with a smaller one.
Enlarging to the whole circle here costs at most the same displayed bound,
already below the proposed intermediate block budget \(N^{5/2+\epsilon}\).
It does not place this part in \(N^{2+\epsilon}\) for every \(\epsilon\).

## 4. Integrated paired-label estimate for the prime part

Let \(B_p\) denote the block with \(w_n\) in place of \(v_n\), and put
\[
 T_m(\alpha)=\sum_{K<n\le\min(2K,N/m)}w_ne(mn\alpha).
\]
The subfamily of its fourth expansion with
\((m_1=m_3,m_2=m_4)\) or \((m_1=m_4,m_2=m_3)\) is exactly
\[
 P(\alpha)=2\left(\sum_m\mu(m)^2|T_m|^2\right)^2
             -\sum_m\mu(m)^4|T_m|^4\ge0.                 \tag{14}
\]
The subtraction removes the duplicate all-equal case once. This operation
uses the actual signs: they square in this subfamily. It makes no assertion
about cancellation among the remaining labels.

Since \(P\ge0\), integrate on the circle to bound this part. For two fixed
labels \(m,t\in(M,2M]\), the zero-frequency condition is
\(m(n_1-n_3)=t(n_4-n_2)\). Put \(g=(m,t)\). Its differences must be
\((n_1-n_3,n_4-n_2)=j(t/g,m/g)\), with
\(|j|\ll Kg/M\). There are \(O(K^2)\) pairs for each \(j\). Using
\(0\le w_n\le L\), after the signed subfamily has been selected, gives
\[
 \int_{\mathfrak m_Q}P\le\int_{\mathbb T}P
 \ll K^2L^4\sum_{m,t}\left(1+\frac{K(m,t)}M\right).
\]
The divisor identity \((m,t)=\sum_{d\mid m,t}\phi(d)\) yields
\(\sum_{m,t\in(M,2M]}(m,t)\ll M^2\log(2M)\). For example, bound the
number of multiples of \(d\le2M\) by \(3M/d\), and use \(\phi(d)\le d\).
Consequently
\[
 \boxed{P_{M,K}:=\int_{\mathfrak m_Q}P
 \ll\big(M^2K^2+MK^3\log(2M)\big)L^4
 \ll N^{11/5}L^5.}                                      \tag{15}
\]
The last inequality uses \(MK\le N\), \(M\ge U\asymp N^{2/5}\).
The sharp hyperbolic endpoint only shortens the counted intervals.
The cost of discarding the major-arc subtraction **for this nonnegative
subfamily** is at most (15), below \(N^{5/2}\). The whole prime-block
moment has not been enlarged in this step.

## 5. Attempt the nonpaired estimate at the controlling endpoint

Apply the definitions \(b_t,a_s,A_r\) from (10) to \(B_p\). Let \(P_r\)
be the Fourier coefficients of (14), and put \(R_r=A_r-P_r\). Each \(R_r\)
is the original arithmetic sum with the paired label family removed. Define
\[
\begin{split}
 \mathcal R_{M,K}
 &=\mathcal K_Q(0)R_0
 -2\sum_{q\le Q}\sum_{r=1}^{2N}c_q(r)
       \frac{\sin(2\pi rQ/(qN))}{\pi r}\,R_r,\\
 \int_{\mathfrak m_Q}|B_p|^4&=P_{M,K}+\mathcal R_{M,K}.    \tag{16}
\end{split}
\]
Both \(R_0\) and \(\mathcal R_{M,K}\) can have either sign. No term in
the sine-weighted expression has been bounded separately here.

Here is the actual prime-specific cancellation sum in (16). For each
\(n_i=p_i\ell_i\) with \(p_i>V\) prime and \(w_{n_i}>0\), define
\[
 C_{\boldsymbol n}(r)=
 \sum_{\substack{m_i\in(M,2M],\ m_in_i\le N\\
 m_1n_1+m_2n_2-m_3n_3-m_4n_4=r\\
 (m_1,m_2,m_3,m_4)\text{ not paired}}}
       \mu(m_1)\mu(m_2)\mu(m_3)\mu(m_4).
\]
Then
\[
 R_r=\sum_{K<n_1,\ldots,n_4\le2K}
          \prod_{i=1}^4\log p_i\ C_{\boldsymbol n}(r),    \tag{17}
\]
where the sum includes only those \(n_i\) having the unique prime just
specified. These are actual prime weights, not arbitrary coefficients.

**The concrete attempted estimate** is
\[
       \mathcal R_{U,K}\ll_\epsilon N^{5/2+\epsilon}
       \quad\text{for the critical range (6)}.            \tag{18, unproved}
\]
Together with (13), (15), and
\(|B_p+B_h|^4\le8(|B_p|^4+|B_h|^4)\), it would improve the whole block
from exponent \(13/5\) to \(5/2\). The following direct summation attempt
does not establish (18).

Fix \(\boldsymbol n,r,m_2,m_3\) and solve the constraint for \(m_4\).
With \(g=(n_1,n_4)\), admissible \(m_1\) occupy one residue class modulo
\(d=n_4/g\), if the congruence is solvable. Parametrize
\[
        m_1=a+dt,\qquad m_4=b+(n_1/g)t.                 \tag{19}
\]
The remaining signed inner sum is a product of the two fixed Möbius values
times
\(\sum_{t\in\mathcal J}\mu(a+dt)\mu(b+(n_1/g)t)\),
with the original interval, product, and nonpaired restrictions. Its length
is at most \(1+M/d\).

Now use the prime formula instead of a generic coefficient estimate.
If \(p_1\ne p_4\), then \(\ell_i<V<p_j\) implies
\[
 (n_1,n_4)=(\ell_1,\ell_4),\qquad d\ge p_4>V=U.
\]
For \(M=U\), the interval \((U,2U]\) has length \(U<d\), so (19)
contains **at most one integer**. There is no cancellation in this last
variable to estimate. Its contribution is 0 or one product of actual
Möbius values. Taking its absolute value returns 0 or 1, with no power
saving. Even a theorem about cancellation on long progressions could not
improve this step. When \(p_1=p_4\), a longer interval can remain, but the
two affine Möbius factors are still present; no unproved estimate for them
is invoked. The other block ranges are also not resolved by this argument.

The unsupported prime-specific estimate is therefore (18) for the aggregate
in (16)--(17), **after** summing these constrained fragments with the prime
weights and the rational-arc kernel. No distribution theorem supplied here
bounds that aggregate. This is the point at which this arithmetic attempt
fails, not a generic-polynomial obstruction.

## 6. Quantify the two possible absolute-value completions

They provide bounds, but both miss (18). For \(B_p=\sum b_te(t\alpha)\),
the actual coefficients obey \(\sum|b_t|\ll XL\) and
\(\sum|b_t|^2\ll XL^5\). For the latter, use \(|b_t|\le\tau(t)L\),
support \(t\le4X\), and the elementary bounds
\(\tau(t)^2\le d_4(t)\), \(\sum_{t\le Y}d_4(t)\le Y(1+\log Y)^3\).
Thus the full-circle completion, using Young's convolution inequality,
only gives
\[
       \int_{\mathfrak m_Q}|B_p|^4\le A_0
               \le\|b\|_1^2\|b\|_2^2\ll X^3L^7.        \tag{20}
\]
For \(X\asymp N\), exponent 3 loses \(N^{2/5}\), ignoring logarithms,
against the existing block benchmark. No prime cancellation is claimed in
this completion.

Replacing the kernel term by term is worse. Parseval for
\({\bf1}_{\mathfrak m_Q}\) gives
\[
 \sum_{|r|\le2N}|\mathcal K_Q(r)|
 \le\sqrt{4N+1}\sqrt{\mathcal K_Q(0)}\ll\sqrt N.
\]
Also \(|A_r|\le A_0\) by Cauchy, and \(|P_r|\le P_0\) since \(P\ge0\).
Together with the whole-circle bound in the proof of (15) and with (20),
the termwise absolute completion yields only
\[
       |\mathcal R_{M,K}|\ll\sqrt N\,X^3L^7.             \tag{21}
\]
This bound introduces a factor \(\sqrt N\) beyond (20), and reaches
\(N^{7/2}L^7\) in (6). This is the quantitative bound produced by the
absolute-value move, not a claim that the actual cancellation loss has
that size. We retain (16) in the useful budget instead of making that move.

For comparison, the checked sharp bilinear estimate gives
\[
 \sup_{\mathfrak m_Q}|B_p|^2\ll X(M+K+\sqrt N)L^3,
\quad
 \int_{\mathfrak m_Q}|B_p|^4
        \ll X^2(M+K+\sqrt N)L^8.                         \tag{22}
\]
The same estimate applies to (5). One obtains it by Cauchy and the
geometric sum in the remaining interval, including
\(m\le\min(N/n,N/n')\), followed by the denominator bound stated below.
It is \(N^{13/5}L^8\) in (6), and \(N^{5/2}L^8\) when
\(M,K\asymp\sqrt N\). It is the surviving benchmark, not an integrated
improvement from this attempt.

## 7. Recombination and the original total error

Let \(I_f=\int_{\mathfrak m_Q}|f|^4\). The other terms in (2) satisfy
\[
 I_{S_0}\ll N^{6/5}L,\qquad
 I_{T_{\log}}\ll N^2L^9,\qquad
 I_{T_{\rm prod}}\ll N^{13/5}L^9.                         \tag{23}
\]
The pointwise bounds behind the last two are
\((N/q+U+q)L^2\) and \((N/q+UV+q)L^2\), respectively, with
\(q\asymp\sqrt N\) on the minor set. Their Fourier coefficients are
bounded by \(\tfrac12\tau(t)\log t\), hence their squared global
\(L^2\) norms are \(O(NL^5)\). The short term uses
\(\psi(V)\ll V\) and \(\sum_{n\le V}\Lambda(n)^2\ll VL\).
The long Type I term is still above the desired exponent even if (18)
were proved. Keeping \(T_{\log}-T_{\rm prod}\) combined is an exact
alternative; no better estimate for that combination is established here.

Hölder gives the explicit costs
\[
 I_Q\le64(I_{S_0}+I_{T_{\log}}+I_{T_{\rm prod}}+I_{T_{\rm II}}),
 \quad I_{T_{\rm II}}\le J^3\sum_{M,K}I_{B_{M,K}},
 \quad I_{B_{M,K}}\le8(P_{M,K}+\mathcal R_{M,K}+I_{B_h}).  \tag{24}
\]
Thus no cross-block or cross-Type cancellation is silently used. If a
future estimate relies on it, the first or second inequality in (24) must
be replaced, not cited as preserving that cancellation.

For an upper budget write \(\mathcal R^+=\max(0,\mathcal R)\), and let
\(R_{\rm crit}^+\), \(R_{\rm other}^+\) be its sums over (6) and over
every remaining nonempty block, respectively. The sine-weighted
cancellation inside each \(\mathcal R\) is still retained. Dropping a
negative \(\mathcal R\) costs at most \(P_{M,K}\), since the moment in
(16) is nonnegative. Using (13), (15), (23), (24), and the original
reduction proves the component budget
\[
 \boxed{E(N)\le4M_Q+256I_{T_{\rm prod}}
       +2048J^3(R_{\rm crit}^++R_{\rm other}^+)
       +O_\epsilon(N^{12/5+\epsilon}).}                  \tag{25}
\]
The final controlled term includes all \(h_n\) blocks, the paired-label
parts, the short and logarithmic Type I pieces, and the geometric
\(O(N^2L^3)\) remainder. Powers of \(J=O(L^2)\) are absorbed in
\(\epsilon\). Every unresolved term is displayed.

Inserting (22), (23) into this split budget gives at best
\(4M_Q+O(N^{13/5}L^{16})+O(N^2L^3)\). The unsplit estimate from
`UPPER_BOUND.md` is stronger in logarithms and remains
\[
       E(N)\le4M_Q+O(N^{13/5}L^6)+O(N^2L^3).             \tag{26}
\]
Neither is an improved bound for total \(E\). The existing unconditional
\(E(N)\ll_C N^3/L^C\) is unchanged. No RH, GRH, stochastic model, or
unproved prime/Möbius distribution estimate entered the proved bounds.

## 8. Source and bounded checks

The primary input checked on 2026-09-09 is Montgomery and Vaughan,
*Multiplicative Number Theory II: Primes and Sieves*,
[author-hosted manuscript](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf).
Equations (17.3)--(17.7), printed pp.55--56, give the identity, with their
\(U,V\) names reversed relative to ours. Equations (17.10), (17.12)--(17.14),
pp.57--59, keep the sharp product cutoff in bilinear sums. Equation (17.32)
and its following estimates, p.66, give the denominator and Type I bounds;
Theorem 17.1, p.65, gives the unchanged full-sum benchmark. In (22), apply
(17.32) with length parameter \(MK\), summation length \(K\), and use
\(\min(M,\|h\alpha\|^{-1})\le\min(MK/h,\|h\alpha\|^{-1})\) for
\(h\le K\). No additional distribution theorem is invoked.

The new self-contained estimates and kernel derivation are checked by
`artifacts/arithmetic_fourth/check.py`, with saved `result.json`. This is
one bounded process, with maximum identity cutoff 625 and one Fourier
block at \(N=256\). It checks the truncated identity using exact integer
coefficients of \(\log p\), checks the prime/proper-power split and its
unique-prime claim, compares the kernel with interval antiderivatives at
50 decimal places, and compares the signed moment expansion with an
independent direct scalar quadrature on the exact minor intervals. It
reports \(r=0\), the signed off-diagonal, paired and nonpaired integrals,
and the absolute-kernel completion separately. Quadrature values are
finite diagnostics, not enclosures or asymptotic evidence. A 60-second
alarm bounds the diagnostic computation. No scientific CI experiment is used.

The one recorded Fourier block is \((N,U,V,M,K,Q)=(256,9,9,9,18,5)\).
Rounded values below are finite diagnostics only:

| Quantity for the actual large-prime block | Value |
| --- | ---: |
| Full-circle fourth moment | 5627.584917 |
| Minor-kernel r=0 contribution | 4865.516126 |
| Signed off-diagonal contribution | -589.722282 |
| Minor fourth moment | 4275.793844 |
| Termwise absolute-kernel completion | 6713.508573 |
| Paired-label minor contribution | 4934.774712 |
| Signed nonpaired minor contribution | -658.980868 |

The 917 coefficient identities passed with exact integer log-prime vectors.
All 513 tested kernel values agreed with the independent interval formula
to better than \(2\cdot10^{-50}\) in 50-decimal arithmetic. The independent
scalar quadrature agreed with both block moments at relative tolerance
\(10^{-8}\). These tests do not estimate any asymptotic cancellation rate.
