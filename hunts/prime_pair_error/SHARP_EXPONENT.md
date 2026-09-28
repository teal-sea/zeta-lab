# The corrected energy bound at exponent constant \(2c_0\)

**Frontier correction, 2026-09-12.** The negative conclusion of section 1.2
is withdrawn. Its AP-variance calculation omitted the centered principal
character, undercounted induced characters, and used a zero-free upper
envelope as a lower bound. `FAREY_BASELINE_REPAIR.md` supplies the corrected
identities and an independent bounded-overlap proof of the available
\(N^3(\log N)^9/Q\) residual fourth-moment bound. That bound is not an
optimality statement or a general route closure. Sections 2 and 3, which
derive (S\('''\)), do not use the faulty AP-variance estimate.

The upper bound (S\('''\)) remains the inherited campaign bound. A matching
lower bound is conditional on a possible real zero and on all the error
separation hypotheses in `MAJOR_ARC_EXPLICIT.md` section 5. It is not an
unconditional determination of the true exponent or evidence that such a
zero exists. `SIGNED_MEAN_RENEWAL.md` records the smaller scalar target
equivalent to RH and a new attempted arithmetic estimate for it.

2026-09-12. Base: `MAJOR_ARC_EXPLICIT.md` (commit 7c6f264: its sections 2 to
5, its (H), its Proposition and corollary), `ARC_SPLIT_BUDGET.md` (arcs,
(1), (3), (11), (12)), `UPPER_BOUND.md` (7), (20), `ENDPOINT_SHARP.md`
sections 4 and 5. Assignment: attack the minor-arc fourth moment at the
actual cutoff \(R=\exp(\sigma\sqrt\ell)\), target
\(\int_{\mathfrak m}|F|^4\ll N^3\ell^{O(1)}R^{-2+\varepsilon}\), revisiting the
Farey large sieve and Gallagher's lemma at this cutoff; first decide whether
the smaller cutoff removes the old obstruction; if not, record it exactly and
choose the next mechanism.

**Result, stated first.** Two statements, one negative and one positive.

*Historical negative argument, withdrawn by the correction above.* The smaller cutoff moves the obstruction but does not remove it.
At the rank-3 cutoff the difficulty was the modulus range \(q\le\sqrt N/L\);
at cutoff \(R\) only the moduli \(R<q\le R^2\ell\), i.e. \(N^{o(1)}\) of them,
need anything beyond Vaughan (section 1.1). But the Farey dissection at level
\(\sqrt N\) that the large sieve needs forces arcs of width \(1/(q\sqrt N)\),
which by Gallagher's lemma is the variance of \(\Lambda\) in progressions
mod \(q\) over intervals of length \(q\sqrt N/2\), and the large sieve gives
exactly Vaughan's \(N^3\ell^2/Q\) for that variance, with the missing factor
\(Q^{1-\varepsilon}\) being the large sieve's slack \(h/Q^2\) at interval
length \(h=Q\sqrt N\gg Q^2\) (section 1.2). Closing it needs the variance of
primes in intervals of length \(\asymp\sqrt N\) below its trivial order by a
power of \(Q=e^{\sigma\sqrt\ell}\), and at height \(N/h\asymp\sqrt N\) the
zero-free region yields \(N^{2(\beta-1)}\ge e^{-4c}\), a constant: no such
saving is known even for \(q=1\). A different dissection (section 1.3) proves
the literal target with the exceptional spikes made explicit, but it is the
arc split at cutoff \(R^2\ell\) in disguise and does not move the exponent.

*Positive.* The reason the factor \(2\) between `MAJOR_ARC_EXPLICIT.md`'s
exponent \(c_0\) and its ceiling \(2c_0\) was attributed to the minor arcs
is that the major-arc term carrying the Page-allowed zero was bounded by a
supremum times Parseval over the whole circle. Integrating it over each arc
instead, using that both \(K_N(\theta)\) and \(I_{\tilde\beta}(\theta)\)
decay like \(1/|\theta|\) beyond \(1/N\), removes the factor \(R\) from that
term (section 2). The balance then puts \(\sigma=2c_0\), and under
\[
 c_0\le\min\big(1/12,\ \sqrt c/4,\ \sqrt b/4,\ c_P\big),
\tag{H$''$}
\]
for every fixed \(c''<2c_0\),
\[
 \boxed{\ E_{\rm corr}^{(Z)}(N)\ \ll\ N^3\exp\!\big(-c''\sqrt{\log N}\big).\ }
\tag{S$'''$}
\]
With the conditional lower bound of `MAJOR_ARC_EXPLICIT.md` section 5, which
gives \(E_{\rm corr}^{(Z)}\gg N^3e^{-2\kappa\sqrt\ell}/\tilde q^{\,2}\) whenever a
real zero sits at \(1-\kappa/\sqrt\ell\) just below the target's threshold,
**the exponent constant of this target is \(2c_0\)**: unconditionally from
above, and from below in the presence of the zero that Page allows. What is
left between the two bounds is \(\ell^{O(1)}\tilde q^{\,2}\). The arc balance
that every budget since `ENDPOINT_BOUND.md` was built on is no longer the
binding constraint; the minor arcs only need \(R\ge e^{2c_0\sqrt\ell}\).

Grade: derived, one route, finite checks in section 5, independently read.
Nothing about the zeros of \(\zeta\) beyond the classical inputs; the lower
half of the two-sided statement is conditional on a zero that may not exist.

**Historical independent check, 2026-09-12** (attempt `a-0082`,
`SHARP_EXPONENT_REVIEW.md`). All five items confirmed: the dyadic reduction,
the obstruction of section 1.2 including the negative claim that no known
input supplies the missing power at interval length \(\asymp\sqrt N\), the
dissection of section 1.3, the mechanism of section 2 with the per-arc
integral and its flatness in \(R\) recomputed by a fresh script, and the
correction 2.1 (the check agrees it was a miss of `a-0080`). One defect,
non-binding: the term \(R^2e^{-(2c/\sigma)\sqrt\ell}\) in (7), inherited from
`MAJOR_ARC_EXPLICIT.md` (6), should be \(Re^{-(2c/\sigma)\sqrt\ell}\); it is
dominated by its neighbour and induces a condition weaker than one already
in (H\(''\)). Corrected in both documents, marked at (7). The present
frontier correction supersedes that review's endorsement of section 1.2.

## 1. The assigned attack, and where the obstruction sits at cutoff \(R\)

Notation as in `ARC_SPLIT_BUDGET.md` section 2: \(R=\lfloor e^{\sigma\sqrt\ell}\rfloor\),
\(\mathfrak m\) the complement of the arcs \(|\alpha-a/r|\le R/(rN)\), \(r\le R\).
The minor-arc term of the budget is \(I_R=\int_{\mathfrak m}|F|^4\), bounded by
`UPPER_BOUND.md` (20) as \((N^3/R+N^{13/5})L^6\) through \(\sup_{\mathfrak m}|F|^2\int|F|^2\).

### 1.1 What the smaller cutoff does remove

Cover \(\mathfrak m\) by the Farey arcs \(I'_{q,a}=\{|\alpha-a/q|\le1/(q\sqrt N)\}\),
\(q\le\sqrt N\) (Dirichlet with parameter \(\sqrt N\)); those with \(q\le R\)
are inside \(\mathfrak M\) up to their outer parts, which are minor and are
kept. On \(I'_{q,a}\), \(F=P_{q,a}+R_{q,a}\) with \(P_{q,a}=(\mu(q)/\phi(q))K_N(\alpha-a/q)\).
For a dyadic block \(q\sim Q\), Hölder gives
\[
 Z'_Q:=\sum_{q\sim Q}\sum_a^*\int_{I'_{q,a}}|F|^4
 \le\sup_{q\sim Q}\sup_{I'_{q,a}}|F|^2\cdot\sum_{q\sim Q}\sum_a^*\int_{I'_{q,a}}|F|^2
 \ll\frac{N^2\ell^8}{Q}\cdot N\ell=\frac{N^3\ell^9}Q,
\]
by Vaughan for \(Q\le N^{2/5}\) (\(|\alpha-a/q|\le1/q^2\) on \(I'_{q,a}\)
for \(q\le\sqrt N\)) and bounded overlap of the arcs within the block,
not disjointness. For \(Q>N^{2/5}\), retain Vaughan's other terms to get
\(Z'_Q\ll (N^3/Q+N^{13/5}+N^2Q)\ell^9\). The additional terms are
\(O(N^{13/5}\ell^9)\) for \(Q\le\sqrt N\), below \(N^3/R^2\) eventually.
For \(R^2\ell^{9}\le Q\le N^{2/5}\) the displayed bound is already
\(\le N^3/R^2\). Among the blocks with \(q>R\), attention therefore reduces
to \(R<Q\le R^2\ell^9\):
moduli of size \(N^{o(1)}\), where the rank-3 programme's obstruction (the
range up to \(\sqrt N/L\), `RANK3_QUARTIC_LITERATURE.md`) does not apply.
This comparison does not bound the outer parts of the Farey arcs with
\(q\le R\). Those were mentioned above but still need separate treatment;
this paragraph alone is not a reduction of the entire minor-arc integral.

### 1.2 Farey large sieve and Gallagher at this cutoff: what they give

**Withdrawn derivation retained as history.** Equations (1)-(4) below are
not current proof inputs. The clipped endpoints, reduced numerators,
principal character and imprimitive multiplicities are handled explicitly
in `FAREY_BASELINE_REPAIR.md`, equations (F)-(O). Its equation (E) gives
the required second-moment baseline directly by bounded overlap. The
concluding general closure and zero-density assertion below do not follow.

Fix \(Q\in(R,R^2\ell^9]\). Write \(\alpha=a/q+\theta\), \(|\theta|\le1/(q\sqrt N)\),
and
\[
 R_{q,a}(a/q+\theta)=\sum_{n\le N}c_n(q,a)e(n\theta),\qquad
 c_n(q,a)=\Lambda(n)e(an/q)-\frac{\mu(q)}{\phi(q)} .
\]
Gallagher's lemma (\(\int_{|\theta|\le\Theta}|\sum c_ne(n\theta)|^2d\theta\ll\Theta^2\int|\sum_{x<n\le x+1/(2\Theta)}c_n|^2dx\))
with \(\Theta=1/(q\sqrt N)\), \(h_q:=q\sqrt N/2\), and the exact identity
\(\sum_{x<n\le x+h}c_n(q,a)=\sum_{b\bmod q}e(ab/q)\Delta_b(x,h)\),
\(\Delta_b(x,h):=\psi(x+h;q,b)-\psi(x;q,b)-1_{(b,q)=1}h/\phi(q)\) (using
\(\sum_b^*e(ab/q)=\mu(q)\)), followed by orthogonality over \(a\), give
\[
 \sum_{a\bmod q}\int_{I'_{q,a}}|R_{q,a}|^2\ll\frac1{q^2N}\cdot q\,V_q(h_q),\qquad
 V_q(h):=\int_0^N\sum_{b\bmod q}|\Delta_b(x,h)|^2dx .
\tag{1}
\]
So \(\sum_{q\sim Q}\sum_a\int_{I'}|R|^2\ll(QN)^{-1}\sum_{q\sim Q}V_q(h_q)\), and
with \(\sup|R_{q,a}|^2\ll N^2\ell^8/Q\) (Vaughan plus \(|P|\le N/\phi(q)\)),
\[
 Z'^{\rm res}_Q:=\sum_{q\sim Q}\sum_a\int_{I'}|R_{q,a}|^4\ll\frac{N\ell^8}{Q^2}\sum_{q\sim Q}V_q(h_q).
\tag{2}
\]
The target \(Z'^{\rm res}_Q\ll N^3Q^{-2+\varepsilon}\) is therefore
\[
 \sum_{q\sim Q}V_q(h_q)\ll N^2Q^{\varepsilon},\qquad h_q\asymp Q\sqrt N .
\tag{3}
\]
Three inputs, against (3):

- *Trivial.* \(\sum_b|\Delta_b|^2\le(\sum_b|\Delta_b|)^2\ll(h\ell)^2\), so
  \(\sum_{q\sim Q}V_q\ll N\cdot Q\cdot h^2\ell^2\asymp N^2Q^3\ell^2\). Off by \(Q^3\).
- *Koukoulopoulos, Theorem 1.1* (first moment, `RANK3_Z_COMPONENT.md`):
  \(\sum_b|\Delta_b|^2\le E(x,h;q)\sum_b|\Delta_b|\ll h\,E(x,h;q)\), and
  \(\int\sum_{q\le2Q}E(x,h;q)dx\ll hN(\log N)^{-A}\) for \(Q^2\le h/N^{1/3+\varepsilon}\),
  which holds here. So \(\sum_{q\sim Q}V_q\ll h^2N(\log N)^{-A}\asymp N^2Q^2(\log N)^{-A}\).
  Off by \(Q^2\): the theorem's saving is logarithmic and the factor \(h\) in
  \(\sum_b|\Delta_b|\ll h\) is what a first moment cannot recover.
- *The large sieve for characters* (the genuine second-moment tool). By
  orthogonality \(\sum_b^*|\Delta_b(x,h)|^2=\phi(q)^{-1}\sum_{\chi\ne\chi_0}|\psi(x+h,\chi)-\psi(x,\chi)|^2\),
  reduction to primitive characters costs a factor \(\ll\log Q\), and the
  multiplicative large sieve gives
  \(\sum_{q\le2Q}\frac q{\phi(q)}\sum_\chi^*|\sum_{x<n\le x+h}\Lambda(n)\chi(n)|^2\le(h+4Q^2)\sum_{x<n\le x+h}\Lambda(n)^2\ll(h+Q^2)h\ell\).
  Hence \(\sum_{q\sim Q}\sum_b|\Delta_b(x,h)|^2\ll\ell^2(h+Q^2)h/Q\), and
  integrating over \(x\le N\),
  \[
   \sum_{q\sim Q}V_q(h_q)\ll\frac{N\ell^2h_q^2}Q\asymp N^2Q\ell^2 .
  \tag{4}
  \]
  Into (2): \(Z'^{\rm res}_Q\ll N^3\ell^{10}/Q\). **Exactly Vaughan's order.**
  Off (3) by \(Q^{1-\varepsilon}\), and the missing factor is visible: the large
  sieve is sharp when the number of characters, \(\asymp Q^2\), matches the
  length \(h\) of the sequence; here \(h=Q\sqrt N\gg Q^2\), and the slack
  \(h/Q^2\asymp\sqrt N/Q\) is what (4) carries over the random-model size
  \(\sum_{q\sim Q}V_q\asymp N\cdot Q\cdot(h\ell)\asymp N^{3/2}Q^2\ell\), which
  would satisfy (3) with room.

**The obstruction, exactly.** (3) asks for the variance of \(\Lambda\) in
progressions to moduli \(q\sim Q\) over intervals of length \(h\asymp Q\sqrt N\)
to be within \(Q^{\varepsilon}\) of its random size, i.e. a saving of
\(Q^{1-\varepsilon}\) over the large sieve, equivalently \(Q^{3-\varepsilon}\)
over trivial. Through the explicit formula that variance is governed by the
zeros of the \(L(s,\chi)\), \(\chi\bmod q\), at heights up to
\(N/h\asymp\sqrt N/Q\), where the zero-free region (ZF) gives
\(\beta\le1-c/\log(q\sqrt N/Q)\approx1-2c/\ell\) and so
\(N^{2(\beta-1)}\ge e^{-4c}\): a constant, not a power of \(Q\). Even for
\(q=1\), \(\int_N^{2N}(\psi(x+h)-\psi(x)-h)^2dx\) at \(h\asymp\sqrt N\) is not
known below its trivial order \(h^2N\) by more than a subpolynomial factor
(the Vinogradov-Korobov region gives \(\exp(-c\,\ell^{1/3}(\log\ell)^{-1/3})\)
at that height, and density estimates add nothing near \(\sigma=1\)). The
smaller cutoff changed the modulus range from \(\sqrt N/L\) to \(R^2\ell^9\),
and the modulus range was never the binding side of this estimate: the
interval length \(\asymp\sqrt N\), set by the Farey level, is. So the assigned
route is closed at this cutoff by the same input that closes it at every
cutoff, and the answer to the first question of the assignment is no.

### 1.3 A different dissection proves the literal target, and why that does not help

Dissect instead with parameter \(N/Q_2\), \(Q_2=R^2\ell\): arcs
\(|\alpha-a/q|\le Q_2/(qN)\) for \(q\le Q_2\), and Vaughan on the rest, which
gives \(\ll N^3\ell^{O(1)}/Q_2\le N^3\ell^{O(1)}/R^2\). On the arcs with
\(R<q\le Q_2\) the heights are \(N|\theta|\le Q_2/q\le R\ell\), so
`MAJOR_ARC_EXPLICIT.md` section 2 applies with \(R\) replaced by \(Q_2\): by
its (3) and (4),
\(|F(a/q+\theta)-P_{q,a}|\le\sqrt q\,N\Upsilon_{Q_2}(q)+(\text{exceptional real zeros of characters mod }q)\),
so \(\int|F|^4\) over these arcs is
\(\sum_{q}\sum_a\int|P_{q,a}|^4+O(\cdot)\ll N^3\ell^c/R^2+N^3\ell^{O(1)}Q_2^{4}\Upsilon^4+\mathcal E\),
with \(\mathcal E\) the spikes of the exceptional zeros. Hence
\[
 \int_{\mathfrak m}|F|^4\ \ll\ N^3\ell^{O(1)}R^{-2}+\mathcal E,\qquad
 \mathcal E\ll\sum_{\tilde\beta}\frac{N^{4\tilde\beta-1}}{\tilde q}\Big(\frac{\tilde q}{\phi(\tilde q)}\Big)^{O(1)} ,
\tag{5}
\]
the sum over the at most two real zeros (the TT-exceptional \(\beta_e\) and the
Page-allowed \(\tilde\beta\)) of real characters of conductor in \((R,Q_2]\).
Two remarks. First, \(\mathcal E\) is not removable from \(\int_{\mathfrak m}|F|^4\):
at \(a/q_e\) with \(R<q_e\le Q_2\), \(|F|^2\) has a spike of height
\(\asymp N^{2\beta_e}/q_e\), so the assigned target is false as literally
stated whenever such a zero exists with \(\beta_e\) close to \(1\) and
\(q_e<R^2\); it is true for the corrected integrand, where \(\widehat C_N\)
subtracts that spike. Second, and decisive: (5) is the arc split of
`ARC_SPLIT_BUDGET.md` at cutoff \(Q_2\) written in the variables of cutoff
\(R\). Its budget balances the same two terms as before at the larger cutoff,
so proving (5) leaves the exponent where it was. The literal target and the
exponent are not the same question, and the operator's reason for the
target, the factor \(2\) between \(c_0\) and \(2c_0\), lives elsewhere.

## 2. The mechanism: integrate the Page term over the arc

`MAJOR_ARC_EXPLICIT.md` (5) bounds \(|W|\) on \(I_{r,a}\) by a supremum, and
its section 4 multiplies \(\sup_{\mathfrak M}|W|^2\) by
\(\int_{\mathbb T}(|F|+|H|)^2\ll N\ell\). For the one term that binds, the
Page-allowed real zero \(\tilde\beta\) of \(\tilde\chi\bmod\tilde q\),
\(\tilde q\mid r\), that costs a factor \(R\) which the term does not have.
Split, on \(I_{r,a}\) with \(\tilde q\mid r\),
\[
 W=W_P+W_0,\qquad
 W_P(a/r+\theta)=-\frac{\overline{\tilde\chi}(a)\tau(\tilde\chi_r)}{\phi(r)}I_{\tilde\beta}(\theta),\qquad
 |\tau(\tilde\chi_r)|\le\sqrt{\tilde q}\le\sqrt r,
\]
\(\tilde\chi_r\) the character mod \(r\) induced by \(\tilde\chi\), and \(W_0\)
everything else, with \(\sup_{I_{r,a}}|W_0|\ll\sqrt r\,N\Upsilon(r)+R^{3/2}E_{\rm md}=:N\eta(r)\)
from that document's (3), (4) (with the term of section 2.1 below added to
\(\Upsilon\)). Two facts about the two functions of \(\theta\):
\[
 |K_N(\theta)|\le\min\Big(N,\frac1{2\|\theta\|}\Big),\qquad
 |I_{\tilde\beta}(\theta)|\le\min\Big(2N^{\tilde\beta},\ C\frac{N^{\tilde\beta}}{N|\theta|}\Big)\quad(|\theta|\le R/N),
\tag{6}
\]
the second from splitting \(\int_1^N\) at \(t_0=1/|\theta|\): the part below
\(t_0\) is \(\le t_0^{\tilde\beta}/\tilde\beta\) and the part above, by parts,
is \(\ll t_0^{\tilde\beta-1}/|\theta|\), both \(\ll|\theta|^{-\tilde\beta}=N^{\tilde\beta}(N|\theta|)^{-\tilde\beta}\),
and \((N|\theta|)^{1-\tilde\beta}\le R^{\kappa/\sqrt\ell}=e^{\kappa\sigma}\) is
the constant \(C\) (section 5 measures it). Now
\((|F|^2-|H|^2)^2\le8|H|^2|W|^2+2|W|^4\le16|H|^2(|W_P|^2+|W_0|^2)+16(|W_P|^4+|W_0|^4)\),
and with \(|H(a/r+\theta)|\le|K_N(\theta)|/\phi(r)+R^{3/2}E_{\rm md}\):

- \(\int_{I_{r,a}}|K_N|^2|W_P|^2/\phi(r)^2\le\frac{r}{\phi(r)^4}\int\min(N,\tfrac1{2|\theta|})^2\min(2N^{\tilde\beta},\tfrac{CN^{\tilde\beta}}{N|\theta|})^2d\theta
  \ll\frac{r}{\phi(r)^4}N^{2\tilde\beta+1}\), the integral being \(\ll N\)
  (\(\int_{|\theta|<1/N}N^2\cdot4N^{2\tilde\beta}+\int_{1/N}^\infty\frac{C^2N^{2\tilde\beta}}{4N^2\theta^4}\ll N^{2\tilde\beta+1}\)).
  Summing over the \(\phi(r)\) values of \(a\) and over \(r\le R\) with \(\tilde q\mid r\):
  \(\ll N^{2\tilde\beta+1}\sum_{m\le R/\tilde q}\frac{\tilde qm}{\phi(\tilde qm)^3}\ll N^{2\tilde\beta+1}\Big(\frac{\tilde q}{\phi(\tilde q)}\Big)^3\tilde q^{-2}\ll N^3\ell^3e^{-2c_0\sqrt\ell}\tilde q^{-2}\).
  **No factor of \(R\).** Section 5 item (2) measures this integral flat in \(R\).
- \(\int_{I_{r,a}}(R^{3/2}E_{\rm md})^2|W_P|^2\ll R^3E_{\rm md}^2\frac r{\phi(r)^2}N^{2\tilde\beta-1}\);
  over \(a\) and \(r\): \(\ll R^4E_{\rm md}^2N^{2\tilde\beta-1}\ell\ll N^3\ell\,R^4e^{-2\sqrt\ell/3}e^{-2c_0\sqrt\ell}\).
- \(\int_{I_{r,a}}|W_P|^4\ll\frac{r^2}{\phi(r)^4}N^{4\tilde\beta-1}\); over \(a\) and
  \(r\le R\): \(\ll N^{4\tilde\beta-1}\sum_{r\le R}r^2/\phi(r)^3\ll N^{4\tilde\beta-1}\ell^{O(1)}\ll N^3\ell^{O(1)}e^{-4c_0\sqrt\ell}\).
- The \(W_0\) terms as before, by supremum times Parseval:
  \(\int_{\mathfrak M}|H|^2|W_0|^2+\int_{\mathfrak M}|W_0|^4\ll N^2\max_r\eta(r)^2\cdot N\ell\).

### 2.1 One term added to \(\Upsilon\)

`MAJOR_ARC_EXPLICIT.md` section 3, third bullet, said that a real zero of a
real character which is not the Page zero lies outside (ZF)'s region. That is
not right in general: (ZF) allows one real zero per real \(\chi\) in
\(\sigma\ge1-c/\log(r(|t|+2))\), Page at \((R,R^3)\) allows one zero in
\(\sigma>1-b/\log R^4\) among all of them, and when \(4c>b\) a real \(\chi\bmod r\)
may have a real zero in \((1-c/\log 2r,\ 1-b/(4\sigma\sqrt\ell)]\) that is
(ZF)-exceptional and not Page-exceptional. There is at most one per real
character, it contributes \(|I_\beta(\theta)|\le2N^\beta\le2Ne^{-(b/(4\sigma))\sqrt\ell}\)
to \(F_\chi\), and after the Gauss-sum factor it adds
\(\sqrt r\,Ne^{-(b/(4\sigma))\sqrt\ell}\) to (5) there, i.e. the term
\(e^{-(b/(4\sigma))\sqrt\ell}\) to \(\Upsilon(r)\). In that document's budget
this is \(Re^{-(b/(2\sigma))\sqrt\ell}\), harmless under its (H) (at
\(\sigma=c_0\): \(b/(2c_0)-c_0\ge c_0\) since \(c_0^2\le b/4\)); the bullet is
corrected there with a pointer here. The check `a-0080` confirmed that bullet
and did not see this; it is recorded as a miss of that check.

## 3. The budget

Collecting section 2 with `ARC_SPLIT_BUDGET.md` (4), (11) and
`MAJOR_ARC_EXPLICIT.md` (3), (4), with \(R=\lfloor e^{\sigma\sqrt\ell}\rfloor\):
\[
 E_{\rm corr}^{(Z)}(N)\ll N^3\ell^{O(1)}\Big[e^{-2c_0\sqrt\ell}+R^{-1}
 +Re^{-(2c/\sigma)\sqrt\ell(1+o(1))}+Re^{-(c/(2\sigma))\sqrt\ell(1+o(1))}+Re^{-(b/(2\sigma))\sqrt\ell}
 +R^{-3}+R^3e^{-2\sqrt\ell/3}+R^4e^{-(2/3+2c_0)\sqrt\ell}\Big]
 +N^3e^{-2c_m\sqrt\ell}+N^{13/5}\ell^6+N^2\ell^2 .
\tag{7}
\]
(**Corrected 2026-09-12**, defect found by the check `a-0082`: the third
term was printed as \(R^2e^{-(2c/\sigma)\sqrt\ell(1+o(1))}\), inherited from
`MAJOR_ARC_EXPLICIT.md` (6). Squaring \(\sqrt r\cdot\sqrt{R/r}=\sqrt R\) gives
\(R\), not \(R^2\); the term is in any case dominated by the one after it.
Neither (H\(''\)) nor the conclusion changes.) The first term is the
Page-allowed zero, now without \(R\). Take \(\sigma=2c_0\). The exponents of
the remaining terms are then
\(2c_0,\ c/c_0-2c_0,\ c/(4c_0)-2c_0,\ b/(4c_0)-2c_0,\ 6c_0,\ 2/3-6c_0,\ 2/3-6c_0\),
each at least \(2c_0\) when \(c_0^2\le c/4\), \(c_0^2\le c/16\), \(c_0^2\le b/16\),
\(c_0\le1/12\); with \(2c_m=1/2-o(1)>2c_0\) and the Page-matching condition
\(c_0\le b/(4\sigma)=b/(8c_0)\), i.e. \(c_0^2\le b/8\), and TT's uniqueness
\(c_0\le c_P\), this is (H\(''\)). Therefore
\(E_{\rm corr}^{(Z)}(N)\ll N^3\ell^{O(1)}\exp(-2c_0\sqrt\ell)\), which is (S\('''\)).

**Two-sided.** `MAJOR_ARC_EXPLICIT.md` Proposition: if a primitive real
\(\tilde\chi\) of odd conductor \(\tilde q\le e^{\varepsilon\sqrt\ell}\) has a real
zero \(1-\kappa/\sqrt\ell\) with \(c_0<\kappa<\min(\sqrt c,\sqrt b)-3\varepsilon\),
then \(E_{\rm corr}^{(Z)}\ge c_1N^3e^{-2\kappa\sqrt\ell}/\tilde q^{\,2}\) (even
\(\tilde\chi\); odd with an extra \(\kappa^2/\ell\)). As \(\kappa\downarrow c_0\)
this approaches \(N^3e^{-2c_0\sqrt\ell}/\tilde q^{\,2}\), and (S\('''\)) is
\(N^3\ell^{O(1)}e^{-2c_0\sqrt\ell}\). The exponent constant of the fixed target
is \(2c_0\), with \(\ell^{O(1)}\tilde q^{\,2}\) between the bounds, and the only
way past it is the effective zero-free interval for real characters that the
corollary there names.

**Against the previous budgets.** Every budget from `ENDPOINT_BOUND.md` (18)
to `MAJOR_ARC_EXPLICIT.md` (6) was a balance of a major-arc term
\(N^3R^ke^{-2\gamma\sqrt\ell}\) against a minor-arc term \(N^3R^{-j}\), and
each improvement moved \(k\), \(j\) or \(\gamma\): \((7,1/6,\gamma)\to(2,1,\gamma)\to(1,1,c_0)\).
Here the binding major-arc term has \(k=0\), so the balance disappears:
\(\sigma\) is chosen only to make the minor arcs and the other major-arc
terms small, and the exponent is set by the binding term alone. That is why
the minor-arc \(j\) no longer matters for the exponent, and why the assigned
attack, had it succeeded, would have changed \(\sigma\) and nothing else.

## 4. The doors, restated

- **The target's threshold \(c_0\).** It is a parameter of the definition of
  \(E_{\rm corr}^{(Z)}\), not a theorem. Every admissible \(c_0\) under (H\(''\))
  gives a target with exponent exactly \(2c_0\); the family is indexed by
  \(c_0\) up to \(\min(1/12,\sqrt c/4,\sqrt b/4,c_P)\), and the constraint
  \(\sqrt b/4\) is the arc balance's last trace (the Page matching at
  \((R,R^3)\) with \(R=e^{2c_0\sqrt\ell}\)). Raising \(c_0\) changes the target
  and is not this assignment's to do; it is the operator's.
- **Siegel zeros.** Past \(2c_0\) for a fixed target: the corollary of
  `MAJOR_ARC_EXPLICIT.md` section 5.
- **The shape \(\sqrt\ell\).** Inherent to the inputs, `MAJOR_ARC_EXPLICIT.md`
  section 6, and now visible in a second way: the exponent is
  \(2c_0\sqrt\ell\) because the Page-allowed zero sits at \(1-c_0/\sqrt\ell\)
  and contributes \(N^{2\tilde\beta+1}\); the \(\sqrt\ell\) is the target's.
- **The polylogarithm.** \(\ell^{O(1)}\) from Vaughan's bound and from
  \((\tilde q/\phi(\tilde q))^3\); the lower bound has \(\tilde q^{-2}\). Not
  worth an attempt.
- **The minor-arc quartic** at cutoff \(R\): closed at this cutoff by the
  interval-length obstruction of section 1.2, and moot for the exponent by
  section 3. The one place it would matter is a target with a larger
  threshold, where \(\sigma=2c_0\) may exceed what the other major-arc terms
  allow, and \(j=2\) would buy room; that is a different target.

## 5. Finite checks

`sharp_exponent_probe.py`, results in `results_sharp_exponent_probe.json`,
five seconds. Neither item tests an asymptotic statement.

**(1) The decay (6) of \(I_\beta\).** For \(N\in\{10^4,10^6\}\), \(\beta=1-\kappa/\sqrt\ell\)
with \(\kappa\in\{0.1,0.3,1\}\), and forty values of \(N\theta\) from \(1\) to
\(200\), the largest value of \(|I_\beta(\theta)|\cdot N|\theta|/N^\beta\) is
\(0.36,\ 0.48,\ 2.03\) at \(N=10^4\) and \(0.35,\ 0.44,\ 1.42\) at \(N=10^6\),
against the constant \(e^{\kappa\sigma}\) (\(\sigma=\log200/\sqrt\ell\)) of
\(1.19,\ 1.69,\ 5.73\) and \(1.15,\ 1.53,\ 4.16\). The bound holds with room.
At \(\theta=0\), \(|I_\beta|/N^\beta\) is \(1.03\) to \(1.49\), inside the
trivial \(2N^\beta\).

**(2) The per-arc integral is flat in \(R\).** At \(N=10^4\),
\(\int_{|\theta|\le R/(rN)}|K_N(\theta)|^2|I_\beta(\theta)|^2d\theta/N^{2\beta+1}\)
for \(\kappa\in\{0.3,1\}\), \(r\in\{1,3,7\}\), \(R\in\{5,20,80\}\):

| \(\kappa\) | \(r=1\) | \(r=3\) | \(r=7\) |
| --- | --- | --- | --- |
| \(0.3\) | \(0.8145,\ 0.8145,\ 0.8145\) | \(0.8139,\ 0.8145,\ 0.8145\) | \(0.8101,\ 0.8144,\ 0.8145\) |
| \(1.0\) | \(1.4559,\ 1.4561,\ 1.4561\) | \(1.4540,\ 1.4560,\ 1.4561\) | \(1.4444,\ 1.4554,\ 1.4561\) |

(the three entries are \(R=5,20,80\)). A sixteenfold increase of \(R\) changes
the integral by less than \(0.1\%\): the mass sits within \(|\theta|\ll1/N\),
and the factor \(R\) that supremum-times-Parseval charged for this term is
not there.

## 6. Scope

The assigned attack was carried to the point where its obstruction is exact:
at cutoff \(R\) the Farey large sieve and Gallagher's lemma reproduce
Vaughan's bound to the order, the missing factor is the large sieve's slack
at interval length \(\asymp\sqrt N\), and no unconditional input supplies it;
a different dissection proves the literal target with the exceptional spikes
made explicit but is the arc split at a larger cutoff and moves nothing. The
mechanism chosen instead is bookkeeping on the major arcs, integrating the
one binding term over each arc with the decay of two explicit functions, and
it reaches the ceiling that `MAJOR_ARC_EXPLICIT.md` set: the exponent of the
fixed target is \(2c_0\). No power saving; the shape \(\sqrt\ell\) is
unchanged and inherent; nothing about the zeros of \(\zeta\); the lower half
of the two-sided statement is conditional on a Page-allowed zero existing
and is stated for odd conductors. Sections 1 to 3 have had an independent
read (`SHARP_EXPONENT_REVIEW.md`); its one non-binding defect is corrected
in place.
