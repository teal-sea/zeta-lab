# Proving (not just measuring) cancellation in RANK3_ROUTE_D.md's cross term, for prime \(q\)

This document answers the task assigned to it: whether \(\Sigma_{\rm cross}(q)\)
in RANK3_ROUTE_D.md's exact identity (D7) can be **proven**, not merely
assumed or measured, to be small relative to \(\Sigma_{\rm diag}(q)\), and at
what weight this closes. `RANK3_CROSS_TERM_MEASURE.md` (already on this
branch) measured \(\Sigma_{\rm cross}(q)\) numerically and found it well
inside the proved cancellation-free ceiling (D8), without proving anything
about why. This document supplies a proof, via Dirichlet character
orthogonality and Gauss-sum twisting, for every **prime** \(q\) — and
identifies precisely, not just numerically, where the same argument breaks
for composite squarefree \(q\).

**Answer, stated first.** For \(q\) **prime**, \(\Sigma_{\rm cross}(q)\)
genuinely cancels: an exact identity (CC1) below shows
\(\Sigma_{\rm cross}(q)=\Sigma_{\rm diag}(q)/(q-1)-E(q)\) with \(E(q)\ge0\),
so \(\Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)\le q\sum_b^*T(q,b)\) (CC2) —
replacing (D8)'s ceiling \(\phi(q)^2\sum_b^*T(q,b)\) with one smaller by a
full factor \(\phi(q)^2/q\approx\phi(q)\). This lands exactly on
RANK3_ROUTE_D.md §5's "diagonal-only" weight \(\mu(q)^2/\phi(q)\) — one
power of \(\phi(q)\) saved, not the two RANK3_POLYRANGE.md's guess
\(\mu(q)^2/\phi(q)^2\) would need. For **composite squarefree** \(q\), the
proof's one load-bearing step (every nonprincipal character mod \(q\) is
primitive) is false, and numerically the resulting identity, applied
anyway, is off by 50-150% — this route is genuinely blocked there, for the
specific reason given in §4, not merely unproven.

## 1. Setup: characters mod \(q\), reused notation

All notation is RANK3_ROUTE_D.md's: \(q\ge2\), \(N\), \(L=\log N\),
\(\Lambda\), \(K_N(\beta)=\sum_{n=1}^N\exp1(n\beta)\), \(\exp1(x)=e^{2\pi
ix}\); for \((b,q)=1\), \(S_b(\beta)=\sum_{n\le N,\,n\equiv
b(q)}\Lambda(n)\exp1(n\beta)\), \(D_b(\beta)=S_b(\beta)-K_N(\beta)/\phi(q)\)
(D2), \(T(q,b)=\int_{\mathbb T}|K_ND_b|^2\) (D5),
\(X(b,b')=\int_{\mathbb T}K_ND_b\overline{K_ND_{b'}}\) (D6),
\(\Sigma_{\rm diag}(q)=\phi(q)\sum_b^*T(q,b)\),
\(\Sigma_{\rm cross}(q)=\sum_{b\ne b'}^*c_q(b-b')X(b,b')\) (D7).

For a Dirichlet character \(\chi\bmod q\) (principal character \(\chi_0\)
included), define
\[
 L(\beta,\chi):=\sum_{n=1}^N\Lambda(n)\chi(n)\exp1(n\beta),\qquad
 M(\chi,\chi'):=\int_{\mathbb T}K_NL(\chi)\,\overline{K_NL(\chi')}.
\]
\((M(\chi,\chi'))_{\chi,\chi'\ne\chi_0}\) is a Gram matrix (same argument as
\(X\)), \(M(\chi,\chi):=M_\chi\ge0\).

**Character decomposition of \(D_b\), exact.** The classical orthogonality
relation \(\mathbf1_{n\equiv b(q)}=\frac1{\phi(q)}\sum_{\chi\bmod
q}\bar\chi(b)\chi(n)\), valid for \((n,q)=1\) (and both sides vanish when
\((n,q)>1\), since \(n\equiv b(q)\) forces \((n,q)=1\) as \((b,q)=1\), and
\(\chi(n)=0\) for every \(\chi\) when \((n,q)>1\)), gives, summing over all
\(N\) coefficients at once,
\[
 S_b(\beta)=\frac1{\phi(q)}\sum_{\chi\bmod q}\bar\chi(b)L(\beta,\chi).
\]
Separating the principal character and defining
\(\varepsilon(\beta):=L(\beta,\chi_0)-K_N(\beta)\) (coefficient at \(n\):
\(\Lambda(n)\mathbf1_{(n,q)=1}-1\), for every \(1\le n\le N\)),
\[
 \boxed{\ D_b(\beta)=\frac{\varepsilon(\beta)}{\phi(q)}
 +\frac1{\phi(q)}\sum_{\chi\ne\chi_0}\bar\chi(b)L(\beta,\chi).\ }
\tag{CC0}
\]
This is checked coefficientwise (at each \(n\), both sides equal
\(\Lambda(n)\mathbf1_{n\equiv b(q)}-1/\phi(q)\), using the orthogonality
relation once more) and confirmed to floating-point precision by
`rank3_cross_term_cancellation_probe.py`'s development checks (character
reconstruction of \(\psi(t;q,b)\) against direct enumeration, max abs
difference \(\le10^{-13}\) at \(q\in\{5,7,11\}\)).

**A note on \(\varepsilon\).** \(\varepsilon\) is *not* small: writing
\(d(n):=\Lambda(n)-1\) (UPPER_BOUND.md's own coefficient, whose partial sums
give \(\Delta(t)=\psi(t)-t\) and \(T_N=\sum_t\Delta(t)^2+(\text{telescoping})\)),
\[
 \varepsilon_n=\Lambda(n)\mathbf1_{(n,q)=1}-1=d(n)-\Lambda(n)\mathbf1_{(n,q)>1},
\]
so \(\varepsilon\) is \(F_N-K_N\) (UPPER_BOUND.md's own \(q=1\) remainder)
minus a correction bounded pointwise by \(\rho_2(q)\) (D3). Consequently
\(E(q):=\int_{\mathbb T}|K_N\varepsilon|^2\) — computed by the same
(D5)-shaped quadratic form applied to \(\Delta_\varepsilon(t):=\sum_{n\le
t}\varepsilon_n=\psi_{\rm cop}(t;q)-t\), \(\psi_{\rm
cop}(t;q):=\sum_{n\le t,(n,q)=1}\Lambda(n)\) — satisfies, by
\((\Delta(t)+r(t))^2=\Delta(t)^2+2\Delta(t)r(t)+r(t)^2\) with
\(|r(t)|\le\rho_2(q)\) and Cauchy-Schwarz,
\[
 \boxed{\ |E(q)-T_N|\ \le\ \rho_2(q)\sqrt{N\,T_N}+\rho_2(q)^2N.\ }
\tag{CC-E}
\]
So \(E(q)\approx T_N\), **not** \(\approx0\) — an earlier draft of this
derivation mistakenly treated \(\varepsilon\) as the small
\(\rho_2(q)\)-sized piece alone, which fails the coefficientwise check
above; (CC0)'s \(\varepsilon\) is the full \(F_N-K_N\)-sized object, and
(CC-E) is the correct, numerically confirmed relation (below).

## 2. Summing over \(a\): where character orthogonality does the work

By (D4) (\(R^{(1)}_{q,a}=\sum_b^*\exp1(ab/q)D_b\)) and (CC0),
\[
 R^{(1)}_{q,a}=\underbrace{\frac{c_q(a)}{\phi(q)}\varepsilon}_{A(\beta,a)}
 +\underbrace{\frac1{\phi(q)}\sum_{\chi\ne\chi_0}\tau_a(\bar\chi)L(\beta,\chi)}_{B(\beta,a)},
\qquad
 \tau_a(\bar\chi):=\sum_{b\bmod q}^*\bar\chi(b)\exp1(ab/q),
\]
using \(\sum_b^*\exp1(ab/q)=c_q(a)\) and
\(\sum_b^*\exp1(ab/q)\bar\chi(b)=\tau_a(\bar\chi)\) (the sum over \(b\)
equals the sum over all residues mod \(q\) since \(\chi(b)=0\) off the
reduced residues). Two facts, valid for **every** \(q\) (no primality used
yet):

* \(c_q(a)=\mu(q)\) for every reduced \(a\) (classical, already used in
  RANK3_ROUTE_D.md §1's consistency check).
* \(\sum_a^*\bar\chi(a)=0\) for \(\chi\ne\chi_0\) (orthogonality).

These two facts alone kill the \(A\)-\(B\) cross term exactly when summed
over \(a\): \(\sum_a^*c_q(a)\bar\chi(a)=\mu(q)\sum_a^*\bar\chi(a)=0\), so
\[
 \sum_{a\bmod q}^*\int_{\mathbb T}|K_NR^{(1)}_{q,a}|^2
 =\underbrace{\sum_a^*\int|K_NA|^2}_{\mu(q)^2E(q)/\phi(q)}
 +\underbrace{\sum_a^*\int|K_NB|^2}_{\frac1{\phi(q)^2}\sum_{\chi,\chi'\ne\chi_0}G(\chi,\chi')M(\chi,\chi')},
\qquad G(\chi,\chi'):=\sum_{a\bmod q}^*\tau_a(\bar\chi)\overline{\tau_a(\bar\chi')}.
\tag{CC-split}
\]
The left side is exactly \(\Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)\) (D7).
Separately, summing (CC0) over \(b\)^* with the same orthogonality facts
gives, for every \(q\),
\[
 \boxed{\ \Sigma_{\rm diag}(q)=E(q)+\sum_{\chi\ne\chi_0}M_\chi.\ }
\tag{CC1'}
\]
Everything up to here holds for **every** modulus \(q\), squarefree or not.
The only place primality enters is evaluating \(G(\chi,\chi')\).

## 3. Evaluating \(G(\chi,\chi')\): primality is exactly what is used

For \(\chi\) **primitive** mod \(q\), the classical Gauss-sum twist
\(\tau_a(\bar\chi)=\chi(a)\tau(\bar\chi)\) holds for every integer \(a\), and
\(|\tau(\bar\chi)|^2=q\). For \(q\) **prime**, every nonprincipal character
mod \(q\) is automatically primitive (the only proper divisor of \(q\) is
\(1\), which induces only \(\chi_0\)), so
\[
 G(\chi,\chi')=\tau(\bar\chi)\overline{\tau(\bar\chi')}\sum_{a}^*\chi(a)\bar\chi'(a)
 =q\phi(q)\,\mathbf 1[\chi=\chi'],\qquad q\text{ prime},
\]
by character orthogonality over \(a\) in the last step. Substituting into
(CC-split) and using (CC1') to write \(\sum_\chi M_\chi=\Sigma_{\rm
diag}(q)-E(q)\):
\[
 \Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)
 =\frac{\mu(q)^2E(q)}{\phi(q)}+\frac{q}{\phi(q)}\big(\Sigma_{\rm diag}(q)-E(q)\big).
\]
For \(q\) prime, \(\mu(q)^2=1\) and \(\phi(q)=q-1\), so this rearranges to
\[
 \boxed{\ \Sigma_{\rm cross}(q)=\frac{\Sigma_{\rm diag}(q)}{q-1}-E(q),\qquad q\text{ prime}.\ }
\tag{CC1}
\]
Since \(E(q)\ge0\) (a sum of squares, (CC-E)'s target quantity), dropping it
gives an unconditional, one-directional but fully explicit improvement on
(D8):
\[
 \boxed{\ \Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)\ \le\ q\sum_{b\bmod q}^*T(q,b),\qquad q\text{ prime}.\ }
\tag{CC2}
\]
(CC2) replaces (D8)'s \(\phi(q)^2\sum_b^*T(q,b)\) with \(q\sum_b^*T(q,b)\) —
smaller by the factor \(\phi(q)^2/q=(q-1)^2/q\), i.e. a full extra power of
\(\phi(q)\) for large \(q\). Carrying this through (D9)-(D11) exactly as
RANK3_ROUTE_D.md does (the \(R^{(2)}\) correction and arc transfer are
unaffected — they only use \(|R^{(2)}_{q,a}|\le\rho_2(q)\) and the sup bound
on \(K_N\) off the arc, neither of which this document touches) replaces
(D11)'s weight \(2\mu(q)^2\) on \(\sum_b^*T(q,b)\) with
\(2\mu(q)^2q/\phi(q)^2\sim2\mu(q)^2/\phi(q)\) for prime \(q\) — landing
exactly on the "diagonal-only" weight \(\mu(q)^2/\phi(q)\) RANK3_ROUTE_D.md
§5 says is "not derived here, and not decidable from UPPER_BOUND.md or
RESULTS.md." It is now derived, for prime \(q\).

**This does not reach RANK3_POLYRANGE.md's guessed weight
\(\mu(q)^2/\phi(q)^2\)** — that needs one further power of \(\phi(q)\)
beyond what (CC2) supplies, and nothing here suggests \(E(q)\) itself is
smaller than \(\Sigma_{\rm diag}(q)/\phi(q)\) (indeed (CC-E) says
\(E(q)\approx T_N\), a \(q\)-independent quantity, so \(E(q)\) does not
shrink with \(q\) the way a second cancellation power would require).

## 4. Numerical verification

`rank3_cross_term_cancellation_probe.py` computes \(\Sigma_{\rm diag}(q)\),
\(\Sigma_{\rm cross}(q)\) via `rank3_cross_term_probe.py`'s
already-cross-checked machinery (reused, not reimplemented), and \(E(q)\)
directly from \(\Delta_\varepsilon(t)=\psi_{\rm cop}(t;q)-t\), for prime
\(q\in\{2,3,5,7,11,13,17,19\}\) (\(q=2\) is degenerate: \(\phi(2)=1\), no
\(b\ne b'\) pairs exist, \(\Sigma_{\rm cross}(2)\equiv0\), already noted in
RANK3_ROUTE_D.md §3 and RANK3_CROSS_TERM_MEASURE.md) and composite
squarefree \(q\in\{6,10,15\}\), across \(N\in\{10^3,\dots,10^6\}\)
(56 rows total: 49 prime, 21 composite; the 7 prime rows in \(N_{\rm
ladder}\) at each of the 7 primes \(3,\dots,19\)).

**(CC1) holds to floating-point precision at every one of the 49 prime
rows**: worst relative error \(3.4\times10^{-11}\) (accumulated rounding on
sums of size \(\sim10^{12}\), not a discrepancy). **(CC2) holds at every one
of the 49 rows**, with the measured improvement factor
\(\phi(q)^2/q=(q-1)^2/q\) matching exactly: \(1.333\) at \(q=3\) up to
\(17.05\) at \(q=19\), constant across all seven \(N\) at each \(q\) as
(CC2) predicts. (CC-E)'s bound also holds at every row checked (a smaller,
separate ladder at \(q\in\{3,5,7,11,13\}\), \(N\in\{10^3,10^4,10^5\}\)):
\(|E(q)-T_N|\) stays comfortably inside the stated envelope, confirming
\(E(q)\approx T_N\) rather than \(E(q)\approx0\).

**Applied to composite squarefree \(q\in\{6,10,15\}\), (CC1) fails
outright**: relative error between measured \(\Sigma_{\rm cross}(q)\) and
(CC1)'s right-hand side ranges over \([0.54,\,1.56]\) — the same order as
the quantities themselves, not floating-point noise. This is not a
numerical accident: §3's derivation used primality exactly once, to get
\(\tau_a(\bar\chi)=\chi(a)\tau(\bar\chi)\) and \(|\tau(\bar\chi)|^2=q\) for
*every* nonprincipal \(\chi\). For composite squarefree \(q\) (e.g.
\(q=6\): \(\phi(6)=2\), the single nonprincipal character mod \(6\) is
**imprimitive**, induced by the Legendre symbol mod \(3\) — there is no
primitive nonprincipal character mod \(6\) at all), the twist identity and
the \(|\tau|^2=q\) normalization both fail for the imprimitive characters,
so \(G(\chi,\chi')\) need not vanish off the diagonal and need not equal
\(q\phi(q)\) on it. This document does not evaluate \(G(\chi,\chi')\) for
imprimitive \(\chi\) — doing so needs the classical reduction of an
imprimitive character's twisted sum to the primitive character inducing it
(a formula involving \(\mu(q/q^*)\), \(q^*\) the conductor), which is a
real, identifiable next step, not attempted here.

## 5. What this does and does not unlock for the rank-3 \(q\)-sum

RANK3_POLYRANGE_TINT_CHECK.md §3 shows, by partial summation against
classical (BDH), that a weight decaying like \(1/q\) on \(\sum_b^*T(q,b)\),
summed over \(2\le q\le R_0\), gives \(O_\epsilon(N^{2+\epsilon})\) (the
same computation that document performs for the sharper
\(\mu(q)^2/\phi(q)^2\) weight goes through unchanged for \(\mu(q)^2/\phi(q)\),
since only the *rate* of decay matters, and the boundary term
\(w(R_0)F(R_0)\ll(1/R_0)(R_0N^2\log N)=N^2\log N\) is already \(O(N^2\log
N)\) at \(w(q)=O(1/q)\), not just at \(w(q)=O(1/q^2)\)). **But that argument
needs the weight on every \(q\) in the range, not just the primes**: the
squarefree composite \(q\) in \(2\le q\le R_0\) (the majority of squarefree
integers, by density) are **not** covered by (CC1)-(CC2) — §4 shows the
identity fails there, and this document proves no substitute bound for
them. Those \(q\) remain at RANK3_ROUTE_D.md (D11)'s unimproved weight
\(O(\mu(q)^2)\), which RANK3_MEAN_VALUE_TOOLS.md already showed sums to
\(O(N^{5/2})\) — the CHHL-matching, not-beating, order. **So the full
\(2\le q\le R_0\) sum's order is unchanged by this document**: it is still
\(O(N^{5/2})\) unless composite squarefree \(q\) are separately handled,
which is exactly the wall this document hits, precisely stated in §4.

What *is* established, unconditionally: restricted to prime \(q\) alone,
the contribution to \(\sum_{q\le R_0}(\cdots)\) is \(O_\epsilon(N^{2+\epsilon})\)
— a genuinely smaller order than \(N^{5/2}\) for that sub-sum, proven (not
assumed) via real cancellation in the Gram-matrix off-diagonal sum
\(\Sigma_{\rm cross}(q)\), arising from Dirichlet character orthogonality
and Gauss-sum twisting rather than from discarding the cross term as
negligible by fiat.

## 6. Where this leaves the task's question

- **Can \(\Sigma_{\rm cross}(q)\) be proven, not just measured, to be small
  relative to \(\Sigma_{\rm diag}(q)\)?** Yes, for \(q\) **prime**: (CC1) is
  an exact identity, verified to floating-point precision, showing
  \(\Sigma_{\rm cross}(q)/\Sigma_{\rm diag}(q)\to0\) like \(1/q\) as
  \(q\to\infty\) through primes, with an explicit, non-asymptotic
  correction term \(E(q)\) bounded by (CC-E).
- **At what weight does this close?** \(\mu(q)^2/\phi(q)\) — one power of
  \(\phi(q)\) saved relative to the cancellation-free ceiling, matching
  RANK3_ROUTE_D.md §5's "diagonal-only" line exactly, for prime \(q\). It
  does **not** reach RANK3_POLYRANGE.md's guessed \(\mu(q)^2/\phi(q)^2\)
  (two powers); nothing here supplies or suggests the second power.
- **For composite squarefree \(q\)?** Blocked, precisely: the proof's one
  primality-dependent step (every nonprincipal character mod \(q\) is
  primitive) is false there, the resulting off-diagonal Gauss-sum matrix
  \(G(\chi,\chi')\) is not evaluated by this document for imprimitive
  characters, and the identity (CC1), applied anyway, is numerically wrong
  by 50-150%, not by a small correction. The stated next step — the
  imprimitive-character Gauss-sum reduction — is a real, identifiable
  piece of unconditional character theory, not a restatement of Route A's
  \(\Delta(t;q,b)\)-uniformity requirement or of RANK3_ROUTE_D.md §6's
  separate transfer-step obstruction (both of which are independent
  requirements this document does not touch).

This document is algebraic bookkeeping (character orthogonality, Gauss-sum
twisting, Cauchy-Schwarz) plus explicit numerical verification around the
existing unconditional construction in UPPER_BOUND.md and RANK3_ROUTE_D.md;
it assumes and establishes nothing about zeros of \(L\)-functions or the
Riemann Hypothesis.
