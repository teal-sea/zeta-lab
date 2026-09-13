# Extending the cross-term cancellation from prime \(q\) to composite squarefree \(q\)

This document answers the task assigned to it: whether
`RANK3_CROSS_TERM_CANCELLATION.md`'s identity \((CC1)\)-\((CC2)\), proved
there only for **prime** \(q\), extends to **composite squarefree** \(q\)
(\(q\) with \(\ge2\) distinct prime factors, \(\mu(q)^2\ne0\)), by evaluating
the off-diagonal Gauss-sum matrix \(G(\chi,\chi')\) from that document's §3
for every pair of nonprincipal characters mod \(q\), imprimitive ones
included.

**Answer, stated first.** Yes, and by a wider margin than
`RANK3_CROSS_TERM_CANCELLATION.md` §4 anticipated. \(G(\chi,\chi')=0\) for
\(\chi\ne\chi'\) **unconditionally** — for every modulus \(q\) (not just
squarefree, not just composite, not just prime) and every pair of
characters mod \(q\) (not just primitive ones) — because the fact that
kills the off-diagonal never needed primitivity in the first place; the
identity `RANK3_CROSS_TERM_CANCELLATION.md` derived only for prime \(q\)
used a *stronger* fact than the off-diagonal vanishing actually requires.
What primality (or, as it turns out, squarefreeness) genuinely buys is the
**diagonal normalization** \(G(\chi,\chi)\), which is \(\phi(q)\cdot q\) only
when \(\chi\) is primitive mod \(q\) — for imprimitive \(\chi\), it is
\(\phi(q)\) times \(\chi\)'s **conductor**, a strictly smaller number. With
that one correction, `RANK3_CROSS_TERM_CANCELLATION.md` §3's derivation goes
through for every squarefree \(q\) and yields the exact identity \((CT1)\)
below, which specializes to \((CC1)\) at prime \(q\) and is verified here to
floating-point precision at \(q\in\{6,10,14,15,21\}\), \(N\) up to \(10^6\).
The resulting bound on \(\Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)\) is
**exactly** \(q\sum_b^*T(q,b)\) — the same ceiling \((CC2)\) proves for prime
\(q\), reached here for every squarefree \(q\), with one honestly-stated
caveat in §5 about when that ceiling actually beats the cancellation-free
one.

All notation is `RANK3_CROSS_TERM_CANCELLATION.md`'s (itself reusing
`RANK3_ROUTE_D.md`'s): \(q\ge2\) squarefree, \(\chi_0\) the principal
character mod \(q\), \(L(\beta,\chi)=\sum_{n\le N}\Lambda(n)\chi(n)\exp1(n\beta)\),
\(M(\chi,\chi')=\int_{\mathbb T}K_NL(\chi)\overline{K_NL(\chi')}\),
\(M_\chi:=M(\chi,\chi)\ge0\), \(\tau_a(\bar\chi)=\sum_{b\bmod q}^*\bar\chi(b)\exp1(ab/q)\),
\(G(\chi,\chi')=\sum_{a\bmod q}^*\tau_a(\bar\chi)\overline{\tau_a(\bar\chi')}\),
\(E(q)\), \(\Sigma_{\rm diag}(q)\), \(\Sigma_{\rm cross}(q)\) as before.
`RANK3_CROSS_TERM_CANCELLATION.md` §2's identity (CC-split) and (CC1') are
established there for **every** modulus \(q\) with no primality used, and
are simply reused here unchanged:
\[
 \Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)
 =\frac{\mu(q)^2E(q)}{\phi(q)}+\frac1{\phi(q)^2}\sum_{\chi,\chi'\ne\chi_0}G(\chi,\chi')M(\chi,\chi'),
\qquad
 \Sigma_{\rm diag}(q)=E(q)+\sum_{\chi\ne\chi_0}M_\chi.
\tag{CC-split, CC1'}
\]
Everything below evaluates \(G(\chi,\chi')\) for composite squarefree \(q\),
which is the one piece §3 of the source document left undone.

## 1. \(G(\chi,\chi')=0\) off the diagonal: no primitivity needed at all

Fix any modulus \(q\ge1\) and any two Dirichlet characters \(\chi,\chi'\) mod
\(q\) (principal or not, primitive or not). For \(a\) with \((a,q)=1\), the
map \(b\mapsto ab\bmod q\) is a **bijection of the full residue ring**
\(\mathbb Z/q\mathbb Z\) onto itself (its inverse is \(b\mapsto\bar ab\)),
and \(\chi\) is completely multiplicative on all of \(\mathbb Z/q\mathbb Z\)
(with \(\chi(n)=0\) exactly when \((n,q)>1\), and \(\chi(ab)=\chi(a)\chi(b)\)
holding in that case too, both sides \(0\) together, since \((ab,q)>1\iff(b,q)>1\)
when \((a,q)=1\)). So, summing over **all** residues \(b\bmod q\) (the
non-reduced ones contribute \(0\) on both sides, so restricting to the
reduced residues, as \(\tau_a\)'s definition does, changes nothing):
\[
 \tau_a(\bar\chi)=\sum_{b\bmod q}\bar\chi(b)\exp1(ab/q)
 \overset{b=a^{-1}b'}=\sum_{b'\bmod q}\bar\chi(a^{-1}b')\exp1(b'/q)
 =\chi(a)\sum_{b'\bmod q}\bar\chi(b')\exp1(b'/q)=\chi(a)\,\tau(\bar\chi),
\tag{T1}
\]
where \(\tau(\bar\chi):=\tau_1(\bar\chi)\). **This holds for every character
mod every modulus, with no primitivity or squarefreeness hypothesis
anywhere** — the classical fact that fails for imprimitive \(\chi\) is a
*different* one, the reduction of \(\tau(\chi)\) **itself** to the Gauss sum
of the primitive character inducing it (§2 below); the twisting relation
(T1) is not that fact and does not need it.
`RANK3_CROSS_TERM_CANCELLATION.md` §3 invoked primitivity to get (T1) (it
only needed it for primitive \(\chi\), which is all prime \(q\) has), but
(T1) was never actually conditional on primitivity — it is conditional only
on \((a,q)=1\), which is exactly the range \(\tau_a\) is summed over
throughout.

Substituting (T1) into the definition of \(G\) and using plain character
orthogonality over \(a\) (valid for any two characters mod any \(q\)):
\[
 G(\chi,\chi')=\tau(\bar\chi)\overline{\tau(\bar\chi')}\sum_{a\bmod q}^*\chi(a)\bar\chi'(a)
 =\phi(q)\,\tau(\bar\chi)\overline{\tau(\bar\chi')}\,\mathbf1[\chi=\chi'].
\tag{G1}
\]
\[
 \boxed{\ G(\chi,\chi')=0\text{ whenever }\chi\ne\chi',\text{ for every modulus }q\text{ and every pair of characters mod }q.\ }
\]
This alone already answers the off-diagonal half of the task's question: the
Gauss-sum matrix is diagonal unconditionally, not just for primitive
characters or prime moduli. What remains is the diagonal value
\(G(\chi,\chi)=\phi(q)|\tau(\bar\chi)|^2\), and *that* is where primitivity
(via squarefreeness) genuinely enters.

## 2. The diagonal value: \(|\tau(\chi)|^2\) is the conductor, not \(q\)

For \(\chi\) **primitive** mod \(q\), \(|\tau(\chi)|^2=q\) is the classical
fact `RANK3_CROSS_TERM_CANCELLATION.md` used, and every nonprincipal \(\chi\)
mod a **prime** \(q\) is primitive, which is what made \(G(\chi,\chi)=q\phi(q)\)
uniformly there. For **imprimitive** \(\chi\) mod \(q\), induced by the
primitive character \(\chi^*\) mod its conductor \(q^*\mid q\), \(q^*<q\),
the classical reduction of an imprimitive Gauss sum to the primitive one
inducing it is, writing \(d:=q/q^*\),
\[
 \tau(\chi)=\mu(d)\,\chi^*(d)\,\tau(\chi^*),
\tag{T2}
\]
**valid when \(\gcd(d,q^*)=1\)** (this hypothesis is exactly why the task
restricts to squarefree \(q\): for \(q\) squarefree, *every* divisor pair
\(q^*\mid q\), \(d=q/q^*\), automatically satisfies \(\gcd(d,q^*)=1\), since
\(q\)'s prime factorization has every prime to the first power, so \(q^*\)
and \(d\) partition the prime factors of \(q\) with no overlap; for
non-squarefree \(q\) this would fail and (T2) would need the more general
induced-modulus formula). (T2) can be checked directly by the same
substitution technique as (T1): decompose \(b\bmod q\) via CRT as
\((u,v)=(b\bmod q^*,b\bmod d)\) (a bijection on reduced residues since
\(\gcd(q^*,d)=1\)), write \(b/q=ux/q^*+vy/d\) for the Bézout pair
\(dx+q^*y=1\), and split \(\tau(\chi)=\sum_b^*\chi^*(u)\exp1(b/q)\) into a
primitive Gauss sum in \(u\) (using \(\chi(b)=\chi^*(u)\) for \((b,q)=1\),
the defining property of induction) times a Ramanujan sum in \(v\), which
evaluates to \(\mu(d)\) exactly as \(c_q(a)=\mu(q)\) does for \((a,q)=1\)
(the two facts are the same computation, one with \(\chi^*\) inserted and
one without). Since \(|\chi^*(d)|=1\) (\((d,q^*)=1\)) and \(|\tau(\chi^*)|^2=q^*\)
(the primitive case), (T2) gives
\[
 \boxed{\ |\tau(\chi)|^2=q^*=\operatorname{cond}(\chi),\qquad q\text{ squarefree}.\ }
\tag{T3}
\]
Combining (G1) and (T3):
\[
 \boxed{\ G(\chi,\chi')=\phi(q)\cdot\operatorname{cond}(\chi)\cdot\mathbf1[\chi=\chi'],\qquad q\text{ squarefree}.\ }
\tag{G2}
\]
At prime \(q\), \(\operatorname{cond}(\chi)=q\) for every nonprincipal
\(\chi\) (its only proper divisor is \(1\), which induces only \(\chi_0\)),
so (G2) reduces to `RANK3_CROSS_TERM_CANCELLATION.md` §3's
\(G(\chi,\chi')=q\phi(q)\mathbf1[\chi=\chi']\) exactly. For composite
squarefree \(q\), \(\operatorname{cond}(\chi)\) genuinely varies over the
nonprincipal characters — this is the one place the prime and composite
cases differ, and it is a normalization difference, not a failure of
diagonality.

## 3. Reworking §3's derivation: the exact identity for composite squarefree \(q\)

Substituting (G2) into (CC-split), using \(\mu(q)^2=1\) (squarefree \(q\)):
\[
 \Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)
 =\frac{E(q)}{\phi(q)}+\frac1{\phi(q)}\sum_{\chi\ne\chi_0}\operatorname{cond}(\chi)\,M_\chi.
\tag{CT0}
\]
Write \(\operatorname{cond}(\chi)=q-(q-\operatorname{cond}(\chi))\) and define
\[
 W(q):=\sum_{\chi\ne\chi_0}\big(q-\operatorname{cond}(\chi)\big)M_\chi\ \ge0
\]
(nonnegative: \(\operatorname{cond}(\chi)\le q\) always, and \(M_\chi\ge0\)
as a Gram-matrix diagonal entry). Then \(\sum_\chi\operatorname{cond}(\chi)M_\chi
=q\sum_\chi M_\chi-W(q)=q\big(\Sigma_{\rm diag}(q)-E(q)\big)-W(q)\), using
(CC1'). Substituting into (CT0) and solving for \(\Sigma_{\rm cross}(q)\)
(the same algebra `RANK3_CROSS_TERM_CANCELLATION.md` §3 performs, carried
through with \(\operatorname{cond}(\chi)\) in place of the constant \(q\)):
\[
 \boxed{\ \Sigma_{\rm cross}(q)=\frac{(q-\phi(q))\,\Sigma_{\rm diag}(q)-(q-1)E(q)-W(q)}{\phi(q)},
 \qquad q\text{ squarefree}.\ }
\tag{CT1}
\]
At prime \(q\): \(\operatorname{cond}(\chi)=q\) for every nonprincipal
\(\chi\), so \(W(q)\equiv0\), \(q-\phi(q)=1\), \(\phi(q)=q-1\), and (CT1)
reads \(\Sigma_{\rm cross}(q)=\big[\Sigma_{\rm diag}(q)-(q-1)E(q)\big]/(q-1)
=\Sigma_{\rm diag}(q)/(q-1)-E(q)\) — exactly \((CC1)\). (CT1) is the
requested generalization: an **exact identity**, for every squarefree \(q\),
reducing to (CC1) at prime \(q\) with \(W(q)\) as the single new,
manifestly nonnegative term that composite moduli introduce.

Since \(E(q)\ge0\), \(W(q)\ge0\), and \(q\ge\phi(q)\), dropping both
nonnegative subtracted terms from (CT1) gives the one-directional bound
\[
 \Sigma_{\rm cross}(q)\ \le\ \frac{(q-\phi(q))\Sigma_{\rm diag}(q)}{\phi(q)},
\]
and adding \(\Sigma_{\rm diag}(q)\) to both sides,
\[
 \boxed{\ \Sigma_{\rm diag}(q)+\Sigma_{\rm cross}(q)\ \le\ q\sum_{b\bmod q}^*T(q,b),\qquad q\text{ squarefree}.\ }
\tag{CT2}
\]
This is **exactly** \((CC2)\)'s bound — the prime-only ceiling
`RANK3_CROSS_TERM_CANCELLATION.md` proved now holds, unconditionally, for
*every* squarefree \(q\), composite included. The derivation needed nothing
beyond §1-§2's evaluation of \(G\); the rest of the algebra is identical to
the prime case, character-conductor bookkeeping aside.

## 4. Numerical verification

`rank3_composite_cross_term_probe.py` checks three independent things, at
\(q\in\{6,10,14,15,21\}\) (the squarefree composite moduli named in the
task) across \(N\in\{10^3,3\times10^3,10^4,3\times10^4,10^5,3\times10^5,10^6\}\)
(35 rows), reusing `rank3_cross_term_probe.py`'s `reduced_residues`,
`delta_table`, `T_and_X`, `ramanujan_sum_direct` for \(\Sigma_{\rm diag}(q)\)
and \(\Sigma_{\rm cross}(q)\) (not reimplemented) and
`rank3_cross_term_cancellation_probe.py`'s `E_quantity` for \(E(q)\) (also
not reimplemented). Characters mod \(q\) are enumerated as CRT products of
cyclic characters at each prime factor (discrete logs against a primitive
root at each small prime \(2,3,5,7\)); \(M_\chi\) is computed from the
complex partial sums \(S_\chi(t)=\sum_{n\le t}\Lambda(n)\chi(n)\) by the same
(D5)-shaped Parseval formula \(T(q,b)\) uses, and cross-checked at \((q,N)=(6,500)\)
against an independent explicit convolution of \(\Lambda(n)\chi(n)\) with the
constant sequence \(1\) (max abs difference \(3.6\times10^{-12}\) on a
quantity of size \(\sim3\times10^4\)).

**(1) \(G(\chi,\chi')\), brute-force from its definition** (no Gauss-sum
formula assumed — direct computation of \(\tau_a(\bar\chi)\) for every
reduced residue \(a\) and every character, then the double sum defining
\(G\)): at every \(q\in\{6,10,14,15,21\}\), the maximum off-diagonal
\(|G(\chi,\chi')|\) is \(\le5.2\times10^{-13}\) (floating-point zero on
quantities of size \(\sim10^2\)), and every diagonal entry matches
\(\phi(q)\cdot\operatorname{cond}(\chi)\) to relative error \(\le5.3\times10^{-15}\).
This independently confirms (G2) without relying on the algebraic
derivation in §1-§2 at all.

**(2) (CC1'), \(\Sigma_{\rm diag}(q)=E(q)+\sum_\chi M_\chi\)**, already
established for every \(q\) in the source document, holds here at composite
squarefree \(q\) to worst relative error \(2.6\times10^{-12}\) across all 35
rows — a sanity check on the character/\(M_\chi\) machinery introduced in
this document, independent of \(G\).

**(3) The new identity (CT1)**, computed as
`predicted = [(q-phi(q))*Sigma_diag(q) - (q-1)*E(q) - W(q)] / phi(q)` and
compared against the directly-measured \(\Sigma_{\rm cross}(q)\) (from
\(c_q(b-b')X(b,b')\), `rank3_cross_term_probe.py`'s machinery, entirely
independent of characters), holds to worst relative error \(7.4\times10^{-11}\)
across all 35 rows (\(5\) moduli \(\times\) \(7\) values of \(N\)) — the same
order of floating-point accumulation error the prime-\(q\) check in
`RANK3_CROSS_TERM_CANCELLATION.md` reports (\(3.4\times10^{-11}\)), not a
discrepancy. **(CT2) holds at every one of the 35 rows.** This directly
contradicts the *naive* application of (CC1) that
`RANK3_CROSS_TERM_CANCELLATION.md` §4 reports failing by 50-150% at these
same moduli — that failure came from assuming \(\operatorname{cond}(\chi)=q\)
uniformly (i.e. using (CC1) verbatim), not from any failure of the
underlying cancellation; replacing \(q\) with \(\operatorname{cond}(\chi)\)
character-by-character, as (CT1) does, repairs it completely.

Full rows are in `results_rank3_composite_cross_term_probe.json`.

## 5. Where the composite-\(q\) ceiling differs from the prime case: when does it actually help?

(CT2)'s bound \(q\sum_b^*T(q,b)\) is only useful if it beats the
cancellation-free ceiling \(\phi(q)^2\sum_b^*T(q,b)\) that (D8) already
proves unconditionally (`RANK3_ROUTE_D.md` §3) — i.e. only when
\(\phi(q)^2>q\). For **prime** \(q\ge3\), \((q-1)^2>q\) always
(\(q^2-3q+1>0\) for \(q\ge3\)), so (CC2) is a genuine improvement at every
prime \(q\ge3\) (checked already in `RANK3_CROSS_TERM_CANCELLATION.md` §4:
improvement factor \(1.333\) at \(q=3\) up to \(17.05\) at \(q=19\)). For
**composite squarefree** \(q\), this is no longer automatic: \(\phi(q)\) can
be small relative to \(\sqrt q\) when \(q\) has several small prime factors.
Checking every squarefree \(q\le200\) directly: \(\phi(q)^2<q\) — (CT2)'s
bound *worse* than the trivial one — holds only at \(q=2\) (degenerate,
\(\Sigma_{\rm cross}(2)\equiv0\) already) and \(q=6\) (\(\phi(6)=2\),
\(4<6\)) in that entire range; every other squarefree \(q\in[3,200]\),
composite or prime, has \(\phi(q)^2>q\). Among this document's own five test
moduli, \(q=6\) is exactly this exception (improvement factor
\(\phi(6)^2/6=2/3<1\), confirmed in the numerical run above); \(q\in\{10,14,15,21\}\)
all show genuine improvement (\(1.6\), \(2.57\), \(4.27\), \(6.86\)
respectively — the same column `rank3_composite_cross_term_probe.py` prints
as `improvement`).

This is not a defect in (CT1)-(CT2)'s derivation — both are exact/proven
regardless — it is a fact about which bound is *sharper* at a given \(q\),
and it is finite in extent: since \(\phi(q)\gg q/\log\log q\) uniformly
(Mertens' third theorem), \(\phi(q)^2\gg q^2/(\log\log q)^2\gg q\) once
\(\log\log q\) is smaller than \(\sqrt q/(\text{absolute constant})\), i.e.
for all \(q\) past some small, absolute, computable threshold — the direct
check above already shows that threshold is at most \(6\) for every
squarefree \(q\), which strongly suggests (but this document does not
prove) that \(q=2,6\) are the *only* squarefree exceptions, full stop, not
just up to \(200\). Whichever way that goes, taking \(\min\big(\phi(q)^2,q\big)\sum_b^*T(q,b)\)
termwise (both bounds are proven, independently, for every squarefree \(q\))
loses nothing: the composite-\(q\) extension is never worse than what
`RANK3_ROUTE_D.md` (D8) already had, and is strictly better at every
squarefree \(q\ge3\) except (at most, and apparently exactly) \(q=6\).

**A second, separate caveat**, for whoever carries this into
`RANK3_POLYRANGE_TINT_CHECK.md` §3's partial-summation argument over
\(2\le q\le R_0\): that argument (per `RANK3_CROSS_TERM_CANCELLATION.md` §5)
needs a weight on \(\sum_b^*T(q,b)\) decaying like \(1/q\) (or \(1/\phi(q)\),
the same order) after the \((\mu(q)/\phi(q))^2\) prefactor is folded in.
Following `RANK3_ROUTE_D.md` (D9)-(D11)'s assembly, (CT2)'s ceiling
contributes weight \(\mu(q)^2\,q/\phi(q)^2\) to \(\sum_b^*T(q,b)\) — at prime
\(q\), \(q/\phi(q)^2\sim1/q\sim1/\phi(q)\), matching the "diagonal-only"
target weight `RANK3_ROUTE_D.md` §5 names. At composite squarefree \(q\),
\(q/\phi(q)^2=(q/\phi(q))/\phi(q)=O(\log\log q)/\phi(q)\) by the same Mertens
bound — the same order as the prime case **up to an extra
\(\log\log q\) factor**, not a full extra power of \(q\) or \(\phi(q)\). This
document does not redo `RANK3_POLYRANGE_TINT_CHECK.md` §3's partial
summation with this exact weight to confirm the \(\log\log q\) factor is
absorbed into that argument's \(N^\epsilon\) — that check is a real,
identifiable next step, not attempted here, and is the one piece still
needed to carry (CT2) all the way to `RANK3_CROSS_TERM_CANCELLATION.md` §5's
conclusion ("full \(2\le q\le R_0\) sum's order is unchanged... unless
composite squarefree \(q\) are separately handled") being overturned.

## 6. What this does and does not unlock

`RANK3_CROSS_TERM_CANCELLATION.md` §4-§6 identified composite squarefree
\(q\) as genuinely blocked for Route D's \(q\)-sum, because its identity
(CC1), applied to them, was numerically wrong by 50-150%, and it supplied no
substitute. This document supplies that substitute: (CT1) is an exact
identity for every squarefree \(q\), verified to floating-point precision,
and (CT2) — the resulting bound — is **exactly** the same ceiling (CC2)
proves for primes, not a weaker one, for every squarefree \(q\) except the
finite (apparently just \(\{2,6\}\)) set where the trivial Cauchy-Schwarz
ceiling (D8) was already smaller. So `RANK3_CROSS_TERM_CANCELLATION.md` §5's
statement that "the squarefree composite \(q\)... are not covered by
(CC1)-(CC2)" no longer holds: they are covered, by (CT1)-(CT2), at the same
weight. What is **not** done here is §5's remaining half: confirming that
`RANK3_POLYRANGE_TINT_CHECK.md`'s partial-summation argument, applied to the
\(\mu(q)^2q/\phi(q)^2\) weight (rather than the \(\mu(q)^2/\phi(q))\) weight
that argument was checked against), still gives \(O_\epsilon(N^{2+\epsilon})\)
once summed over the *full* range \(2\le q\le R_0\) including composite
\(q\) — precisely stated as the wall in §5 above. Nothing in this document
touches rank 1, `RANK3_SCOPE.md` §4's separate bottleneck (rank 1's
\(O_H(N^3L^{-2H})\) term dominates (23) regardless of ranks 2-3), or any
statement about zeros of \(L\)-functions or the Riemann Hypothesis; this is
character-sum algebra (orthogonality, Gauss-sum twisting and reduction,
Cauchy-Schwarz-free exact bookkeeping) plus explicit floating-point
verification around the existing unconditional construction.
