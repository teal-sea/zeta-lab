# Review of ENDPOINT_SHARP.md, third revision, section 4 only

Independent check, 2026-09-11 (attempt `a-0077`). Scope: only the two
substitutions of section 4 (the progression input (DF) and the separate
sieve level \(D_1\)), which postdate `ENDPOINT_SHARP_REVIEW.md` and are
explicitly marked there as not yet covered. Sections 2, 3, 5 and 6 are not
re-reviewed here; `ENDPOINT_SHARP_REVIEW.md`'s verdicts on those stand.

Read: `ENDPOINT_SHARP.md` sections 1, 4, 7 item (5) and 8;
`ENDPOINT_SHARP_REVIEW.md`; `ENDPOINT_BOUND.md` section 4;
`SIEGEL_UNIFORMITY.md` section 3.

This attempt has no network access in its tool set (`python`, `grep`, `rg`,
`ls`, `cat`, `head`, `tail`, `wc`, `find` only), so the (DF) quotation
against the arXiv source was not independently checked here; it is treated
as given, per the document's own note that it was compared against the
source in the orchestrator session. Everything else below was recomputed
from scratch with a new script, `review2_sharp_section4_probe.py`, results
in `results_review2_sharp_section4_probe.json`, not derived from any prior
probe in this directory.

## Item 1: the sieve level

**Verdict: confirmed**, both the diagnosis of the defect in the first two
versions and the repair.

**The diagnosis.** At \(\kappa=1/2\), (A) gives \(A(N)=4c/\log\ell\to0\), so
if the fundamental lemma were applied at the approximant level \(D_0\), the
sieve parameter would be \(s=A(N)\sqrt\ell=(4c/\log\ell)\sqrt\ell(1+o(1))\).
This exponent is \(o(\sqrt\ell)\): for any fixed \(\gamma>0\),
\((4c/\log\ell)/\gamma\to0\) as \(\ell\to\infty\), so
\(A(N)\sqrt\ell=o(\gamma\sqrt\ell)\) for every fixed \(\gamma\), i.e.
\(e^{9-s}\) decays strictly slower than \(\exp(-\gamma\sqrt\ell)\) for
every fixed \(\gamma\). The diagnosis is correct: the displayed error at
level \(D_0\) cannot supply the target rate, and (1\('\)) did not follow at
that level as written.

**The repair, recomputed independently.** With \(D_1=\lfloor N^{1/2}\rfloor\),
\(Z=e^{\sqrt\ell}\):
\[
 s_1=\frac{\log D_1}{\log Z},\qquad\text{hypothesis: } D_1\ge Z^{10}.
\]
I recomputed \(s_1\) and the hypothesis directly from \(N\) and \(Z\)
(50-60 digit arithmetic, no use of the document's asymptotic formulas):

| \(\log N\) | \(s_1\) (exact) | \(\sqrt\ell/2\) | \(D_1\ge Z^{10}\)? |
| --- | --- | --- | --- |
| 100 | 5.000000 | 5.000000 | **no** |
| 399 | 9.987492 | 9.987492 | **no** |
| 400 | 10.000000 | 10.000000 | **yes** (equality) |
| 401 | 10.012492 | 10.012492 | yes |
| 1000 | 15.811388 | 15.811388 | yes |
| 10000 | 50.000000 | 50.000000 | yes |

This confirms the document's claim exactly: \(D_1\ge Z^{10}\) holds if and
only if \(\log N\ge400\), with equality at exactly \(\log N=400\) (the
crossing is not merely asymptotic here; the floor in \(D_1\) changes
\(\log D_1\) by \(O(N^{-1/2})\), negligible at this scale, so the
integer-valued check and the continuous formula agree to the precision
shown). The document's \(s_1=\sqrt\ell/2(1+o(1))\) is confirmed, and if
anything is more accurate than stated: the correction from flooring is
\(O(N^{-1/2}/\sqrt\ell)\) relative, far smaller than a generic \(o(1)\).

**All four cases of section 4, recomputed with \(D_1\).** Using
\(e^{9-s_1}=e^9\exp(-\sqrt\ell/2(1+o(1)))\), \(b\sim e^{\gamma_E}\sqrt\ell\),
\(q<Z=e^{\sqrt\ell}\):

- \((a,r)>1\): untouched by the level, bound \(\ll\ell^2\), as before.
- untwisted, \((a,r)=1\): main term \(y/\phi(r)\), error
  \(O(Ne^{9-s_1}+bD_1)=O(Ne^{9-\sqrt\ell/2}+\sqrt\ell N^{1/2})\). Matches
  (427)-(428).
- twisted, \(q\mid r\): main term
  \(\chi(a)(y^\beta-1)/(\phi(r)\beta)\), error of the same two orders.
  Matches (438), (441).
- twisted, \(q\nmid r\): main term vanishes by character-sum cancellation
  (unaffected by the level, checked again below); error
  \(N(\log\ell)e^{9-s_1}+bqD_1\ll N(\log\ell)e^{9-\sqrt\ell/2}+\sqrt\ell\,
  e^{\sqrt\ell}N^{1/2}\). Matches (4.2), and the second term is
  \(N^{1/2+o(1)}\), safely below \(N\exp(-\gamma\sqrt\ell)\) for any fixed
  \(\gamma\) since \(\log N=\ell\gg\sqrt\ell\) dominates the comparison.

I re-derived the final admissible range independently rather than just
re-reading it off: the four error sources are \(O(N\exp(-c_0\sqrt\ell/2))\)
(exceptional-character mismatch, from item 3 below),
\(O(N\exp(-\delta\sqrt\ell/\sqrt2))\) (the (DF) Bombieri-Vinogradov term at
\(\log y\ge\ell/2\)), and \(O(Ne^{9-\sqrt\ell/2})\) (the sieve level
\(D_1\) itself, dropping the fixed constant \(e^9\)). Collecting exponents
gives exactly
\[
 \gamma<\min(c_0/2,\ \delta/\sqrt2,\ 1/2),
\]
matching the document's displayed range. The "\(1/2\)" is exactly and only
the sieve-level term; nothing else in section 4 contributes a competing
constant near \(1/2\).

**\(D_1\) does not leak outside section 4.** I grepped every occurrence of
`D_1` and `D_0` in the document. `D_1` appears only in section 1's
definition, section 4 throughout, and section 7 item (5)'s recomputation
note; one further mention in section 6's qualitative "what fixes the
exponent" paragraph uses \(s_1=\log D_1/\log Z\) generically to describe
why the *proof method* stops working past \(\kappa=1/2\), not as a
substituted value in an equation. Equation (18\('\)) uses only \(D_0=N^{A(N)}\),
and property (P4) in section 2.2 is stated only in terms of \(D_0\). So the
claim that \(D_1\) "enters nothing outside section 4" is confirmed exactly:
no equation elsewhere in the document plugs in \(D_1\) or \(N^{1/2}\) as
the level for anything but the progression sieve of section 4.

## Item 2: the progression input (DF)

**No web access used**, consistent with this attempt's tool restrictions
(`python`/`grep`/`rg`/`ls`/`cat`/`head`/`tail`/`wc`/`find` only, no
network). The quotation of Drappeau-Fiorilli's Lemma 2.2, their Theorem
1.2, their \(x\)-exceptional-character definition, and their (1.6) are
therefore treated as given, per the document's own record that they were
compared against arXiv:2003.02201v1 in the orchestrator session. I checked
only the mathematics built on top of the quotation.

**(a) Derivation of (D\('\)): confirmed.** Setting \(x:=y\) and \(Q:=R\) in
the quoted lemma and bounding the single term \((q,y)=(r,y)\) by the whole
sum over \(q\le R\), \(y'\le y\) gives
\[
 \big|\psi(y;r,a)-(1-\eta_{y,a}1_{\tilde q\mid r})\tfrac y{\phi(r)}\big|
 \ll ye^{-\delta\sqrt{\log y}}+R\sqrt y(\log y)^{O(1)}.
\]
With \(\eta_{y,a}=\tilde\chi(a)/(\beta y^{1-\beta})\), \(\eta_{y,a}\,y=
\tilde\chi(a)y^\beta/\beta\) is immediate algebra (\(y\cdot y^{1-\beta}\!
{}^{-1}=y^\beta\)), and expanding the product
\((1-\eta_{y,a}1_{\tilde q\mid r})y/\phi(r)\) gives exactly (D\('\)) as
displayed, equation (337)-(339). Confirmed.

**(b) The frozen-at-\(x\) remark: confirmed by direct computation, and it
is a real feature of the quoted statement, not a document error.** The
document observes that if the lemma's uniformity in \(y\le x\) were taken
literally with \(\eta_{x,a}\) frozen at \(x\), the exceptional term at a
shorter prefix \(y<x\) would differ from the "correct" \(y\)-frozen term
\(\tilde\chi(a)y^\beta/\beta\) by
\[
 \Delta(x,y,\beta)=\tilde\chi(a)\,y\,x^{\beta-1}\big((x/y)^{1-\beta}-1\big)/\beta,
\]
and claims this, summed over \(\tilde q\mid q\le Q\), is not
\(O(xe^{-\delta\sqrt{\log x}})\) when \(1-\beta\) and
\(\log(x/y)/\sqrt{\log x}\) are both small compared with \(\delta\). I
first checked the algebra: writing \(L=\log(x/y)\), \(\varepsilon=1-\beta\),
\(y\,x^{\beta-1}=yx^{-\varepsilon}=xe^{-L-\varepsilon\log x}\), so
\(|\Delta|=xe^{-L-\varepsilon\log x}\,\varepsilon\)-scale terms exactly as
the document states; direct symbolic evaluation of
\(yx^{\beta-1}((x/y)^{1-\beta}-1)/\beta\) against \(\eta_{x,a}y-\tilde\chi(a)y^\beta/\beta\)
agrees to 49 of 50 computed digits (the last-digit discrepancy is
floating-point rounding at that precision, not a mismatch).

Naively one might expect a fixed \(\varepsilon=c_0/\sqrt{\log x}\) (the
extremal size an exceptional zero is permitted) to make \(|\Delta|\) small
compared with \(xe^{-\delta\sqrt{\log x}}\) once \(\delta<c_0\), and this is
in fact what happens at that extremal size (I checked it: with
\(\varepsilon=c_0/\sqrt{\log x}\) fixed and \(\delta<c_0\), the ratio
\(|\Delta|/(xe^{-\delta\sqrt{\log x}})\to0\)). The remark's force is that
Siegel's theorem gives no *effective lower bound* on how close to \(1\) an
exceptional \(\beta\) can be: \(1-\beta\) can be far smaller than
\(c_0/\sqrt{\log x}\), e.g. \(1-\beta=\mu/\log x\) for fixed \(\mu\), which
is certainly "small compared with \(\delta\)" (it is \(o(1/\sqrt{\log x})\)).
In that regime, with \(L=\log(x/y)\) also held fixed (also small compared
with \(\delta\sqrt{\log x}\), since it doesn't grow with \(x\) at all), I
computed \(|\Delta|/(xe^{-\delta\sqrt{\log x}})\) directly (\(\delta=0.5\),
\(\mu=1\), \(L=3\), no approximation):

| \(\log x\) | \(1-\beta\) | \(\Delta\) | \(xe^{-\delta\sqrt{\log x}}\) | ratio |
| --- | --- | --- | --- | --- |
| 100 | \(10^{-2}\) | \(1.51\times10^{40}\) | \(1.81\times10^{41}\) | 0.084 |
| 1000 | \(10^{-3}\) | \(1.09\times10^{430}\) | \(2.68\times10^{427}\) | 405 |
| \(10^4\) | \(10^{-4}\) | \(4.84\times10^{4337}\) | \(1.70\times10^{4321}\) | \(2.8\times10^{16}\) |
| \(10^5\) | \(10^{-5}\) | \(1.54\times10^{43423}\) | \(6.03\times10^{43360}\) | \(2.6\times10^{62}\) |
| \(10^6\) | \(10^{-6}\) | \(1.67\times10^{434287}\) | \(2.16\times10^{434077}\) | \(7.7\times10^{209}\) |
| \(10^7\) | \(10^{-7}\) | \(3.62\times10^{4342936}\) | \(1.38\times10^{4342258}\) | \(2.6\times10^{678}\) |

The ratio diverges: \(\Delta\) decays only polynomially in \(\log x\)
(like \(1/\log x\) here) once \(1-\beta\) is taken this small, while the
claimed error term decays exponentially in \(\sqrt{\log x}\), so the ratio
grows like \(e^{\delta\sqrt{\log x}}/\log x\to\infty\). This confirms the
remark exactly: the printed uniformity in \(y\le x\) with \(\eta_{x,a}\)
frozen at \(x\) genuinely fails to be \(O(xe^{-\delta\sqrt{\log x}})\) in
this corner of the parameter space, so the remark is not an overcautious
reading, it identifies a real gap between the literal text and what a
uniform-in-\(y\) statement would need.

**(c) The document does not rely on the questioned uniformity: confirmed.**
Section 4 states explicitly "the lemma is applied here with \(x:=y\) for
each prefix \(y\) separately" (line 332), never invoking the lemma at a
fixed \(x\) with \(y<x\) varying; the "Matching the exceptional data"
paragraph is built entirely to handle the resulting \(y\)-dependence of the
exceptional datum, and section 7 item (5) repeats "section 4 applies the
lemma at \(x=y\) and does not use that uniformity." I searched section 4
end to end for any use of a fixed exceptional datum across a range of
\(y\) and found none: every occurrence of \(\tilde\chi_y,\tilde q_y,
\tilde\beta_y\) or \(\chi,\beta\) is either the definition of the
\(y\)-exceptional data (varying with \(y\)) or the TT-exceptional data
fixed at \(Z\) (which is a different, and correctly distinguished, object).
Confirmed.

## Item 3: matching the exceptional data

**Verdict: confirmed.** I checked the four bullets against the definitions
in section 1 and (DF), looking specifically for a missed case and for the
three-way threshold confusion the task asked about
(\(b/(2\sqrt{\log y})\) vs. \(b/\sqrt{\log y}\) vs. \(c/\sqrt{\log N}\)).

- **Bullet 1** (\(\chi\) exists, \(q\mid r\)). The chain
  \(q\le r\le R\le e^{\sqrt{\log y}}\) needs \(R\le e^{\sqrt{\log y}}\),
  i.e. \(\sigma\sqrt\ell\le\sqrt{\ell/2}\), i.e. \(\sigma\le1/\sqrt2\); the
  document's \(\sigma\le1/20\) satisfies this with room to spare. The
  threshold chain \(\beta>1-c_0/\sqrt\ell\ge1-b/(2\sqrt{\log y})\) reduces,
  after clearing denominators, to \(\sqrt{\log y}\le(b/2c_0)\sqrt\ell\);
  since \(\log y\le\ell\) always and \((Cmp)\) gives \(c_0\le b/2\) (so
  \(b/2c_0\ge1\)), this holds unconditionally, not just in the
  \(\log y\ge\ell/2\) regime. \(\beta\) then lies in DF's Theorem 1.2
  region at \(Q=T=e^{\sqrt{\log y}}\) by definition, so by uniqueness
  \(\chi\) *is* the \(y\)-exceptional character. No step here confuses the
  factor of \(2\): the document keeps DF's own \(b/(2\sqrt{\log y})\)
  (from \(\log(QT)=2\sqrt{\log y}\) at \(Q=T=e^{\sqrt{\log y}}\)) distinct
  from this document's own \(c_0/\sqrt\ell\) (no factor of \(2\), since
  \(Z\) itself, not \(Z^2\), is the conductor bound), and (Cmp) is exactly
  the bridge that makes the comparison valid.
- **Bullet 2** (\(y\)-exceptional \(\tilde\chi_y\) with \(\tilde q_y\mid r\),
  not TT-exceptional). Since \(c_0\le c\) (from (Cmp)) makes TT-exceptional
  a subset of Page-exceptional at the same conductor bound \(Z\), any
  character meeting the TT threshold would already be forced, by (Pg)'s
  uniqueness, to be the (unique) TT-exceptional character; so failing to be
  TT-exceptional while having conductor \(\tilde q_y\le r<Z\) forces
  \(\tilde\beta_y\le1-c_0/\sqrt\ell\) exactly as claimed, and
  \(y^{\tilde\beta_y-1}\le\exp(-c_0\sqrt\ell/2)\) follows from
  \(\log y\ge\ell/2\). The bound \(2ye^{-c_0\sqrt\ell/2}/\phi(r)\ll
  Ne^{-c_0\sqrt\ell/2}\) is correct (\(1/\tilde\beta_y<2\) for large \(N\),
  \(1/\phi(r)\le1\)).
- **Bullet 3** (\(\chi\) exists, \(q\nmid r\)). The dichotomy
  \(\tilde\chi_y=\chi\Rightarrow1_{\tilde q_y\mid r}=0\), else
  \(\tilde\chi_y\ne\chi\Rightarrow\tilde\chi_y\) is not TT-exceptional (by
  uniqueness of the TT-exceptional character, which is \(\chi\)), reducing
  to bullet 2. This is exhaustive and correct.
- **Bullet 4** (no TT-exceptional character at \(Z\)). Any \(y\)-exceptional
  \(\tilde\chi_y\) with \(\tilde q_y\mid r\) is trivially "not
  TT-exceptional" (there is none to be), so bullet 2 applies verbatim.

**Case search.** I looked for a case not covered by the four bullets: the
only way the indicator \(1_{\tilde q_y\mid r}\) in (D\('\)) can be nonzero
is if some \(y\)-exceptional character (there is at most one, globally,
by (Pg)/(DF)'s own uniqueness) has \(\tilde q_y\mid r\); bullets 1-2 exhaust
this by whether that character equals the TT-exceptional \(\chi\) or not,
and bullet 3 covers \(1_{\tilde q_y\mid r}=0\) directly when \(\chi\) is
the one that fails to divide \(r\). No fifth case (e.g. two distinct
\(y\)-exceptional characters both dividing \(r\)) exists, since DF's Lemma
2.2 posits a single \(x\)-exceptional character for the whole modulus
range \(q\le Q\), not one per \(q\). I found no confusion between
\(b/(2\sqrt{\log y})\), \(b/\sqrt{\log y}\), or \(c/\sqrt\ell\) anywhere in
the four bullets; each threshold is used with its own constant and its own
factor of \(2\) exactly where DF's or this document's own definition
places it. (Dsecond)'s constant \(c_4=\min(c_0/2,\delta/\sqrt2)\) is the
correct combination of bullet 2's exponent (\(c_0\sqrt\ell/2\), giving
\(c_0/2\)) and the (DF) Bombieri-Vinogradov exponent
(\(\delta\sqrt{\log y}\ge\delta\sqrt{\ell/2}=\delta\sqrt\ell/\sqrt2\),
giving \(\delta/\sqrt2\)).

## Item 4: the Small \(y\) reduction

**Verdict: confirmed**, both the trivial small-\(y\) bound and all four
inequalities that follow from \(\log y\ge\ell/2\).

- \(y\le N\exp(-\gamma\sqrt\ell)\Rightarrow\) both sides of (1\('\)) are
  \(O(y\ell)\): routine (\(\Lambda(n)\le\log N=\ell\), \(|a(n)|\ll b\ll
  \sqrt\ell\le\ell\) pointwise), and \(y\ell\le N\ell\exp(-\gamma\sqrt\ell)
  =N\exp(-\gamma\sqrt\ell(1-o(1)))\), absorbed into the same exponential
  rate at a slightly smaller constant, standard in this document's style.
- \(e^{\sqrt{\log y}}\ge R\): reduces to \(\sigma\le1/\sqrt2\); holds since
  \(\sigma\le1/20\).
- \(e^{\sqrt{\log y}}\le Z\): immediate from \(\log y\le\ell\) (as \(y\le N\)).
- \(b/(2\sqrt{\log y})\ge c_0/\sqrt\ell\): shown above under item 3, and it
  in fact needs only \(\log y\le\ell\), not \(\log y\ge\ell/2\).
- \(ye^{-\delta\sqrt{\log y}}\le Ne^{-\delta\sqrt\ell/\sqrt2}\): from
  \(y\le N\) and \(\sqrt{\log y}\ge\sqrt{\ell/2}=\sqrt\ell/\sqrt2\) (this
  step *does* need \(\log y\ge\ell/2\)).
- \(R\sqrt y(\log y)^{O(1)}\le Ne^{-\sqrt\ell}\) for large \(N\): I checked
  this directly at concrete scale rather than only asymptotically. At
  \(\log y=\ell/2\), \(\sigma=0.05\):

  | \(\log N\) | \(R\) | \(R\sqrt y(\log y)^3\) | \(Ne^{-\sqrt\ell}\) | holds? |
  | --- | --- | --- | --- | --- |
  | 1000 | 4 | \(1.87\times10^{117}\) | \(3.64\times10^{420}\) | yes |
  | \(10^4\) | 148 | \(1.01\times10^{1099}\) | \(3.28\times10^{4299}\) | yes |
  | \(10^5\) | \(7.36\times10^6\) | \(2.12\times10^{10878}\) | \(1.29\times10^{43292}\) | yes |

  and the exponents' asymptotic comparison confirms it holds for every
  large \(N\): the left side has \(\log(R\sqrt y(\log y)^{O(1)})=
  \sigma\sqrt\ell+\ell/2+O(\log\log\ell)\), the right side has
  \(\ell-\sqrt\ell\), and \(\ell/2+\sigma\sqrt\ell\ll\ell-\sqrt\ell\)
  since \(\ell/2\) is the dominant, strictly smaller, linear term.

Every inequality in the Small \(y\) paragraph is confirmed, and I found no
inequality there that silently needed a stronger hypothesis than
\(\log y\ge\ell/2\) (the two that don't need the lower half at all,
\(e^{\sqrt{\log y}}\le Z\) and the \(b/(2\sqrt{\log y})\) chain, only use
\(\log y\le\ell\), which is unconditional).

## Summary

| Item | Verdict |
| --- | --- |
| 1. The level \(D_1\) (diagnosis and repair) | Confirmed |
| 2(a). Derivation of (D\('\)) | Confirmed |
| 2(b). The frozen-at-\(x\) remark | Confirmed (the uniformity genuinely fails in the stated regime) |
| 2(c). The document does not rely on it | Confirmed |
| 3. Matching the exceptional data, four bullets | Confirmed, no missed case, no threshold confusion found |
| 4. The Small \(y\) reduction | Confirmed |

No defect was found in either of the third revision's two substitutions.
Everything reachable with the tools available in this attempt (recomputing
every displayed error term of section 4 at level \(D_1\), rederiving the
final admissible range for \(\gamma\), and independently testing the (DF)
frozen-at-\(x\) remark's own numerical claim) checks out against the text.
The one item this attempt could not settle on its own is the word-for-word
comparison of the (DF) quotation against arXiv:2003.02201v1, since this
attempt's tool set has no network access; that comparison is recorded as
already done in the orchestrator session, and settling it independently
would need an attempt with web access repeating that fetch and diff.
