# The error in the presence of a dominant real zero: an asymptotic, and the binding chain reconstructed

2026-09-12. Base: `SHARP_EXPONENT.md` (commit 3b0fc2e, the two-sided statement
(S\('''\)) and its budget (7)), `MAJOR_ARC_EXPLICIT.md` (its sections 2, 3 and 5,
the lemma (5), the case analysis of section 3 and the Proposition), `ARC_SPLIT_BUDGET.md`
(the arcs, (1), (3), (4), (8), (9), (11) and 4.1), `SIEGEL_UNIFORMITY.md` (18), (19),
(23), `ENDPOINT_SHARP.md` sections 1, 4 and 5, `UPPER_BOUND.md` (2), (4), (7). Assignment
(a takeover of the campaign, 2026-09-12): take the fixed target from its actual latest
state, reconstruct the estimate that binds and every input it depends on, and advance
the strongest route that the complete current budget justifies, without changing the
target, its \(Z\), its threshold \(c_0\), its correction, or its endpoints.

**Result, stated first.** Section 1 is the reconstruction. Section 2 proves one
statement that the chain already contains but never stated: when a real zero of a real
character of small odd conductor sits at \(1-\kappa/\sqrt\ell\) and is the dominant real
zero at scale \(Z\), the original CHHL error is asymptotically the energy of that zero's
own correction,
\[
 \boxed{\ E(N)=\widetilde{\mathcal A}(N)\,(1+o(1)),\qquad
 \widetilde{\mathcal A}(N):=2\sum_{h=1}^N C_{\tilde q,\tilde\beta,Z}(h)^2,\ }
\tag{T}
\]
under the hypotheses (U) and (W) of section 2, with \(\widetilde{\mathcal A}\) evaluated
in section 3 to an explicit constant:
\[
 \widetilde{\mathcal A}(N)=\frac{2\,\mathfrak M_2(\tilde q;Z)}{\tilde\beta^{2}}
 \Big(\frac{\tilde q}{\phi(\tilde q)}\Big)^{3}\frac{N^{2\tilde\beta+1}}{\tilde q^{2}}\,
 \mathcal J_{\pm}(\tilde\beta)\,(1+o(1))
 +2\,\mathfrak M_2(\tilde q;Z)\frac{\tilde q^{2}}{\phi(\tilde q)^{3}}N^{4\tilde\beta-1}\mathcal J_{12}(\tilde\beta)\,(1+o(1)),
\tag{A}
\]
\(\mathcal J_+(\beta)\to4/3\) for even \(\tilde\chi\), \(\mathcal J_-(\beta)\sim(15-\pi^2)\delta^2/18\)
for odd \(\tilde\chi\) (\(\delta=1-\tilde\beta\)), \(\mathcal J_{12}(\beta)\to1/3\), and
\(\mathfrak M_2(\tilde q;Z)=2\prod_{2<p<Z,\ p\nmid\tilde q}(1+(p-1)^{-3})\), which tends to
\(C_3/\prod_{p\mid\tilde q}(1+(p-1)^{-3})\) with \(C_3=\prod_p(1+(p-1)^{-3})=2.30096\ldots\)
The two-sided statement of `SHARP_EXPONENT.md`, which left \(\ell^{O(1)}\tilde q^{\,2}\)
between its bounds, is therefore an asymptotic equality. For the fixed target the same
argument gives, in the case where the TT-exceptional character exists with conductor
at most \(e^{\sigma\sqrt\ell}\), the bound \(E_{\rm corr}^{(Z)}\ll N^3e^{-c''\sqrt\ell}\)
for every \(c''<\lambda_0=\min(1/6,\sqrt c/2,\sqrt b/2)\), which is at least \(2c_0\)
under (H\(''\)) (Corollary 2.3): the binding term of (S\('''\)) is present exactly when
the target's correction is inactive on the major arcs.

Grade: derived, one route, finite checks in section 6, a corollary of the existing chain
with no new arithmetic input (section 4 says exactly what is used). Conditional on a zero
that may not exist; nothing about the zeros of \(\zeta\); no power saving; the fixed
target's exponent constant \(2c_0\) is unchanged. The novelty of (T) was not searched;
what is claimed is that this hunt produced it. **Not independently read.** One reader,
the author. A fresh-context check was started twice on 2026-09-12 and did not report
(the first run failed on an output limit before writing anything, the second had not
written a file when this was committed). The places a defect would most likely hide are
step (a) of the proof of Theorem 2.1, whether every input of the chain really holds with
the model's datum below or above the threshold, and the matching in (2); the numerics of
section 3 are the least likely, being measured.

## 1. The binding estimate and its dependencies, reconstructed

The fixed target is \(E_{\rm corr}^{(Z)}(N)=2\sum_{h\le N}|r(h)-C_N(h)|^2\) with
\(r(h)=\psi_2(N,h)-(N-h)\mathfrak S(h)\), \(Z=e^{\sqrt\ell}\), \(\ell=\log N\), and
\(C_N=C_{q_e,\beta_e,Z}\) of `SIEGEL_UNIFORMITY.md` (19) when the TT-exceptional data
\((\chi_e,q_e,\beta_e)\) exist at \(Z\) (primitive real \(\chi_e\), \(q_e<Z\),
\(\beta_e>1-c_0/\sqrt\ell\), TT Definition 2.1 with its threshold \(c_0\)), and
\(C_N=0\) otherwise. The strongest complete bound is (S\('''\)):
\(E_{\rm corr}^{(Z)}\ll N^3e^{-c''\sqrt\ell}\) for every fixed \(c''<2c_0\), under
(H\(''\)): \(c_0\le\min(1/12,\sqrt c/4,\sqrt b/4,c_P)\). It is assembled as follows;
every line names the document and the input it consumes.

| step | statement | consumes |
| --- | --- | --- |
| reduction to the circle | \(\big|\sqrt{E_{\rm corr}^{(Z)}}-\|G_{\rm corr}\|_2\big|\le\sqrt{D_{\rm tail}}\ll N\) | `UPPER_BOUND.md` (2), (4), (6): GHN Theorem 2 for the tail |
| arcs | \(R=\lfloor e^{\sigma\sqrt\ell}\rfloor\), \(I_{r,a}\) of radius \(R/(rN)\), \(\mathfrak M\), \(\mathfrak m\) | `UPPER_BOUND.md` (7), `ARC_SPLIT_BUDGET.md` section 2 |
| major arcs, split | \(\int_{\mathfrak M}|G_{\rm corr}|^2\le3\int_{\mathfrak M}(|F|^2-|H|^2)^2+3\|R_{\rm mod}\|^2+3\kappa_0^2|\mathfrak M|\) | `ARC_SPLIT_BUDGET.md` (3), section 3 |
| model remainder | \(\|R_{\rm mod}\|^2\ll N^3e^{-2c_m\sqrt\ell}+N^2\), \(c_m=1/4-o(1)\) | `SIEGEL_UNIFORMITY.md` (18) at this \(Z\) (TT Lemma 5.1 at level \(N^{1/4}\), the local identities (17)), `ENDPOINT_SHARP.md` section 5 |
| intensity difference | \(\int_{\mathfrak M}(|F|^2-|H|^2)^2\ll\sup_{\mathfrak M}|W|^2\cdot N\ell\) except for the one term integrated per arc | `MAJOR_ARC_EXPLICIT.md` section 4; `SHARP_EXPONENT.md` section 2 |
| \(\sup|W|\) on an arc | (5) of `MAJOR_ARC_EXPLICIT.md`: \(\sqrt r\,N\Upsilon(r)+1_{\tilde q\mid r}\sqrt r\,Ne^{-c_0\sqrt\ell}+R^{3/2}Ne^{-\sqrt\ell/3}\) | (EF) Davenport 17, 19; (ZF) Davenport 14; the zero count, Davenport 16; (GS) Montgomery-Vaughan 9.10; (Pg\('\)) Page's theorem in Drappeau-Fiorilli's Theorem 1.2 form; (Md) the four sieve cases of `ENDPOINT_SHARP.md` section 4 at level \(D_1=N^{1/2}\) (the fundamental lemma, TT Lemma 5.1 / Friedlander-Iwaniec 6.3, and the coset cancellation); the term of `SHARP_EXPONENT.md` 2.1 |
| the Page term, per arc | \(\int_{I_{r,a}}|K_N|^2|I_{\tilde\beta}|^2\ll N^{2\tilde\beta+1}\), no factor \(R\) | `SHARP_EXPONENT.md` (6) and section 2, first bullet |
| minor arcs | \(\int_{\mathfrak m}|G_{\rm corr}|^2\ll N^3\ell^{O(1)}R^{-1}+N^{13/5}\ell^6+N^2\ell^2\) | `ARC_SPLIT_BUDGET.md` (9)-(11): Vaughan's bound (V) through `UPPER_BOUND.md` (20), leakage (13), truncation (9), and 4.1 for the correction polynomial (the large sieve, `SIEGEL_UNIFORMITY.md` (17)) |
| budget | (7) of `SHARP_EXPONENT.md`, \(\sigma=2c_0\), (H\(''\)) | arithmetic |

Three things about this chain that the takeover confirms rather than changes.

1. **The Λ side of the major arcs is the explicit formula, not the progression theorem.**
   `ENDPOINT_SHARP.md`'s input (1\('\)), and with it (DF), the Drappeau-Fiorilli lemma
   whose quotation was checked twice, is no longer consumed by the binding chain: the
   explicit formula (EF) with the zero-free region at the arc's own modulus and height
   replaced it in `MAJOR_ARC_EXPLICIT.md`. What `ENDPOINT_SHARP.md` section 4 still
   supplies is (Md), the model side, whose only source input is the fundamental lemma.
2. **What binds is the Page-allowed zero the target does not subtract**, and only in
   the case where such a zero exists for a character other than \(\chi_e\). The case
   analysis of `MAJOR_ARC_EXPLICIT.md` section 3 has three cases; the middle one is the
   binding term, and it is absent when the TT-exceptional character is itself the
   Page-exceptional character at \((R,R^3)\). Corollary 2.3 below reads that off.
3. **The constant \(c_0\) is the target's, and unpinned.** `S8_CONTROL.md` recorded that
   TT never pins it to a number; (H\(''\)) is the list of what it must satisfy for the
   exponent to be \(2c_0\), and every constant in that list is soft except the shape:
   the \(1/12\) comes from bounding the model error \(E_{\rm md}\ll Ne^{-\sqrt\ell/3}\)
   where the sieve at level \(N^{1/2}\) gives \(e^{-(1/2-o(1))\sqrt\ell}\) (which would
   make it \(1/8\)), and a level \(N^{\theta}\) would make it \(\theta/4\). None of this
   moves the exponent of the fixed target, which is why it is recorded and not pursued.

Review status of the chain, as inherited: `ARC_SPLIT_BUDGET.md` sections 3 to 5 read by
`a-0078`, with two order-level steps in 4.1 named and not binding; `MAJOR_ARC_EXPLICIT.md`
sections 2 to 5 read by `a-0080` (one defect, corrected; its endorsement of a wrong
bullet later caught by `a-0082`), the odd-character remark of section 5 unread until
section 5 below; `SHARP_EXPONENT.md` sections 1 to 3 read by `a-0082` (one non-binding
defect, corrected in two documents); the endpoint checkpoint reviewed three times, its
(DF) quotation passed against the published lemma by a scoped outside check, and (DF)
now outside the binding chain. Unread against a primary source inside this hunt: the
fundamental lemma as Friedlander-Iwaniec Lemma 6.3 (consumed as TT Lemma 5.1).

## 2. The asymptotic

Notation as in `MAJOR_ARC_EXPLICIT.md`: \(c\) the constant of (ZF), \(b\) the constant of
(Pg\('\)) (Page at \((Q,T)\): at most one zero of \(\prod_{q\le Q}\prod_\chi L(s,\chi)\)
in \(\mathrm{Re}\,s>1-b/\log(QT)\), \(|\mathrm{Im}\,s|\le T\), and it is real and belongs to
a unique primitive real character), \(c_m=1/4-o(1)\). The letter \(\kappa\) is the
zero's distance parameter as in that document's section 5, not the exponent parameter
of `ENDPOINT_HALF.md`.

Let \(\tilde\chi\) be a primitive real character of odd conductor \(\tilde q\), with a real
zero \(\tilde\beta=1-\kappa/\sqrt\ell\) of \(L(s,\tilde\chi)\), \(0<\kappa\). Put
\(\tilde C(h):=C_{\tilde q,\tilde\beta,Z}(h)\), the correction of `SIEGEL_UNIFORMITY.md`
(19) evaluated at these data, and \(\widetilde{\mathcal A}(N)=2\sum_{h\le N}\tilde C(h)^2\).

(U) *Dominance.* Either \(\kappa<c_0\), in which case \(\tilde\chi\) is the TT-exceptional
character at \(Z\) (unique by (Pg) at \(Q=Z\), `ENDPOINT_SHARP.md` section 4, since
\(c_0\le c\)); or \(\kappa\ge c_0\) and no TT-exceptional character exists at \(Z\).
Equivalently: no primitive real character of conductor below \(Z\) other than
\(\tilde\chi\) has a real zero above \(1-c_0/\sqrt\ell\). When \(\kappa<c\) this is
automatic, because \(\tilde\beta\) then lies in Page's region at \(Q=Z\) and is the one
zero there.

(W) *Window.* \(\tilde q\le e^{\varepsilon\sqrt\ell}\), and with \(\sigma:=2\kappa+3\varepsilon\),
\[
 \frac{c}{2\sigma}-\sigma>2\kappa+2\varepsilon,\qquad
 \frac{b}{2\sigma}-\sigma>2\kappa+2\varepsilon,\qquad
 \frac23-3\sigma>2\kappa+2\varepsilon,\qquad
 \sigma\le\frac1{\sqrt2}.
\tag{W}
\]
For every fixed \(\kappa_1<\min(1/12,\sqrt c/4,\sqrt b/4)\) there is \(\varepsilon_0(\kappa_1)>0\)
such that (W) holds for all \(\kappa\le\kappa_1\) and \(\varepsilon\le\varepsilon_0\): at
\(\varepsilon=0\) the three inequalities read \(16\kappa^2<c\), \(16\kappa^2<b\),
\(8\kappa<2/3\). This is (H\(''\)) with \(\kappa\) in place of \(c_0\) and (U) in place of
\(c_P\). (W) also implies \(2\kappa+2\varepsilon<2c_m\), \(\varepsilon\le\sigma\) (so
\(\tilde q\le R\)), and the Page matching \(\kappa<b/(4\sigma)\) (from the second
inequality, \(b>2\sigma(2\kappa+2\varepsilon+\sigma)>4\sigma\kappa\)).

**Theorem 2.1.** Under (U) and (W), for all sufficiently large \(N\),
\[
 E(N)=\widetilde{\mathcal A}(N)\Big(1+O\big(\ell^{O(1)}\kappa^{-1}e^{-\eta\sqrt\ell}\big)\Big),
 \qquad\eta=\tfrac12\big(\lambda(\sigma)-2\kappa-2\varepsilon\big)>0,
\tag{T}
\]
where \(\lambda(\sigma)=\min(\sigma,\ c/(2\sigma)-\sigma,\ b/(2\sigma)-\sigma,\ 3\sigma,\ 2/3-3\sigma)\),
the implied constants absolute. Moreover \(E_{\rm corr}^{(Z)}(N)=E(N)\) when \(\kappa\ge c_0\),
and \(E_{\rm corr}^{(Z)}(N)=2\sum_h|r(h)-\tilde C(h)|^2=O(\ell^{O(1)}\kappa^{-2}e^{-2\eta\sqrt\ell})\,\widetilde{\mathcal A}(N)\)
when \(\kappa<c_0\).

*Proof.* Two facts and a triangle inequality.

**(a) The residual after subtracting \(\tilde C\).** Let \(a'(n)=\nu(n)(1-n^{\tilde\beta-1}\tilde\chi(n))\),
the model of `ENDPOINT_SHARP.md` section 1 with \((\tilde\chi,\tilde q,\tilde\beta)\) as
its exceptional data, \(H'=\sum_{n\le N}a'(n)e(n\alpha)\), \(W'=F-H'\), and
\(\widetilde G:=G_y-\widehat{\tilde C}\) with \(\widehat{\tilde C}(\alpha)=2\sum_{h\le N}\tilde C(h)\cos(2\pi h\alpha)\).
By `UPPER_BOUND.md` (2), (4) the coefficient of \(\widetilde G\) at \(h\ge1\) is
\(\psi_2(N,h)-(N-h)\mathfrak S_y(h)-\tilde C(h)\), so
\[
 \Big|\Big(2\sum_{h\le N}|r(h)-\tilde C(h)|^2\Big)^{1/2}-\|\widetilde G\|_2\Big|\le\sqrt{D_{\rm tail}(N,y)}\ll N .
\tag{1}
\]
Now run `ARC_SPLIT_BUDGET.md` sections 3 and 4 and `MAJOR_ARC_EXPLICIT.md` sections 2 to 4
on \(\widetilde G\) with \(a'\) as the model and \(\tilde C\) as the correction. Every input
holds verbatim for these data, because none of them uses where \(\tilde\beta\) sits
relative to the threshold \(c_0\):

- (In2) for \(\tilde C\): `SIEGEL_UNIFORMITY.md` (18) needs \(\tilde q<Z\) and
  \(\tilde\beta\ge3/4\) and the fundamental lemma at level \(N^{1/4}\); it gives
  \(\psi_2^{a'}(N,h)-(N-h)\mathfrak S(h)=\tilde C(h)+O(Ne^{-c_m\sqrt\ell})\) uniformly in
  \(h\), hence \(\|R'_{\rm mod}\|_2^2\ll N^3e^{-2c_m\sqrt\ell}+N^2\) as in
  `ARC_SPLIT_BUDGET.md` (7).
- (Md) for \(a'\): the four cases of `ENDPOINT_SHARP.md` section 4 need only that every
  prime factor of \(\tilde q\) is below \(Z\) (true, \(\tilde q\le R<Z\)), the sieve at
  level \(D_1\), and, when \(\tilde q\nmid r\), the coset cancellation; so
  \(H'_\chi(\theta)=\delta_\chi K_N(\theta)-1_{\tilde q\mid r}1_{\chi=\tilde\chi_r}I_{\tilde\beta}(\theta)+O(rE_{\rm md}(1+R/r))\)
  for every \(\chi\bmod r\), \(r\le R\).
- The Λ side, `MAJOR_ARC_EXPLICIT.md` (3): unchanged, it is the explicit formula.
- The matching of section 3 there. Page at \((R,R^3)\) allows one zero in
  \(\mathrm{Re}\,s>1-b/(4\sigma\sqrt\ell)\); by (W), \(\tilde\beta\) is in that region, so
  \(\tilde\chi\) is the Page-exceptional character at \((R,R^3)\). For \(\chi\bmod r\)
  induced by \(\tilde\chi\) (that is, \(\tilde q\mid r\)), \(F_\chi\) carries
  \(-I_{\tilde\beta}\) (the exceptional real zero of \(L(s,\chi)=L(s,\tilde\chi)\times\)
  Euler factors, which is \(\tilde\beta\) and is (ZF)-exceptional for \(\tilde\chi\) since
  \(\kappa\log(2\tilde q)<c\sqrt\ell\)) and \(H'_\chi\) carries \(-I_{\tilde\beta}\): they
  cancel. For every other real \(\chi\bmod r\) with a (ZF)-exceptional real zero
  \(\beta_\chi\), that zero is not the Page zero, so \(\beta_\chi\le1-b/(4\sigma\sqrt\ell)\)
  and it is the term of `SHARP_EXPONENT.md` 2.1. Every remaining zero is covered by (3).
  Under (U), no character other than \(\tilde\chi\) has a zero above the TT threshold, so
  the model side has no second twist to account for. Therefore
  \[
   \sup_{\alpha\in I_{r,a}}|W'(\alpha)|\ll\sqrt r\,N\Upsilon(r)+R^{3/2}Ne^{-\sqrt\ell/3},
  \tag{2}
  \]
  which is (5) of `MAJOR_ARC_EXPLICIT.md` **without its middle term**: the term that
  bound (S\('''\)) is the zero that \(\tilde C\) now subtracts.
- Major arcs: \(\int_{\mathfrak M}(|F|^2-|H'|^2)^2\le\sup_{\mathfrak M}|W'|^2\int_{\mathbb T}(|F|+|H'|)^2\ll\sup_{\mathfrak M}|W'|^2\cdot N\ell\),
  since \(\int|H'|^2=\sum a'(n)^2\le4b^2\sum_{n\le N}1_{(n,P)=1}\ll N\sqrt\ell\). No term
  needs the per-arc integration of `SHARP_EXPONENT.md` section 2, because no term of
  (2) is the Page zero.
- Minor arcs: `ARC_SPLIT_BUDGET.md` (9) with \(\widehat{\tilde C}\) in place of
  \(\widehat C_N\); its 4.1 needs \(\tilde q<Z\), \(\tilde q\) odd for the linear pieces,
  and \(0<\tilde\beta<1\) for the monotonicity of the weights; so (11) holds.

Squaring (2) with \(\sqrt r\cdot\sqrt{R/r}=\sqrt R\) and \(\sqrt r\le\sqrt R\) (the
corrected form of `MAJOR_ARC_EXPLICIT.md` (6)), and collecting,
\[
 2\sum_{h\le N}|r(h)-\tilde C(h)|^2\ll N^3\ell^{O(1)}\Big[R^{-1}+Re^{-(c/(2\sigma))\sqrt\ell(1+o(1))}
 +Re^{-(b/(2\sigma))\sqrt\ell}+R^{-3}+R^3e^{-2\sqrt\ell/3}\Big]
 +N^3e^{-2c_m\sqrt\ell}+N^{13/5}\ell^6+N^2\ell^2
 \ll N^3\ell^{O(1)}e^{-\lambda(\sigma)\sqrt\ell},
\tag{3}
\]
the last step by (W) (\(2c_m>2\kappa+2\varepsilon\) and \(2/5>\lambda(\sigma)\) are
both implied). The constraints \(2R^2<N\) and \(R\le e^{\sqrt{\ell/2}}\) of the arcs and
of `ENDPOINT_SHARP.md` section 4 hold by \(\sigma\le1/\sqrt2\).

**(b) The size of \(\widetilde{\mathcal A}\).** By section 3 below, for odd \(\tilde q\),
\[
 \widetilde{\mathcal A}(N)\ \ge\ c_2\,\frac{N^{2\tilde\beta+1}}{\tilde q^{\,2}}\cdot
 \begin{cases}1,&\tilde\chi(-1)=1,\\ \kappa^2/\ell,&\tilde\chi(-1)=-1,\end{cases}
 \qquad c_2>0\ \text{absolute},
\tag{4}
\]
and \(N^{2\tilde\beta+1}\tilde q^{-2}=N^3e^{-2\kappa\sqrt\ell}\tilde q^{-2}\ge N^3e^{-(2\kappa+2\varepsilon)\sqrt\ell}\).

**(c) The triangle inequality.** With \(\|x\|:=(2\sum_h|x(h)|^2)^{1/2}\),
\(\sqrt{E(N)}=\|r\|=\|\tilde C\|+O(\|r-\tilde C\|)\), and by (3), (4),
\(\|r-\tilde C\|^2/\|\tilde C\|^2\ll\ell^{O(1)}\kappa^{-2}e^{-(\lambda(\sigma)-2\kappa-2\varepsilon)\sqrt\ell}\),
which gives (T). When \(\kappa\ge c_0\), (U) says \(C_N=0\), so
\(E_{\rm corr}^{(Z)}=E\). When \(\kappa<c_0\), \(C_N=\tilde C\) and
\(E_{\rm corr}^{(Z)}=2\sum|r-\tilde C|^2\), which is (3). \(\square\)

**Remark 2.2 (even conductors).** For \(4\mid\tilde q\) or \(8\mid\tilde q\) the linear
pieces of \(\tilde C\) vanish and \(\widetilde{\mathcal A}\asymp N^{4\tilde\beta-1}\tilde q^{\,2}/\phi(\tilde q)^3\)
(section 3, (11)). The proof above goes through with (W) replaced by
\(\lambda(\sigma)>4\kappa+2\varepsilon\) at \(\sigma=4\kappa+3\varepsilon\), i.e. the window
\(\kappa<\min(1/24,\sqrt c/8,\sqrt b/8)\) up to \(\varepsilon\). The minor-arc lemma 4.1
of `ARC_SPLIT_BUDGET.md` has no linear pieces to bound in this case and the rest is
identical.

**Corollary 2.3 (the fixed target when its correction is active on the arcs).** Suppose
the TT-exceptional character \(\chi_e\) exists at \(Z\) with \(q_e\le e^{\sigma\sqrt\ell}\)
for some \(\sigma\le\min(b/(4c_0),1/\sqrt2)\). Then
\[
 E_{\rm corr}^{(Z)}(N)\ll N^3\ell^{O(1)}e^{-\lambda(\sigma)\sqrt\ell}+N^3e^{-2c_m\sqrt\ell}+N^{13/5}\ell^6,
\]
and in particular \(E_{\rm corr}^{(Z)}(N)\ll N^3e^{-c''\sqrt\ell}\) for every
\(c''<\lambda_0:=\min(1/6,\sqrt c/2,\sqrt b/2)\), attained at \(\sigma=\min(1/6,\sqrt c/2,\sqrt b/2)\),
provided \(q_e\le e^{\sigma\sqrt\ell}\) at that \(\sigma\). Under (H\(''\)),
\(\lambda_0\ge2c_0\), with equality only at the boundary of (H\(''\)).

*Proof.* This is step (a) with \(\tilde\chi=\chi_e\), for which (U) holds by definition:
\(\beta_e>1-c_0/\sqrt\ell\ge1-b/(4\sigma\sqrt\ell)\) puts \(\beta_e\) in Page's region at
\((R,R^3)\), so \(\chi_e\) is the Page-exceptional character there, the middle term of
`MAJOR_ARC_EXPLICIT.md` (5) is absent, and (3) holds with \(\kappa\) playing no role
(no lower bound on \(\widetilde{\mathcal A}\) is needed). \(\square\)

So (S\('''\))'s binding term \(e^{-2c_0\sqrt\ell}\) is a bound for the case in which the
target's correction is switched off on the major arcs (no TT-exceptional zero, or one of
conductor above \(R\)) while a real zero of some character of conductor at most \(R\)
sits just below the threshold. In the complementary case the fixed target is smaller by
the factor \(e^{-(\lambda_0-2c_0)\sqrt\ell}\). The two-sided statement of
`SHARP_EXPONENT.md` is unchanged as a statement about the worst case over the zeros.

## 3. The correction energy, evaluated

Write \(\delta=1-\tilde\beta\), \(u=h/N\), and, from `SIEGEL_UNIFORMITY.md` (15)-(19)
with \((q,\chi,\beta)=(\tilde q,\tilde\chi,\tilde\beta)\),
\[
 \tilde C(h)=\Big(\frac{\tilde q}{\phi(\tilde q)}\Big)^2S_*(h)\Big[-u_{\tilde q}(h)J_1(h)-v_{\tilde q}(h)J_2(h)+\frac{c_{\tilde q}(h)}{\tilde q}J_{12}(h)\Big],
 \qquad S_*(h)=\prod_{p<Z,\ p\nmid\tilde q}\alpha_p(h),
\]
\(u_{\tilde q}=\mu(\tilde q)\tilde\chi(-h)/\tilde q\), \(v_{\tilde q}=\mu(\tilde q)\tilde\chi(h)/\tilde q\)
for odd \(\tilde q\), both zero for even \(\tilde q\). Split
\(\tilde C=\tilde C_{\rm lin}+\tilde C_{\rm quad}\) along the bracket. For odd \(\tilde q\),
\(\tilde\chi(-h)=\tilde\chi(-1)\tilde\chi(h)\), so
\[
 \tilde C_{\rm lin}(h)=-\frac{\mu(\tilde q)\tilde\chi(h)}{\tilde q}\Big(\frac{\tilde q}{\phi(\tilde q)}\Big)^2S_*(h)\big(\tilde\chi(-1)J_1(h)+J_2(h)\big).
\tag{5}
\]

**The weights.** From (15)-(16) there, for \(1\le h\le N-1\),
\(J_1(h)=1+((N-h)^{\tilde\beta}-1)/\tilde\beta\), \(J_2(h)=(N^{\tilde\beta}-h^{\tilde\beta})/\tilde\beta\),
\(J_{12}(h)=\int_0^{N-h}\max(1,t)^{-\delta}(t+h)^{-\delta}dt\), so
\[
 \tilde\chi(-1)J_1+J_2=\frac{N^{\tilde\beta}}{\tilde\beta}\Big[\tilde\chi(-1)(1-u)^{\tilde\beta}+1-u^{\tilde\beta}\Big]+O(1),\qquad
 J_{12}=N^{2\tilde\beta-1}\int_0^{1-u}x^{-\delta}(x+u)^{-\delta}dx+O(1).
\tag{6}
\]
Define the one-variable integrals
\[
 \mathcal J_\pm(\beta)=\int_0^1\big[\pm(1-u)^\beta+1-u^\beta\big]^2du,\qquad
 \mathcal J_{12}(\beta)=\int_0^1\Big(\int_0^{1-u}x^{-\delta}(x+u)^{-\delta}dx\Big)^2du .
\tag{7}
\]
As \(\delta\to0\): \(\mathcal J_+\to4/3\); \(\mathcal J_{12}\to1/3\); and
\(-(1-u)^{1-\delta}+1-u^{1-\delta}=\delta\,[u\log u+(1-u)\log(1-u)]+O(\delta^2)\), so
\[
 \mathcal J_-(\beta)=\frac{15-\pi^2}{18}\,\delta^2\,(1+O(\delta)),
 \qquad\int_0^1\big[u\log u+(1-u)\log(1-u)\big]^2du=\frac{4}{27}+2\cdot\frac{37-3\pi^2}{108}=\frac{15-\pi^2}{18},
\tag{8}
\]
the cross integral by expanding \(\log(1-u)\) and summing \(\sum_k k^{-1}[(k+2)^{-2}-(k+3)^{-2}]\).
The convergence in \(\delta\) is slow where the integrand is singular: section 6 measures
\(\mathcal J_+/(4/3)=0.99\), \(0.95\) and \(3\mathcal J_{12}=1.49\), \(4.83\) at
\(\delta=0.099\), \(0.33\). This is why (A) is stated with the exact \(\mathcal J\)'s and
the limits are given separately.

**The mean square of \(S_*\).** \(\alpha_p(h)\) takes the value \(p/(p-1)\) if
\(p\mid h\) and \(p(p-2)/(p-1)^2\) otherwise for odd \(p\), and \(2\cdot1_{2\mid h}\) at
\(p=2\). Since \(\alpha_p(h)\) depends on \(h\) only through \(p\mid h\),
\(S_*(h)^2=\sum_{d\mid P_{\tilde q}}\lambda(d)1_{d\mid h}\) exactly, with
\(P_{\tilde q}=\prod_{p<Z,p\nmid\tilde q}p\) and \(\lambda(d)=\prod_{p\mid d}b_p\prod_{p\nmid d}a_p\),
\(a_p=\alpha_p(p\nmid h)^2\), \(b_p=\alpha_p(p\mid h)^2-a_p\). Hence for every
\(e\mid\tilde q\) and \(x\ge1\),
\[
 \sum_{\substack{h\le x\\ e\mid h}}S_*(h)^2=\frac xe\prod_{p<Z,\,p\nmid\tilde q}\Big(a_p+\frac{b_p}p\Big)+O\Big(\prod_{p<Z}(a_p+|b_p|)\Big)
 =\frac xe\,\mathfrak M_2(\tilde q;Z)+O(\ell^{O(1)}),
\tag{9}
\]
because \(a_p+b_p/p=E_p:=\frac1p\alpha_p(p\mid h)^2+(1-\frac1p)\alpha_p(p\nmid h)^2\),
which is \(2\) at \(p=2\) and, at odd \(p\),
\(p/(p-1)^2+p(p-2)^2/(p-1)^3=p(p^2-3p+3)/(p-1)^3=1+(p-1)^{-3}\); and
\(a_p+|b_p|=1+O(1/p)\) (with \(4\) at \(p=2\)) makes the error \(\ll(\log Z)^{O(1)}=\ell^{O(1)}\).
Möbius inversion over \(e\mid\tilde q\) gives, for \(h\) coprime to \(\tilde q\),
\[
 \sum_{\substack{h\le x\\(h,\tilde q)=1}}S_*(h)^2=\frac{\phi(\tilde q)}{\tilde q}\,\mathfrak M_2(\tilde q;Z)\,x+O(\tau(\tilde q)\ell^{O(1)}),
 \qquad
 \mathfrak M_2(\tilde q;Z)=\prod_{p<Z,\,p\nmid\tilde q}E_p=2\prod_{2<p<Z,\,p\nmid\tilde q}\Big(1+\frac1{(p-1)^3}\Big)
\tag{10}
\]
for odd \(\tilde q\) (for even \(\tilde q\) the factor \(2\) is absent). Likewise
\(\sum_{h\le x}S_*(h)^2c_{\tilde q}(h)^2=\mathfrak M_2(\tilde q;Z)\phi(\tilde q)\,x+O(\tilde q\,\ell^{O(1)})\),
since \(c_{\tilde q}(h)^2\) depends on \(h\bmod\tilde q\) with period mean \(\phi(\tilde q)\)
(`EXCEPTIONAL_ENERGY.md` (16)) and the divisibility conditions defining \(S_*\) are by
primes not dividing \(\tilde q\). The same argument at \(\tilde q=1\), \(Z\to\infty\)
gives the mean square of the Hardy-Littlewood singular series as
\(C_3=\prod_p(1+(p-1)^{-3})\), which section 6 measures at \(N=10^6\) to \(3\times10^{-5}\).

**Assembly.** Each squared weight has total variation on \([0,N]\) at most twice its
supremum: \(J_1+J_2\) and \(J_{12}\) are nonnegative and nonincreasing, and
\(J_2-J_1=(N^{\tilde\beta}/\tilde\beta)[1-u^{\tilde\beta}-(1-u)^{\tilde\beta}]+O(1)\) is
nonpositive up to \(O(1)\) (as \(x^{\tilde\beta}\ge x\) on \([0,1]\)), decreasing on
\([0,N/2]\) and increasing on \([N/2,N]\) (its derivative is \((N-h)^{\tilde\beta-1}-h^{\tilde\beta-1}\)),
so its square rises once and falls once. Partial summation of (10) against
\((\tilde\chi(-1)J_1+J_2)^2\), of total variation \(\ll N^{2\tilde\beta}\), and of the
\(c_{\tilde q}\)-weighted version against \(J_{12}^2\), of total variation
\(\ll N^{4\tilde\beta-2}\), with (6) and (7):
\[
 2\sum_h\tilde C_{\rm lin}(h)^2=\frac{2\,\mathfrak M_2(\tilde q;Z)}{\tilde\beta^2}\Big(\frac{\tilde q}{\phi(\tilde q)}\Big)^3\frac{N^{2\tilde\beta+1}}{\tilde q^{\,2}}\mathcal J_{\pm}(\tilde\beta)
 \Big(1+O\big(\tau(\tilde q)\ell^{O(1)}N^{-1}+N^{-\tilde\beta}\big)\Big),
\tag{11a}
\]
\[
 2\sum_h\tilde C_{\rm quad}(h)^2=2\,\mathfrak M_2(\tilde q;Z)\frac{\tilde q^{\,2}}{\phi(\tilde q)^3}N^{4\tilde\beta-1}\mathcal J_{12}(\tilde\beta)
 \Big(1+O\big(\tilde q\,\ell^{O(1)}N^{-1}+N^{1-2\tilde\beta}\big)\Big),
\tag{11b}
\]
and the cross term \(4\sum_h\tilde C_{\rm lin}\tilde C_{\rm quad}\) carries
\(\sum_h S_*(h)^2\tilde\chi(h)c_{\tilde q}(h)w(h)\) with a nonincreasing \(w\), whose
period sum \(\sum_{h\bmod\tilde q}\tilde\chi(h)c_{\tilde q}(h)=\tau(\tilde\chi)\sum_a^*\overline{\tilde\chi}(a)=0\)
makes it \(O(\tilde q^{O(1)}\ell^{O(1)}N^{3\tilde\beta-1})\), smaller than (11a) by
\(N^{\tilde\beta-1}\tilde q^{O(1)}=e^{-\kappa\sqrt\ell}\tilde q^{O(1)}\). Adding (11a) and
(11b) is (A); dropping the exact \(\mathcal J\)'s for their limits,
\[
 \widetilde{\mathcal A}(N)\sim\frac83\,\mathfrak M_2\Big(\frac{\tilde q}{\phi(\tilde q)}\Big)^3\frac{N^{2\tilde\beta+1}}{\tilde q^{\,2}}\ \ (\tilde\chi\ \text{even}),\qquad
 \widetilde{\mathcal A}(N)\sim\frac{15-\pi^2}{9}\,\mathfrak M_2\Big(\frac{\tilde q}{\phi(\tilde q)}\Big)^3\frac{\kappa^2}{\ell}\frac{N^{2\tilde\beta+1}}{\tilde q^{\,2}}\ \ (\tilde\chi\ \text{odd}),
\tag{12}
\]
in the regime where the quadratic piece is negligible, which is
\(e^{-2\kappa\sqrt\ell}\tilde q\ll1\) for even \(\tilde\chi\) and
\(e^{-2\kappa\sqrt\ell}\tilde q\,\ell/\kappa^2\ll1\) for odd \(\tilde\chi\) (the ratio of
(11b) to (11a) is \(\tfrac14\tilde q\,e^{-2\kappa\sqrt\ell}\) and
\(\tfrac{6}{15-\pi^2}\tilde q\,e^{-2\kappa\sqrt\ell}\ell/\kappa^2\) to leading order). At
the toy values of section 6 the odd-character quadratic piece is \(60\) to \(300\) times
the linear one, which is the finite-\(N\) face of \(e^{-2\kappa\sqrt\ell}\ell\) being near
its maximum \(\ell\asymp\kappa^{-2}\) there; (A) holds regardless. (4) follows from (11a)
with \(c_2\) from \(\mathcal J_\pm\) and \(\mathfrak M_2\ge1\).

## 4. What is new, what is used, and what changes in the complete budget

Execution rule of the assignment, answered explicitly. **New arithmetic information
used: none.** The inputs of (T) are the chain of section 1 with the model's exceptional
datum set to \((\tilde\chi,\tilde q,\tilde\beta)\), which every input allows because
each is stated for an arbitrary primitive real character of conductor below \(Z\) with a
real zero at least \(3/4\); plus the elementary evaluation (9)-(11). **What it does to
the strongest complete argument for the fixed target: nothing for the upper bound.**
(S\('''\)) and its constant \(2c_0\) stand. What changes is the reading of the ceiling:
the gap \(\ell^{O(1)}\tilde q^{\,2}\) between the two bounds of `SHARP_EXPONENT.md` is
closed to an asymptotic equality, and the binding term of (S\('''\)) is identified with
a case (Corollary 2.3), not with the target as such. **Every other contribution that
could still dominate** is in (3): the minor arcs \(R^{-1}\), the far zeros
\(c/(2\sigma)-\sigma\), the non-Page real zeros \(b/(2\sigma)-\sigma\), the model
\(2/3-3\sigma\) and \(2c_m\); (W) is exactly the statement that none of them does.

The lower bound of `MAJOR_ARC_EXPLICIT.md` section 5 is the case \(\kappa>c_0\) of (T)
without the constant; its odd-character remark, unread until now, is read in section 5.
`EXCEPTIONAL_ENERGY.md` (2) is the quadratic piece's lower bound \(\frac1{192}N^{4\beta-1}q^2/\phi(q)^3\);
(11b) gives its constant, \(\tfrac23\mathfrak M_2\,\mathcal J_{12}\to\tfrac29\mathfrak M_2\),
at least \(2/9\).

## 5. The odd-character remark of `MAJOR_ARC_EXPLICIT.md` section 5, read

The remark claims that for odd \(\tilde\chi\), on \(1/(16N)\le\theta\le1/(8N)\),
\(\operatorname{Im}(\overline{K_N}I_{\tilde\beta})\asymp(1-\tilde\beta)N^{1+\tilde\beta}\) with a
fixed sign, and concludes the lower bound with an extra \(\kappa^2/\ell\). Reading it:
\(K_N(\theta)=e(M\theta)S(\theta)\) with \(M=(N+1)/2\) and
\(S=\sin(\pi N\theta)/\sin(\pi\theta)>0\) for \(0<\theta<1/N\), so
\(\overline{K_N}I_{\tilde\beta}=S\int_1^Nt^{\tilde\beta-1}e((t-M)\theta)dt\) and, with
\(t=M+v\) and the symmetry of \([1,N]\) about \(M\),
\[
 \operatorname{Im}\big(\overline{K_N}I_{\tilde\beta}\big)=S(\theta)\int_0^{M-1}\Big[(M+v)^{\tilde\beta-1}-(M-v)^{\tilde\beta-1}\Big]\sin(2\pi v\theta)\,dv .
\]
The bracket is negative for \(v>0\) and equals \(-2(1-\tilde\beta)vM^{\tilde\beta-2}(1+O(v/M))\)
for \(v\le M/2\), the sine is positive throughout since \(2\pi v\theta\le\pi/8\), and
\(S\ge(8/\pi)\sin(\pi/8)N\). So the imaginary part is negative, and
\(\int_0^{M-1}v\sin(2\pi v\theta)dv\asymp\theta M^3\asymp N^2\) gives the size
\((1-\tilde\beta)N^{1+\tilde\beta}\). The remark is right, and the constant it hides is
about \(0.1\) to \(0.3\) (section 6, item (3)). Its consequence, the odd-character case
of the corollary in `MAJOR_ARC_EXPLICIT.md` section 5, is also the case
\(\tilde\chi(-1)=-1\) of (T): the factor \(\kappa^2/\ell\) is \(\mathcal J_-(\tilde\beta)\).

## 6. Finite checks

`page_zero_asymptotic_probe.py`, results in `results_page_zero_asymptotic_probe.json`,
sixteen seconds. Every \(\tilde\beta\) below is a toy: no exceptional zero is reachable
at these \(N\), and nothing here tests (T), (3), or any statement about primes.

**(1) The mean square (10).** At \(N=10^5\) and \(10^6\), \(Z=e^{\sqrt\ell}\), for
\(\tilde q\in\{1,3,5,7,15,21\}\), the measured mean of \(S_*(h)^2\) over \(h\le N\)
coprime to \(\tilde q\) against \((\phi(\tilde q)/\tilde q)\mathfrak M_2(\tilde q;Z)\):
ratios within \(8\times10^{-5}\) at \(N=10^5\) and within \(10^{-5}\) at \(10^6\),
for example \(1.363445\) against \(1.363442\) at \(\tilde q=3\). The full singular series
\(\mathfrak S(h)\) has mean square \(2.300883\) at \(N=10^6\) against \(C_3=2.300962\).

**(2) The energy (11a), (11b).** For \(N\in\{10^4,10^5\}\), \(\kappa\in\{0.3,1\}\) and the
Jacobi character mod \(\tilde q\in\{3,5,7,13,15,21\}\) (even for \(5,13,21\), odd for
\(3,7,15\)), \(\widetilde{\mathcal A}\) computed term by term from (19) with \(J_{12}\) by
quadrature, split into linear, cross and quadratic parts. The linear part against the
right side of (11a) with the exact \(\mathcal J_\pm(\tilde\beta)\): ratios \(1.0000\) at
\(N=10^5\) and within \(2.4\times10^{-4}\) at \(N=10^4\). The quadratic part against
(11b): ratios \(0.973\) to \(0.998\) at \(N=10^4\) and \(0.9966\) to \(0.9997\) at
\(N=10^5\), the defect shrinking like \(1/N\). The cross part is at most \(3\times10^{-4}\)
of the linear part at \(N=10^4\) and \(6\times10^{-6}\) at \(10^5\). The \(h\)-integral of
\(J_{12}^2\) against \(N^{4\tilde\beta-1}\mathcal J_{12}(\tilde\beta)\): \(0.9999\) and
\(0.9975\) at \(N=10^4\), \(0.99999\) and \(0.9997\) at \(10^5\). The scaled integrals:
\(\mathcal J_+/(4/3)=0.990,0.954,0.991,0.961\), \(\mathcal J_-/((15-\pi^2)\delta^2/18)=1.095,1.378,1.085,1.329\),
\(3\mathcal J_{12}=1.494,4.832,1.429,3.937\), at \(\delta=0.099,0.33,0.088,0.29\): the
limits (8) are approached, slowly where the integrand is singular.

**(3) The parity remark.** For \(N\in\{10^4,10^5\}\), \(\kappa\in\{0.3,1\}\), seventeen
values of \(\theta\) across \([1/(16N),1/(8N)]\): \(\operatorname{Im}(\overline{K_N}I_{\tilde\beta})/((1-\tilde\beta)N^{1+\tilde\beta})\)
is negative at every point, between \(-0.33\) and \(-0.11\).

## 7. Scope

One statement, proved from the chain as it stands: the CHHL error is asymptotically the
correction energy of the dominant real zero whenever that zero has small odd conductor
and sits in the window (W), whether or not the target's threshold counts it; the
constant is explicit through (A) and (12). One corollary about the fixed target, that
its binding term is a case. One reading of a remark that had no reader. Not done: the
case of a TT-exceptional character other than \(\tilde\chi\) (a model with two twists;
the cross terms between them are of relative size \(N^{2(\beta_e-1)}\), which is small
only when \((1-\beta_e)\log N\to\infty\), and that is not guaranteed by TT's range); the
case \(q_e>e^{\sigma\sqrt\ell}\) of Corollary 2.3; even conductors beyond Remark 2.2; any
search of the literature for (T). Nothing here is phrased as bearing on the zeros of
\(\zeta\), and nothing here moves the fixed target's exponent constant, which remains
\(2c_0\) for the worst case over the zeros and \(\lambda_0\) in the case of Corollary 2.3.

## 8. The doors, after this document

- **The target's threshold \(c_0\).** Unchanged: a parameter of the definition, the
  operator's to move, with the trade-off of section 1 item 3 (the \(1/12\) is a soft
  constant of the model error, the \(\sqrt c/4\) and \(\sqrt b/4\) are the zero-free
  region and Page at the arc balance).
- **Siegel zeros.** Past \(2c_0\) for the fixed target in the worst case: the corollary
  of `MAJOR_ARC_EXPLICIT.md` section 5, now with an asymptotic in place of the lower
  bound. In the case of Corollary 2.3 the exponent is \(\lambda_0\), tied to the
  zero-free region and to Page, not to \(c_0\).
- **The shape \(\sqrt\ell\).** Inherent to the inputs, `MAJOR_ARC_EXPLICIT.md` section 6.
- **The two-twist model.** The one case (T) does not cover; a computation, not a wall.
- **The minor-arc quartic.** Moot for the exponent, `SHARP_EXPONENT.md` section 4.
