# POLYMATH-PIN: the Polymath 15 and Rodgers-Tao statements, pinned at source

Written 2026-08-16. The separation claim `Lambda_DH > Lambda_zeta` is
load-bearing on the exact statement and frame of Polymath 15's upper bound, so
both papers are quoted here at source rather than from memory or from
`FRAME.md`'s summary.

**Retrieval route.** Both ar5iv renderings were downloaded whole
(`ar5iv.labs.arxiv.org/html/1904.12438`, 1,688,923 bytes;
`ar5iv.labs.arxiv.org/html/1801.05914`, 1,285,339 bytes; retrieved
2026-08-16, latest posted arXiv versions as ar5iv serves them). Every
displayed formula below is the paper's own LaTeX, extracted character for
character from the MathML `alttext` attributes of the rendered HTML, not
transcribed by hand and not summarised by a model. Prose is taken verbatim
from the same files with markup stripped. In the Rodgers-Tao rendering the
bibliography keys appear raw (`debr`, `newman`, `kkl`, `polymath`) because
ar5iv did not resolve them; they are left as served.

Publication data: Polymath is published as Res. Math. Sci. 6 (2019), art. 31;
Rodgers-Tao as Forum Math. Pi 8 (2020), e6 (journal data recalled, not
re-fetched; the pin is to the arXiv text).

---

## 1. Polymath 15, arXiv:1904.12438, Section 1 (Introduction)

Displays (1)-(4) and their connecting prose, verbatim (arXiv PDF pages 1-2):

> Let $H_{0}\colon\mathbb{C}\to\mathbb{C}$ denote the function
>
> (1) $H_{0}(z)\coloneqq\frac{1}{8}\xi\left(\frac{1}{2}+\frac{iz}{2}\right),$
>
> where $\xi\colon\mathbb{C}\to\mathbb{C}$ denotes the Riemann $\xi$ function
>
> (2) $\xi(s)\coloneqq\frac{s(s-1)}{2}\pi^{-s/2}\Gamma\left(\frac{s}{2}\right)\zeta(s)$
>
> (which is an entire function after removing all singularities) and $\zeta$
> is the Riemann $\zeta$ function. Then $H_{0}$ is an entire even function
> with functional equation $H_{0}(\overline{z})=\overline{H_{0}(z)}$, and the
> Riemann hypothesis (RH) is equivalent to the assertion that all the zeroes
> of $H_{0}$ are real. It is a classical fact (see [27, p. 255]) that $H_{0}$
> has the Fourier representation
>
> $H_{0}(z)=\int_{0}^{\infty}\Phi(u)\cos(zu)\ du$
>
> where $\Phi$ is the super-exponentially decaying function
>
> (3) $\Phi(u)\coloneqq\sum_{n=1}^{\infty}(2\pi^{2}n^{4}e^{9u}-3\pi n^{2}e^{5u})\exp(-\pi n^{2}e^{4u}).$
>
> The sum defining $\Phi(u)$ converges absolutely for negative $u$ also. From
> Poisson summation one can verify that $\Phi$ satisfies the functional
> equation $\Phi(u)=\Phi(-u)$ (i.e., $\Phi$ is even); this fact is of course
> closely related to the functional equation for $\zeta$. De Bruijn [5]
> introduced (with somewhat different notation) the more general family of
> functions $H_{t}\colon\mathbb{C}\to\mathbb{C}$ for $t\in\mathbb{R}$, defined
> by the formula
>
> (4) $H_{t}(z)\coloneqq\int_{0}^{\infty}e^{tu^{2}}\Phi(u)\cos(zu)\ du.$

The de Bruijn / Newman paragraph, verbatim (Section 1, the paragraph
following (4)):

> It follows from the work of Pólya [19] that if $H_{t}$ has purely real
> zeroes for some $t$, then $H_{t^{\prime}}$ has purely real zeroes for all
> $t^{\prime}>t$; de Bruijn showed that the zeroes of $H_{t}$ are purely real
> for $t\geq 1/2$. Newman [14] strengthened this result by showing that there
> is an absolute constant $-\infty<\Lambda\leq 1/2$, now known as the De
> Bruijn-Newman constant, with the property that $H_{t}$ has purely real
> zeroes if and only if $t\geq\Lambda$. The Riemann hypothesis is then clearly
> equivalent to the upper bound $\Lambda\leq 0$. Recently in [22] the
> complementary bound $\Lambda\geq 0$ was established, answering a conjecture
> of Newman [14], and improving upon several previous lower bounds for
> $\Lambda$ [6, 15, 8, 7, 16, 23]. Furthermore, Ki, Kim, and Lee [10]
> sharpened the upper bound $\Lambda\leq 1/2$ of de Bruijn [5] slightly to
> $\Lambda<1/2$. In this paper we improve the upper bound:

(Their [22] is Rodgers-Tao, their [5] is de Bruijn 1950. ASCII math is house
style for authored text only; the quotes keep the source's own characters.)

The theorem, verbatim (Section 1):

> Theorem 1.1 (New upper bound). We have $\Lambda\leq 0.22$.

From the abstract, verbatim:

> By combining these estimates with numerical computations, we are able to
> obtain a new upper bound $\Lambda\leq 0.22$ unconditionally, as well as
> improvements conditional on further numerical verification of the Riemann
> hypothesis.

One further pin, because it is the hunt's own upper-bound engine appearing in
their frame: their Theorem 1.2 (Upper bound criterion), Section 1, concludes

> Then $\Lambda\leq t_{0}+\frac{1}{2}y_{0}^{2}$.

which is the `t + Delta^2/2` bookkeeping with `y_0` the surviving strip
height at time `t_0`.

## 2. Rodgers-Tao, arXiv:1801.05914, Section 1 (Introduction)

Their displays (1)-(4) are character for character the same LaTeX as Polymath
15's (1)-(4) above, same numbering, same connecting prose up to trivial
variants ("where $\xi$ denotes the Riemann xi function", "(see (titch,
p. 255))"). Extracted alttext, verbatim:

> $H_{0}(z)\coloneqq\frac{1}{8}\xi\left(\frac{1}{2}+\frac{iz}{2}\right),$ (1)
>
> $\xi(s)\coloneqq\frac{s(s-1)}{2}\pi^{-s/2}\Gamma\left(\frac{s}{2}\right)\zeta(s)$ (2)
>
> $\Phi(u)\coloneqq\sum_{n=1}^{\infty}(2\pi^{2}n^{4}e^{9u}-3\pi n^{2}e^{5u})\exp(-\pi n^{2}e^{4u}).$ (3)
>
> $H_{t}(z)\coloneqq\int_{0}^{\infty}e^{tu^{2}}\Phi(u)\cos(zu)\ du.$ (4)

Their de Bruijn / Newman paragraph, verbatim (Section 1, following (4)):

> De Bruijn showed that the zeroes of $H_{t}$ are purely real for
> $t\geq 1/2$. Strengthening these results, Newman [newman] showed that there
> is an absolute constant $-\infty<\Lambda\leq 1/2$, now known as the De
> Bruijn-Newman constant, with the property that $H_{t}$ has purely real
> zeroes if and only if $t\geq\Lambda$. The Riemann hypothesis is then
> clearly equivalent to the upper bound $\Lambda\leq 0$. Newman conjectured
> the complementary lower bound $\Lambda\geq 0$, and noted that this
> conjecture asserts that if the Riemann hypothesis is true, it is only
> “barely so”.

The upper-bound history sentence, verbatim, including the footnote text
(Section 1, after Table 1; footnote 1 added in press):

> We also mention that the upper bound $\Lambda\leq 1/2$ of de Bruijn [debr]
> was sharpened slightly [footnote 1: Added in press: this bound has recently
> been improved to $\Lambda\leq 0.22$ in [polymath].] by Ki, Kim, and Lee
> [kkl] to $\Lambda<1/2$. See also [stopple], [cmmrs] on work on variants of
> Newman's conjecture, and ([broughan], Chapter 5) for a survey.

The theorem, verbatim (Section 1):

> Theorem 1 One has $\Lambda\geq 0$.

## 3. Their frame is the wide one, in three lines

1. Their (1) reads `H_0(z) = (1/8) xi(1/2 + iz/2)`, so their `z` sits on
   `s = 1/2 + iz/2 = (1 + iz)/2`; with `Xi(T) = xi(1/2 + iT)` this is
   `H_0(z) = (1/8) Xi(z/2)`, and the zero strip `0 <= Re s <= 1` becomes
   `|Im z| <= 1`: `Delta = 1`, double the narrow frame's `Delta = 1/2` at
   `s = 1/2 + iz`.
2. The hunt's DH object is `H_0(z) = F(1/2 + iz)` with no `z/2` (Stopple's
   kernel at `D = 5`, `FRAME.md` section 1a): the narrow frame, so
   `z_wide = 2 z_narrow`.
3. `FRAME.md` section 2's scaling law (`z -> a z` gives
   `Lambda -> Lambda / a^2`; both kernels carry the same multiplier
   `e^{t u^2}`, so `a = 2` is the whole difference) gives
   `Lambda(wide) = 4 Lambda(narrow)`, measured end to end on Dobner's own
   definitions to 15 significant digits in `FRAME.md` section 5.

Kernel-level corroboration: their (3) has `e^{4u}` inside the Gaussian where
the narrow kernel (Newman-Wu's (7), `FRAME.md` section 1d) has `e^{2u}`, and
`Phi_NW(u) = 2 Phi_P15(u/2)` holds exactly to working precision (measured,
`frame_zeta.py`, mpmath dps 30). Same doubling, seen in the kernel instead of
the argument.

## 4. The separation chain, every link cited or decided

    0 <= Lambda_zeta                       cited: Rodgers-Tao Theorem 1 (Section 2 above)
    Lambda_zeta <= 0.22                    cited: Polymath 15 Theorem 1.1 (Section 1 above),
                                           unconditional per their abstract
    0.22 = 11/50 < 144/625 = 0.2304        exact rational arithmetic, cross-multiplied:
                                           144 * 50 = 7200 > 6875 = 11 * 625
    0.2304 = 4 * (36/625) < Lambda_DH      this hunt, decided: winding count N = 1 for
                                           H_{36/625} (narrow) over a box with interior
                                           Im z >= 3/1024 in exact rationals, python-flint
                                           0.9.0 (Arb) balls, second witness mpmath dps 130
                                           (winding_results.json); strictness cited, Dobner
                                           arXiv:2005.05142 Theorem 1 closed half-line;
                                           frame factor 4 derived in FRAME.md section 3
    Lambda_DH <= 0.7696992583210755065522
                                           this hunt, decided: 4 x the narrow Delta^2/2,
                                           exactly, at the phase-obstruction abscissa
                                           sigma_0' = 112036249819/100000000000 decided on
                                           both backends (python-flint Arb 192 bits and
                                           mpmath.iv dps 40, sieve limit P = 1e5) with exact
                                           rational sign decisions, kappa at 500 bits
                                           (strip2_results.json); de Bruijn 1950 Theorem 13
                                           cited. Through 2026-08-17 this link read
                                           <= 1.6025374835598228, from the coefficient-
                                           domination interval
                                           [0.4006343708899556944469547527,
                                           0.4006343708899556944469548120] of
                                           strip_results.json, which is still correct and is
                                           retained

Hence, in the wide frame where all four sources above live:

    0 <= Lambda_zeta <= 0.22 < 0.2304 < Lambda_DH <= 0.7696992583210755065522,

so `Lambda_DH > Lambda_zeta` unconditionally. Composite grade per
`MISSION.md`: **cited plus decided** (weakest step is a citation; the lower
bound additionally carries the `M2` lemma recorded in `GATE.md`, prose when
this page was written and proved with decided constants since 2026-08-18,
`M2-LEMMA.md`). **The last link is not used by the separation**, which rests
on the floor and on the cited zeta bound alone; sharpening it on 2026-08-18
moved nothing else in this chain.

Frame-invariance check, narrow frame: divide every Lambda by 4.

    0 <= Lambda_zeta <= 0.055 < 0.0576 = 36/625 < Lambda_DH <= 0.19242481458026887663805,

and the middle comparison is the *same* cross-multiplication, because the
factor 4 cancels: `0.055 = 11/200`, and `36 * 200 = 7200 > 6875 = 11 * 625`.
The inequality `Lambda_DH > Lambda_zeta` reads identically in both frames,
as an inequality between constants of the same frame must.

## 5. What the sources did and did not say (the surprises)

1. **Neither paper makes any normalization remark at all.** The task of
   pinning "their remark that de Bruijn's `Lambda <= 1/2` lives in the same
   frame" turns out to be unfillable: there is no such remark. Both papers
   simply *assert* de Bruijn's result of their own `H_t` ("de Bruijn showed
   that the zeroes of $H_{t}$ are purely real for $t\geq 1/2$", with `H_t`
   their (4)), and Polymath 15 adds only "(with somewhat different
   notation)" about de Bruijn's original. So the frame of the classical
   `1/2` is theirs by restatement, not by remark, and the anchor for the
   hunt's dictionary is display (1) itself, not any prose about conventions.
   This is consistent with `FRAME.md`'s finding that frame conversions in
   this literature are routinely silent.
2. **Rodgers-Tao cite Stopple, with no conversion.** Their "See also
   [stopple], [cmmrs] on work on variants of Newman's conjecture" points
   straight at the narrow-frame paper this hunt inherits, one sentence after
   quoting the wide-frame `Lambda <= 1/2`, with nothing said about the
   factor 4 between them. The two frames touch in print exactly once in
   these two papers, and the touch carries no warning.
3. **The two introductions share their displays character for character.**
   P15's (1)-(4) and RT's (1)-(4) are the same LaTeX byte for byte in the
   extracted alttext. Quoting either paper's display pins both.
4. **Nothing else surprised.** The kernel is the expected wide one
   (`e^{4u}` in the Gaussian), `H_0(z) = (1/8) xi(1/2 + iz/2)` is exactly as
   `FRAME.md`'s conversion table row states, `Lambda <= 0.22` is
   unconditional and stated with no side conditions, and RT's Theorem 1 is
   the bare `Lambda >= 0`. The pinned quotes confirm the hunt's dictionary
   with no adjustment needed anywhere.
