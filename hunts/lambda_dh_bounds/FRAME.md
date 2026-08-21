# FRAME: which normalization a Lambda number is stated in

Written 2026-08-16, as closure item (a) of `GATE.md`.

This page exists because the hunt got the frame wrong once, in the one
sentence a reader would quote. `THEOREM13.md` section 6 said the hunt's
deformation and Dobner's "share Lambda exactly". They do not. They differ by
a factor of exactly 4, and every headline number in this directory therefore
has two values, not one.

The de Bruijn-Newman constant is **not** a number attached to a function. It
is a number attached to a function *plus a choice of where the critical line
is parameterised*. Two conventions are in circulation, both standard, both
used by refereed papers on exactly this constant, and neither of them
announces itself:

    narrow frame :  s = 1/2 + i z      (Stopple; this hunt; Newman-Wu's kernel)
    wide frame   :  s = (1 + i z)/2    (de Bruijn as usually quoted; Newman;
                                        Rodgers-Tao; Polymath 15; Dobner;
                                        zeta/heatflow.py)

    Lambda(wide) = 4 * Lambda(narrow),      Delta(wide) = 2 * Delta(narrow).

Everything below is derived rather than recalled, and every row was checked
by code written for this page (`frame_check.py`, `frame_deform2.py`,
`frame_zeta.py` in this session's scratchpad, sharing no code with
`instrument.py`). Grades follow `MISSION.md`: *measured* is one float route,
*decided* is an enclosure with an exact endpoint sign or an exact integer,
*cited* is somebody else's theorem.

---

## 1. The four conventions, as printed

### 1a. Narrow: Stopple, arXiv:1301.3158, read at source

Stopple's opening, verbatim from the arXiv PDF (his page 1, with `s = 1/2 + it`):

> We define, for s = 1/2 + it,
>
>     Xi(t, chi) =def (D/pi)^{(s+1)/2} Gamma((s+1)/2) L(s, chi)
>                   = int_0^inf Phi(u, chi) cos(ut) du,
>
> where
>
> (1)  Phi(u, chi) = 4 sum_{n=1}^inf chi(n) n exp(3u/2 - n^2 pi exp(2u)/D).

and his page 4, verbatim:

> Following Polya [11] and de Bruijn [1] we introduce a deformation
> parameter t:
>
>     Xi_t(x, chi) = int_0^inf exp(t u^2) Phi(u, chi) cos(ux) du,
>
> so that for t = 0, Xi_0(x, chi) is just Xi(x, chi).

and his Lambda, verbatim:

> There exists a real constant Lambda_{-D}, -inf < Lambda_{-D} <= 1/2, such
> that
>   (1) Xi_t(x, chi) has only real zeros if and only if t >= Lambda_{-D}.
>   (2) Xi_t(x, chi) has some complex zeros if t < Lambda_{-D}.
>
> Definition. We define Lambda_Kr = sup {Lambda_{-D} | -D fundamental}.

Set `D = 5` and replace `chi(n)` by the period-5 Davenport-Heilbronn
coefficients `a_n = (1, kappa, -kappa, -1, 0)`, and this is character for
character the hunt's own pair

    Phi_DH(u) = 4 e^{3u/2} sum_{n>=1} n a_n exp(-pi n^2 e^{2u}/5),
    H_t(z)    = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du,

including the closed half-line that defines `Lambda`. Note
`(D/pi)^{(s+1)/2} = (pi/5)^{-(s+1)/2}` at `D = 5`: the same Gamma factor the
hunt uses. **The hunt's frame is published, refereed, and is Stopple's.** It
was never the hunt's own invention, and the hunt should stop presenting it as
a private choice.

### 1b. Wide: Dobner, arXiv:2005.05142, and the Newman line

Dobner's equations (1), (2), (5), (6), as transcribed in `THEOREM13.md`
section 1 and re-read by adversary 1:

    (1)  xi((1+iz)/2) = int_{-inf}^{inf} Phi(u) e^{izu} du
    (5)  Phi_F(u)     := (1/2pi) int_{-inf}^{inf} xi^F((1+ix)/2) e^{-ixu} dx
    (6)  xi_t^F((1+iz)/2) := int_{-inf}^{inf} e^{t u^2} Phi_F(u) e^{izu} du

The argument is `(1+iz)/2 = 1/2 + i z/2`, so this `z` is twice the narrow
frame's. Rodgers-Tao (arXiv:1801.05914) and Polymath 15 (arXiv:1904.12438)
sit here too, with `H_0(z) = (1/8) Xi(z/2)` and `Xi(T) = xi(1/2 + iT)`; so
does this repository's own `zeta/heatflow.py`, whose module docstring states
`H_0(z) = (1/8) Xi(z/2)` in its equation (3).

### 1c. de Bruijn's own multiplier

de Bruijn 1950 Theorem 13 (transcribed in `THEOREM13.md` section 1) uses

    g(z) = int_{-inf}^{inf} F(t) e^{(1/2) lambda^2 t^2} e^{izt} dt,
    all roots real as soon as lambda >= Delta.

This is a statement about the *multiplier*, not about the critical line, so
it is orthogonal to the narrow/wide split and applies inside either. Matching
`e^{(1/2) lambda^2 u^2}` to `e^{t u^2}` gives `t = lambda^2 / 2`, hence the
all-real threshold `t >= Delta^2 / 2` used by both Stopple's frame and
Dobner's, with each frame's own `Delta`.

Newman and Wu (Bull. AMS 57, 2020, arXiv:1901.06596) restate the same theorem
as their Theorem 7, verbatim from the arXiv PDF, page 8:

> Theorem 7 Suppose that the function F satisfies (10), (11) and the zeros of
> the entire function (9) lie in the strip |Im z| <= Delta. Then all the roots
> of the entire function
>
> (16)     int_{-inf}^{inf} F(t) e^{lambda t^2 / 2} e^{izt} dt
>
> lie in the strip
>
> (17)     |Im z| <= max(Delta^2 - lambda, 0)^{1/2}.

with their (10) `F(-t) = conj F(t)` and their (11)
`|F(t)| <= A exp(-|t|^{2+alpha})`. Their `lambda` is `2t` in the `e^{tu^2}`
convention, so (17) reaches zero at `t = Delta^2/2` again.

### 1d. Newman-Wu's own kernel is narrow, which is a trap

Newman-Wu's equation (7) is

    Phi(u) = sum_{n>=1} (4 pi^2 n^4 e^{9u/2} - 6 pi n^2 e^{5u/2}) e^{-pi n^2 exp(2u)}

and their (19) is `H_lambda(z) = int_R e^{lambda t^2} Phi(t) e^{izt} dt`.
Measured here (`frame_zeta.py`, mpmath dps 30, my own quadrature against
`zeta.core.xi`):

| identity | relative defect at z = 1, 3, 10 |
|---|---|
| `2 int_0^inf Phi_NW(u) cos(zu) du = xi(1/2 + iz)` | 4.5e-42, 2.9e-42, 7.1e-42 |
| `2 int_0^inf Phi_NW(u) cos(zu) du = (1/8) xi(1/2 + iz/2)` | 0.873, 0.854, 0.093 |
| `Phi_NW(u) = 2 Phi_RT(u/2)` at u = -0.3, 0, 0.2, 0.45 | 0.0 (exact to working precision) |
| `H_lambda^{NW}(z) = 8 H_{4 lambda}^{RT}(2z)` at (1, 0.05), (4, 0.1), (2+0.3i, 0.03) | 0.0 (exact to working precision) |

So Newman-Wu's kernel sits in the **narrow** frame, alongside Stopple's, while
Rodgers-Tao's and Dobner's sit in the wide one. Applying (*) of section 2 with
`Phi_NW(u) = 2 Phi_RT(u/2)`, their (19) satisfies
`H_lambda^{NW}(z) = 8 H_{4 lambda}^{RT}(2z)`, so the constant their (19)
defines is a **quarter** of the classical de Bruijn-Newman constant that
Polymath 15 bounds by 0.22. This is worth stating because of what it implies
for the sentence on their page 9:

> Moreover, since the roots of xi lie in the strip |Im z| <= 1/2, de Bruijn's
> quantitative bound (17) gives an upper bound Lambda_DN <= 1/2.

In the narrow frame `Delta = 1/2` is right, and (17) applied to it gives all
roots real at `lambda = Delta^2 = 1/4`, which in their own `e^{lambda t^2}`
kernel of (19) is `Lambda_DN <= 1/8`. The quoted `1/2` is the **wide**-frame
number. It is not false, because `1/8` implies `1/2`; it is four times weaker
than what their own Theorem 7 delivers in their own normalization.

Stopple carries the same classical `1/2` in the same narrow frame. His page 4,
verbatim:

> Since Phi(u, chi) has doubly exponential decay, [1, Theorem 13] applies to
> Xi_t(x, chi) and we have an analog of the theorem of de Bruijn for the
> Riemann zeta function:
>   (1) For t >= 1/2, Xi_t(x, chi) has only real zeros.

For a quadratic Dirichlet L-function the Euler product forces all nontrivial
zeros into `0 <= Re s <= 1`, and `Gamma((s+1)/2)` cancels the trivial zeros
rather than adding any, so in his own frame `Delta = 1/2` and Theorem 13
gives `t >= 1/8`. Again `1/2` is implied and so not false, and again it is the
wide-frame number.

Two refereed sources, both about this exact constant, both carrying the
classical number across a frame change without converting it. That is the
whole reason this page exists, and it is why every number in this directory
now travels with its frame attached.

---

## 2. The scaling law, derived

Let `Phi` be any admissible kernel, `a > 0`, `c != 0`, and set

    Phitilde(u) := (c/a) Phi(u/a),     Htilde_t(z) := int_0^inf e^{t u^2} Phitilde(u) cos(zu) du.

Substitute `u = a v`, `du = a dv`:

    Htilde_t(z) = int_0^inf e^{t a^2 v^2} (c/a) Phi(v) cos(z a v) * a dv
                = c int_0^inf e^{(a^2 t) v^2} Phi(v) cos((a z) v) dv
                = c H_{a^2 t}(a z).                                        (*)

Three consequences, all immediate from (*) and none of them recalled:

1. **Zeros.** `Htilde_t(z) = 0` iff `H_{a^2 t}(a z) = 0`, so the zero set of
   `Htilde_t` is `1/a` times the zero set of `H_{a^2 t}`. Since `a` is real
   and positive, real zeros map to real zeros and `Im` scales by `1/a`.
2. **Strip.** `Delta_tilde = Delta / a`.
3. **Time.** `{t : Htilde_t all real} = {t : H_{a^2 t} all real} =
   (1/a^2) {s : H_s all real}`, so `Lambda_tilde = Lambda / a^2`.

Hence

    z -> a z   gives   Lambda -> Lambda / a^2,   Delta -> Delta / a,

and therefore **`Lambda / Delta^2` is invariant**, which is exactly why the
de Bruijn threshold `Delta^2/2` can be quoted frame-free while `Lambda` and
`Delta` separately cannot. A bound of the form `Lambda <= Delta^2/2` is a
statement about a ratio; a bound of the form `Lambda <= 0.1924` is not.

**Verified** at `a = 1/2, 2, 13/10` with `c = 3/7`: relative defects 2.2e-29,
0.0, 0.0. Numbers and method in section 5.

---

## 3. Narrow to wide, the explicit conversion

Apply (*) with `a = 1/2` and `c = 1/2`, i.e. `Phi_F(u) = Phi_DH(2u)`:

    int_0^inf e^{t u^2} Phi_F(u) cos(zu) du = (1/2) H_{t/4}(z/2),

and Dobner's (6) is the full-line integral, which is twice the half-line one
because `Phi_F` is even. Therefore

    Phi_F(u) = Phi_DH(2u),
    xi_t^F((1+iz)/2) = H_{t/4}(z/2),

and for the constants,

    xi_t^F all real  <=>  H_{t/4} all real  <=>  t/4 >= Lambda(narrow)
                     <=>  t >= 4 Lambda(narrow),

    **Lambda(Dobner) = 4 Lambda(hunt).**

Note what the conversion is *not*: it is not a claim that the two
deformations have different zeros. At matched arguments they are the same
function. What differs is the *label on the time axis*, and a constant
defined as an infimum over that axis inherits the label.

---

## 4. The conversion table

`z_n` is the narrow-frame variable (`s = 1/2 + i z_n`), `z_w` the wide one
(`s = (1 + i z_w)/2`); `z_w = 2 z_n`.

| convention | critical-line parameterisation | kernel / multiplier | Lambda relative to narrow | Delta relative to narrow |
|---|---|---|---|---|
| **Stopple 1301.3158; this hunt** | `s = 1/2 + i z` | `Xi_t(x) = int_0^inf e^{t u^2} Phi(u) cos(ux) du` | `Lambda` | `Delta` |
| **Newman-Wu (19)** | `s = 1/2 + i z` (their (7); measured, section 1d) | `H_lambda = int_R e^{lambda t^2} Phi e^{izt} dt` | `Lambda` | `Delta` |
| **Dobner 2005.05142 (6)** | `s = (1 + i z)/2` | `xi_t^F = int_R e^{t u^2} Phi_F e^{izu} du` | `4 Lambda` | `2 Delta` |
| **Rodgers-Tao; Polymath 15; `zeta/heatflow.py`** | `H_0(z) = (1/8) Xi(z/2)`, i.e. `s = 1/2 + i z/2` | `H_t = int_0^inf e^{t u^2} Phi cos(zu) du` | `4 Lambda` | `2 Delta` |
| **de Bruijn 1950 Thm 13; Newman-Wu Thm 7** | frame-free (a statement about the multiplier) | `e^{(1/2) lambda^2 u^2}`, resp. `e^{lambda u^2 / 2}` | `t = lambda^2/2`, resp. `t = lambda/2`, in whichever frame | threshold `t >= Delta^2/2` in that frame |

The last row is the one that stays put under a change of frame, because it is
the ratio statement of section 2.

---

## 5. Numerical verification of every row

All of this was run for this page, at dps 25 to 40, in code that shares
nothing with `instrument.py`: `kappa` from a linear solve on `F(s) = F(1-s)`,
`f` from Hurwitz zeta at `r/5`, `Phi_DH` from the raw series, and Dobner's
`Phi_F` from **his own definition (5)** by direct Fourier inversion, never by
substituting `Phi_DH(2u)`.

**kappa, own route**: `0.28407904384041229602829183239312617` against the
repo's pinned `KAPPA_REF` `...39312651`, agreeing to 32 digits at dps 60
internal. Functional-equation defect `F(s) - F(1-s)` at `s = 5/2`, `-3/2`,
`1/2 + 4i`, `4/5 + 3i`: `0.0`, `0.0`, `9.4e-42`, `2.6e-42` relative. Grade:
**measured**.

**Row: `H_0 = Xi_DH` in the narrow frame** (dps 40, own quadrature vs own
`F(1/2 + iz)`):

| z | `H_0(z)` | relative defect |
|---|---|---|
| 0.3 | 1.4205880198270777747 | 1.7e-41 |
| 1.0 | 1.2981496966817736704 | 3.8e-43 |
| 5.0 | 0.010735470199021671637 | 2.9e-40 |
| 14.7 | 0.000039144042613077367125 | 5.4e-39 |
| 2 + 0.4i | 0.95863790972440174856 - 0.1637374591566112566i | 0.0 |

**Row: evenness of `Phi_DH`** (the hermitian hypothesis of Theorem 13, and
the step `winding.py` needs), dps 40, relative `|Phi(u) - Phi(-u)|`:
`2.0e-41` at `u = 0.1`, `4.5e-41` at `0.5`, `3.3e-41` at `1.0`. Grade:
**measured**; the *reason* is the functional equation `F(s) = F(1-s)`, written
out in `THEOREM13.md` section 5, item 2.

**Row: `Phi_F(u) = Phi_DH(2u)`**, Dobner's `Phi_F` computed only from his (5),
by inversion of `xi^F((1+ix)/2) = Xi_DH(x/2)` truncated at `R = 140`, dps 40.
The truncation floor is set by the Gamma factor: `|Xi_DH(y)|` decays like
`exp(-pi y/4)` (measured: 1.86e-6, 4.81e-14, 8.87e-19, 4.17e-23 at
`y = 20, 40, 55, 70`), and the inversion runs in `x = 2y`, so the neglected
tail is about `exp(-pi R/8)`. Measured directly, by varying `R` at fixed
`u = 0.3` and dps 30:

| R | 40 | 60 | 80 | 110 | 140 |
|---|---|---|---|---|---|
| rel. defect vs `Phi_DH(2u)` | 1.0e-6 | 1.3e-10 | 7.0e-14 | 6.5e-19 | 1.8e-24 |

which is the `exp(-pi R/8)` law, so `R = 140` supports about 24 digits and
`R = 80` about 13. At `R = 140`, dps 40:

| u | `Phi_F(u)` from (5) | rel. vs `Phi_DH(2u)` | rel. vs `Phi_DH(u)` |
|---|---|---|---|
| 0 | 2.305419825971440752138 | 8.3e-24 | 8.3e-24 |
| 0.15 | 2.032945249046710636167 | 6.2e-24 | **0.0919** |
| 0.4 | 0.5911191932630095506773 | 2.9e-23 | **0.674** |
| 0.7 | 0.001063508494264118824889 | 7.2e-21 | **0.9988** |

The `u = 0` row cannot separate the hypotheses and is included only as a
sanity check. The other three separate them by twenty orders of magnitude.
Grade: **measured**.

**Row: the deformation identity `xi_t^F((1+iz)/2) = H_{t/4}(z/2)`**, checked
end to end. Dobner's (6) is evaluated from his (5) alone, on a composite
Gauss-Legendre node set (5 panels, 10 nodes each, on `[0, 1.6]`) whose 50
`Phi_F` values are each a separate Fourier inversion at `R = 80`, dps 28. The
node set's own quality, measured against the analytically known
`2 int_0^inf Phi_F(u) cos(3u) du = Xi_DH(3/2)`, is 7.6e-16, so that is the
floor for this row.

| z | t | `xi_t^F((1+iz)/2)` from (5)+(6) | rel. vs `H_{t/4}(z/2)` | rel. vs `H_t(z)`, the frame-identified reading |
|---|---|---|---|---|
| 1 | 1/5 | 1.411782501208473636314 | 7.7e-15 | **0.0484** |
| 3 | 2/5 | 1.159034557111109238044 | 2.6e-15 | **0.567** |
| 7/10 | 36/625 | 1.420001737196666980069 | 7.2e-15 | **0.0280** |
| 2 + 0.3i | 1/4 | 1.314420783825719854807 - 0.040120424537588350713i | 9.1e-15 | **0.270** |

and the `t = 0` endpoint `xi_0^F((1+iz)/2) = Xi_DH(z/2)`: relative 7.5e-15 at
`z = 1`, 7.6e-16 at `z = 3`, 1.6e-12 at `z = 9`. So the correct conversion is
confirmed to 15 significant digits while the reading the false sentence
licensed is wrong in the second significant digit. Grade: **measured**.

**Row: the scaling law (*)** of section 2, both sides by independent
quadrature, `c = 3/7`, `z = 2`, `t = 3/10`, dps 28:

| a | rel. defect of `Htilde_t(z) = c H_{a^2 t}(a z)` |
|---|---|
| 1/2 | 2.2e-29 |
| 2 | 0.0 (exact to working precision) |
| 13/10 | 0.0 (exact to working precision) |

Grade: **measured**.


**Row: the zeta frames** (`frame_zeta.py`, dps 30, against `zeta.core.xi`):
`int_0^inf Phi_RT cos(zu) du = (1/8) Xi(z/2)` to 1.8e-42 - 5.2e-42;
`int_R Phi_D e^{izu} du = Xi(z/2)` to the same; `2 int_0^inf Phi_NW cos(zu) du
= Xi(z)` to 2.9e-42 - 7.1e-42 while missing `(1/8)Xi(z/2)` by 0.09 to 0.87.
Grade: **measured**.

---

## 6. The headline numbers, in both frames

The bounds themselves are unchanged; only their labels are. The lower side
rests on a decided argument-principle count (`winding_results.json`,
`decided_floor_t = 36/625`) plus Dobner's closed half-line; the upper side is
`Delta^2/2` with `Delta = sigma_0 - 1/2` and `sigma_0` decided on both
backends (`strip_results.json`).

|  | narrow (Stopple / this hunt) | wide (Dobner / Newman / Rodgers-Tao / Polymath 15) |
|---|---|---|
| `sigma_0'` (phase obstruction, `STRIP2.md`) | 1.12036249819, exactly 112036249819/100000000000 | same (an abscissa is a point in the `s` plane, not a `z`) |
| `Delta` | 0.62036249819 (exact) | 1.24072499638 (exact) |
| lower bound on `Lambda_DH` | **> 0.0576**, exactly 36/625 | **> 0.2304**, exactly 144/625 |
| `Delta^2/2` | 0.19242481458026887663805 (exact, = 3848496291605377532761/20000000000000000000000) | 0.7696992583210755065522 (exact, four times it) |
| upper bound headline | **<= 0.19242481458026887663805** | **<= 0.7696992583210755065522** |
| ratio upper/lower | 3.341 | 3.341 (invariant) |

**Note that the abscissa and the ratio are the frame-free quantities**, and
the ratio is the honest measure of how loose the bracket is. No outward
rounding is involved in this row: the abscissa is decided at an exact
rational, so `Delta^2/2` terminates. `STRIP2.md` section 5.2 displays the
narrow value rounded outward to 22 decimals as `0.1924248145802688766381`,
which is the same bound one display ulp higher.

**Superseded 2026-08-18, kept because it is still correct.** Through
2026-08-17 the headline came from the coefficient-domination abscissa of
`STRIP.md` instead, and that row read:

|  | narrow | wide |
|---|---|---|
| `sigma_0` | 1.3951361582351097210613588712...9375 | same |
| `Delta` | 0.8951361582351097210613588712...9375 | 1.7902723164702194421227177424...8750 |
| decided `Delta^2/2` interval | [0.4006343708899556944469547527, 0.4006343708899556944469548120] | [1.6025374835598227777878190108, 1.6025374835598227777878192480] |
| upper bound headline (rounded outward, above the interval's upper endpoint) | **<= 0.4006343708899557** | **<= 1.6025374835598228** |
| ratio upper/lower | 6.955... | 6.955... (invariant) |

The sharpening is a factor **2.082030697360155** and it is in-tree: the
abscissa is derived from a phase obstruction in the Euler products of the two
Dirichlet L-functions whose combination `f` is, and decided on **both**
backends (python-flint 192 bits and mpmath.iv dps 40, sieve limit
`P = 10^5`, 4814 class primes), with a flint-only deep point at 320 bits and
`P = 10^7` deciding 1.1203624981833251. **The lower bound did not move**, so
the separation of `SEPARATION.md`, which rests on the floor alone, is
unaffected.

The relation to the literature, restated exactly. Bombieri and Ghosh
(Russian Math. Surveys 66 (2011), section 6, read in full 2026-08-16, see
`BOMBIERI-GHOSH.md`) determine the exact least upper bound of the real parts
of the zeros of this function, `sigma(tau_+, 1) = 1.120362`. The criterion
`STRIP2.md` decides *is* their Theorem 7 at `q = 1` and `xi = kappa`, term
for term; only its **necessary** half is used, and that half is derived here
from the Euler product and one Moebius image, with no Bohr theory and no
Kronecker theorem. Their converse, which makes the abscissa an exact supremum
rather than an upper bound, is not used and not claimed. **So the number is
theirs and the grade is this hunt's**, and neither `sigma_0` nor `sigma_0'`
may be described as a new number.

**A row this file used to carry, and the correction it needed.** Through
2026-08-17 the table above had a "B-G `sigma(tau_+, 1) = 1.120362` (cited, six
decimals)" row printing `0.192424814576128011...` narrow and
`0.769699258304512045...` wide. `GATE.md`'s closure log flagged that those 18
digits came from `BOMBIERI-GHOSH.md`'s own 29-digit re-solve rather than from
the six cited decimals (which alone give 0.192424505522). `strip2.py` now
decides that the re-solve itself sits about `1.2e-17` *above* its own root, so
the correct value from the deep point is `0.1924248145761280190` narrow and
`0.7696992583045120759956154` wide, agreeing with the old row to 17 digits.
The headline above is the slightly more conservative two-backend `P = 10^5`
value, and it is exact.

## 7. The zeta record, in both frames

`NOVELTY.md` originally quoted these in the wide frame while calibrating a
narrow-frame number against them, which flattered the comparison by exactly
the factor 4. Both columns, so that cannot recur:

| statement | wide frame (as published) | narrow frame (this hunt's) |
|---|---|---|
| de Bruijn 1950, upper | `Lambda_zeta <= 1/2` | `<= 1/8` |
| Ki-Kim-Lee 2009, strict upper | `Lambda_zeta < 1/2` | `< 1/8` |
| Polymath 15 / Rodgers-Tao, upper | `Lambda_zeta <= 0.22` | `<= 0.055` |
| Newman's conjecture / Rodgers-Tao theorem, lower | `Lambda_zeta >= 0` | `>= 0` (sign is frame-free) |
| Saouter-Gourdon-Demichel 2011, historical lower | `> -1.15e-11` | `> -2.875e-12` |

And the comparison the conversion actually buys, stated in the common wide
frame where both live:

    Lambda_zeta <= 0.22    (Polymath 15)
    Lambda_DH   >  0.2304  (this hunt)

so the Davenport-Heilbronn constant sits **above** the best known upper bound
for zeta, hence `Lambda_DH > Lambda_zeta`. Stated in the narrow frame alone,
`0.0576` sits below `0.22` and a reader draws the opposite conclusion. That is
the single most important reason to publish both columns rather than pick one.

Grade of that comparison, per `MISSION.md`: the DH side is **decided** modulo
Dobner's Theorem 1 (an enclosure-carrying integer count plus a cited closed
half-line); the zeta side is **cited** (Polymath 15). A composite takes its
weakest step, so `Lambda_DH > Lambda_zeta` is a *cited-plus-decided* statement
and not a claim this directory proves on its own.

## 8. What to write, every time

- Give the frame with the number: "in the normalization of Stopple
  (arXiv:1301.3158), `s = 1/2 + iz`".
- Print both values, or print one and give the factor 4 and its direction in
  the same sentence.
- Never quote a zeta record without converting it into the frame of the
  number it is being compared with.
- `Lambda / Delta^2` and `sigma_0` are the frame-free quantities. Prefer them
  when the point is a comparison rather than a value.
