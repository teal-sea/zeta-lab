# Novelty record for `lambda_dh_bounds`

Recorded 2026-08-16, from a web sweep run before the hunt opened. Per the
house rule (`ontology/knownness.py`: an unrun check can never read as absence
of prior art), this file says exactly what was searched and what it found.
Nothing below is a claim that anything is *novel*; it is the record a novelty
claim would have to stand on, plus the caveats it would have to carry.

> **Revised 2026-08-16** after the prior-art adversary
> (`attack_adversary5_priorart.md`) and the gate (`GATE.md`, closure items
> (a) and (d)). Four changes, each marked in place: the zeta calibration
> figures now appear in **both** normalizations, because the original quoted
> them in one frame and compared them against a number in the other; Stopple
> is promoted from a one-line mention to the published precedent for this
> hunt's own normalization *and* a prior quantitative non-zeta de
> Bruijn-Newman bound; Newman-Wu Theorem 7 is added as the typeset
> restatement of the engine; and Bombieri-Ghosh 2011 is added, first as an
> unread standing risk to the strip constant and then, later the same day
> after a sibling session retrieved and read it in full
> (`BOMBIERI-GHOSH.md`), as a **closed** risk with a mixed verdict: it
> carries no de Bruijn-Newman content at all, so the bracket is not
> anticipated, but it determines the exact zero-strip abscissa for this
> function, `sigma(tau_+, 1) = 1.120362`, so `sigma_0` is a weaker bound on a
> quantity that was already known. The novelty sentence is rewritten in
> section "The sentence" and the superseded version is kept there verbatim;
> the sentence itself survives the Bombieri-Ghosh reading unchanged, and only
> its footnote moved.

## Read `FRAME.md` first

Every `Lambda` number in this directory has two values, four apart. The error
originated in `THEOREM13.md` section 6 and surfaced here, in the calibration
against the zeta record below. The two frames:

    narrow :  s = 1/2 + i z      (Stopple; this hunt)
    wide   :  s = (1 + i z)/2    (de Bruijn as usually quoted; Newman;
                                  Rodgers-Tao; Polymath 15; Dobner)

    Lambda(wide) = 4 * Lambda(narrow).

The hunt's headline in both:

    narrow (Stopple / this hunt) :  0.0576 < Lambda_DH <= 0.4006343708899557
    wide   (Dobner / Polymath 15):  0.2304 < Lambda_DH <= 1.6025374835598228

Derivation, sources and per-row numerical checks are in `FRAME.md`.

## What is published, and the delta this hunt targets

- **Dobner 2020** (*A proof of Newman's conjecture for the extended Selberg
  class*, arXiv:2005.05142; published in Acta Arithmetica 2021, where the
  arXiv title differs, which is a real trap for a title search). Theorem 1:
  for every F in the extended Selberg class S# there is a real Lambda_F with
  all zeros of the deformation on the critical line iff t >= Lambda_F (the
  half-line structure). Theorem 2: Lambda_F >= 0. The Davenport-Heilbronn
  function is in S# (absolutely convergent series for Re s > 1, entire
  completion, functional equation with gamma factor
  (pi/5)^{-(s+1)/2} Gamma((s+1)/2); no Euler product is required for S#). So
  existence, finiteness and nonnegativity of Lambda_DH are published, and
  strict positivity is an immediate corollary of Theorem 1 plus any computed
  off-line zero (Spira 1994). Dobner names no member and gives no number.
  **The delta: quantitative bounds.** His frame is the wide one.
- **Stopple 2013** (*Notes on Low discriminants and the generalized Newman
  conjecture*, arXiv:1301.3158), read at source this session and re-read for
  this revision. **This is the nearest prior work and it does two things at
  once.**

  *(i) It is the published precedent for this hunt's normalization.* His
  opening, verbatim from the arXiv PDF (`s = 1/2 + it`):

  > We define, for s = 1/2 + it,
  >
  >     Xi(t, chi) =def (D/pi)^{(s+1)/2} Gamma((s+1)/2) L(s, chi)
  >                   = int_0^inf Phi(u, chi) cos(ut) du,
  >
  > where
  >
  > (1)  Phi(u, chi) = 4 sum_{n=1}^inf chi(n) n exp(3u/2 - n^2 pi exp(2u)/D).

  and, four pages later,

  > Following Polya [11] and de Bruijn [1] we introduce a deformation
  > parameter t:
  >
  >     Xi_t(x, chi) = int_0^inf exp(t u^2) Phi(u, chi) cos(ux) du,

  with the constant defined by the same closed half-line this hunt uses:

  > There exists a real constant Lambda_{-D}, -inf < Lambda_{-D} <= 1/2, such
  > that
  >   (1) Xi_t(x, chi) has only real zeros if and only if t >= Lambda_{-D}.
  >   (2) Xi_t(x, chi) has some complex zeros if t < Lambda_{-D}.
  >
  > Definition. We define Lambda_Kr = sup {Lambda_{-D} | -D fundamental}.

  Set D = 5 and replace chi(n) by the period-5 coefficients a_n and this is
  character for character the hunt's Phi_DH, H_t and Lambda_DH. The hunt did
  not invent this frame and must stop presenting it as its own choice.

  *(ii) It is a prior quantitative bound on a non-zeta de Bruijn-Newman
  constant.* His abstract states `-1.13 * 10^{-7} < Lambda_Kr`, sharpened in
  his Theorem 3 to

  > We have that -D = -175990483 satisfies (15), and the corresponding zero
  > gives the bound
  >
  >     -1.12929 * 10^{-7} < Lambda_Kr.

  and his upper side is conditional: "Under the GRH, Lambda_Kr <= 0." So any
  phrasing of the form *first quantitative bound on a de Bruijn-Newman
  constant other than zeta's* is **false**, and the earlier version of this
  file, which listed Stopple only among "generalized Newman lines, all at
  negative-or-zero values", undersold him badly. What Stopple does not have
  is a function that violates its own Riemann hypothesis: quadratic Dirichlet
  L-functions have Euler products and are expected to satisfy GRH, and his
  lower bound is a Lehmer-pair argument, not an off-line zero.
- **Newman-Wu 2020** (*Constants of de Bruijn-Newman type in analytic number
  theory and statistical physics*, Bull. AMS 57, arXiv:1901.06596). Two
  separate roles.

  *(i) The engine, typeset.* Their Theorem 7, verbatim from the arXiv PDF,
  page 8, is the modern restatement of de Bruijn 1950 Theorem 13 that this
  hunt's upper bound uses:

  > Theorem 7 Suppose that the function F satisfies (10), (11) and the zeros
  > of the entire function (9) lie in the strip |Im z| <= Delta. Then all the
  > roots of the entire function
  >
  > (16)     int_{-inf}^{inf} F(t) e^{lambda t^2 / 2} e^{izt} dt
  >
  > lie in the strip
  >
  > (17)     |Im z| <= max(Delta^2 - lambda, 0)^{1/2}.

  with (10) `F(-t) = conj F(t)`, (11) `|F(t)| <= A exp(-|t|^{2+alpha})` for
  some A, alpha > 0, and (9) `f(z) = int_R F(t) e^{izt} dt`. Their lambda is
  2t in the `e^{tu^2}` convention, so (17) reaches zero at t = Delta^2/2:
  this hunt's dictionary, in a Bulletin of the AMS survey, with a strip
  hypothesis and no positivity hypothesis on Phi. **The mechanism of the
  upper bound is published and surveyed; what this hunt supplies is the strip
  constant it is fed.** Cite this alongside de Bruijn 1950 rather than
  resting on the image-only 1950 scan.

  *(ii) A strictly positive constant, computed exactly.* They determine a
  de Bruijn-Newman type constant exactly, `Lambda(rho) = ln 2`, for a
  concrete three-atom probability *measure* (their Case 2; the set of
  admissible values is `[ln 2, inf)`). Any phrasing of the form "first
  strictly positive constant of this type for a concrete object" is
  therefore false. Their text contains no occurrence of Davenport, Heilbronn
  or Epstein.
- **The zeta record**, for calibration, **in both frames**.

  > *Superseded.* This entry originally read: "**The zeta record** for
  > calibration: 0 <= Lambda_zeta <= 0.22 (Rodgers-Tao arXiv:1801.05914;
  > Polymath 15 arXiv:1904.12438), Lambda_zeta < 1/2 (Ki-Kim-Lee 2009),
  > historical lower bounds all negative, ending at -1.15e-11
  > (Saouter-Gourdon-Demichel 2011)." Every one of those is a **wide**-frame
  > number, and the hunt's 0.4006 that they were calibrating is a **narrow**-
  > frame number, so the comparison flattered the hunt by a factor of 4. The
  > cause was the false sentence in `THEOREM13.md` section 6 (now corrected
  > there, with the original preserved).

  | statement | wide frame (as published) | narrow frame (this hunt's) |
  |---|---|---|
  | de Bruijn 1950, upper | `Lambda_zeta <= 1/2` | `<= 1/8` |
  | Ki-Kim-Lee 2009, strict upper | `Lambda_zeta < 1/2` | `< 1/8` |
  | Rodgers-Tao / Polymath 15, upper | `Lambda_zeta <= 0.22` | `<= 0.055` |
  | Rodgers-Tao, lower (Newman's conjecture) | `Lambda_zeta >= 0` | `>= 0` |
  | Saouter-Gourdon-Demichel 2011, historical lower | `> -1.15e-11` | `> -2.875e-12` |

  Read in the common wide frame, where both live, the comparison the
  conversion actually buys is

      Lambda_zeta <= 0.22    (Polymath 15)
      Lambda_DH   >  0.2304  (this hunt, decided)

  so the Davenport-Heilbronn constant sits **above** the best known upper
  bound for zeta. In the narrow frame alone, 0.0576 sits below 0.22 and a
  reader draws the opposite conclusion. Publish both columns.
- **Generalized Newman lines, all at negative-or-zero values**: quadratic
  Dirichlet L-functions (Stopple arXiv:1301.3158, see above, whose bound is
  in the narrow frame; Andrade-Chang-Miller arXiv:1310.3477; best concrete
  bound Lambda_D > -1.17e-7), function fields
  (Chang-Mehrle-Miller-Reiter-Stahl-Yott arXiv:1411.2071, constants <= 0 with
  sup 0 attained). No RH-violating function is treated anywhere in this line.
- **DH zero distribution context**: off-line zeros exist
  (Davenport-Heilbronn 1936), computed instances Spira (Math. Comp. 1994)
  and Balanzario-Sanchez-Ortiz (Math. Comp. 76, 2007); DH also has zeros
  with Re s > 1 (discussed in Ferry et al., arXiv:1602.06328), which is why
  the zero strip needs the coefficient-domination argument; line-zero
  counts Karatsuba 1990/91 and Gritsenko 2017 (Proc. Steklov 296). Note:
  arXiv:2503.24275 (2025) claims DH zeros lie only on the critical line;
  this contradicts the computed zeros above and the repo's own pinned
  50-digit zero, and is treated as unsound.
- **de Bruijn 1950** (Duke Math. J. 17, 197-226), Theorem 13, is the upper
  bound's engine. The restatements consulted (Csordas-Norfolk-Varga 1988;
  Ki-Kim, J. Anal. Math. 91 (2003), where de Bruijn's class conditions are
  integrability, realness/evenness in the sense F(-t) = conj F(t), and
  decay O(e^{-|t|^b}) with b > 2) require **no positivity of Phi**, which
  matters here because Phi_DH has mixed-sign coefficients. The
  all-zeros-in-strip form (zeros of H_0 in |Im z| <= Delta implies H_t
  real-rooted for t >= Delta^2/2) is what the historical citations
  attribute to Theorem 13; it is confirmed against the original text in
  `THEOREM13.md` section 1 and, independently and in typeset form, by
  Newman-Wu Theorem 7 above.

## Standing risks: two sources bearing on this claim were not read

### 1. Bombieri and Ghosh 2011: read in full, risk closed, verdict mixed

E. Bombieri and A. Ghosh, *Around the Davenport-Heilbronn function*, Uspekhi
Mat. Nauk 66:2 (2011), 15-66 = Russian Math. Surveys 66:2 (2011), 221-270,
DOI 10.1070/RM2011v066n02ABEH004740. Fifty pages, both authors at the IAS,
devoted to this single function. Cited by Righetti (arXiv:1506.05716) and by
Nakamura-Pankowski (arXiv:1909.08301). It was **absent from the original
sweep**, which is a gap in that sweep and not a finding about the source. It
was recorded here for part of 2026-08-16 as unreadable and therefore as a
standing risk; that is no longer true. The full English translation is free
at mathnet.ru under the id `rm9410`, and it was retrieved and read in full
the same day. The reading, the retrieval route, the verbatim quotes and two
verification legs are in `BOMBIERI-GHOSH.md`. The verdict has two halves and
they point in opposite directions.

**On `Lambda_DH`: closed, in the hunt's favour.** The paper contains zero
occurrences of Bruijn, Newman, heat, Polya, Turan, Lambda or deformation, in
the text and in all 28 references. Nothing in it bears on the de
Bruijn-Newman constant, on `H_t`, or on the backward heat flow. **The
novelty sentence below needs no change on account of this source.**

**On `sigma_0`: closed, against the hunt.** The decimal
`1.39513615823510972...` is not in the paper (digit searches for `1.395`,
`1.39`, `1.3951`, `0.2840`, `2.4779` all return nothing), but a *sharper and
exact* value of the quantity `sigma_0` bounds is. Their section 5 defines
`sigma(xi, q)` as the least upper bound of the real parts of the zeros, their
Theorem 7 determines it as the root of
`sum_{p = 2,3 mod 5} arctan(p^{-sigma}) = pi/2 - |theta|` with `xi = tan
theta`, and their section 6 evaluates it for this hunt's function:

> For the Titchmarsh value `tau_+ = -phi + sqrt(1 + phi^2)` we find
> ... `sigma(tau_+, 1) = 1.120362`.

Their `tau_+` is this hunt's `kappa`, agreeing to 34 digits. So the exact
strip abscissa for the Davenport-Heilbronn function has been in print since
2011 and is smaller than `sigma_0 = 1.395136...`, which is a
triangle-inequality upper bound on it. **`sigma_0` must not be described as a
new number**, and the sentence below and its footnote are worded so that they
do not depend on it being one. What survives is the derivation, not the
quantity: an enclosure-carrying elementary route to a bound on a constant
that Bombieri and Ghosh had already determined by Bohr-Kronecker theory.

**And it hands the hunt a better upper bound, by citation.** Feeding
`sigma(tau_+, 1)` into the same de Bruijn / Newman-Wu engine gives
`Delta = 0.620362...` and

    Delta^2/2 = 0.192424814576128011   (narrow, Stopple / this hunt)
              = 0.769699258304512045   (wide, Dobner / Polymath 15)

a factor 2.082 better than 0.4006. That improved bound is **cited plus
measured, not decided**: their 1.120362 is a six-decimal value and their
Theorem 7 rests on machinery this tree has not verified. The decided headline
therefore stays 0.4006343708899557, with the sharper number quoted as an
improvement available from the literature. Do not silently swap it in.

### 2. academia.edu preprint 166936409, the one source still unread

Not read: Cloudflare challenge on direct fetch, r.jina.ai 401, Wayback CDX
blocked by egress policy. The search index yielded its full title,

> Off-Line Zeros of the Riemann xi-Function: A Constraint Network, an Exactly
> Solvable Collision Model, Explicit Frozen-Field Bounds, a Lifetime-Deficit
> Dictionary for Weil Positivity, and an Interference-Channel Negative Control

and enough abstract fragments (recorded in
`attack_adversary5_priorart.md` section 2) to establish that its subject is
the Riemann xi function and the classical wide-frame Lambda, with its
headline numbers 0.4233 and 0.4305 stated against the anchor 1/2, and that
Davenport-Heilbronn enters three times as instrument rather than as subject.
One of those three is a set of "measured lifetimes" of DH off-line zeros
under this same backward flow, and a lifetime is the quantity
`hunts/flow_repair/` calls a landing time, so that preprint may contain,
implicitly, a **float-grade lower bound** on Lambda_DH for the two lowest DH
off-line zeros. It names no Lambda_DH and gives no upper bound. This hunt's
floor comes from the pair-5 site near Re z = 240.4 and is decided rather than
measured, which is a different grade, but the caveat stands until someone
reads it. Its provenance could not be determined from inside this checkout;
a search of all tracked files and all of `git log --all` for its distinctive
vocabulary returned nothing outside this file.

## Also surfaced by the prior-art adversary, not threats

- **`sigma* = 2.3822861089...` for the sibling function** `f(s, tau_-)` with
  `tau_- = -1/kappa = -3.5201470213402019924...`, the *other* root of the
  same quadratic. Righetti (arXiv:1506.05716) quotes it; **the constant is
  Bombieri and Ghosh's**, their `sigma(tau_-, 1)` in the same section 6 table
  as `sigma(tau_+, 1)`, and this file's earlier attribution of it to Righetti
  is corrected here (see `BOMBIERI-GHOSH.md` section 5.1). It is a different
  constant for a different member of the family, and it is not the
  coefficient-domination abscissa for that function either, which is
  2.477958026532674935112887. A reader will meet all three numbers together,
  so name them and say which is which.
- **Bucur, Ernvall-Hytonen, Odzak and Smajlovic**, *On a Li-type criterion
  for zero-free regions of certain Dirichlet series with real coefficients*,
  LMS J. Comput. Math. (2016), whose abstract names the Davenport-Heilbronn
  zeta function explicitly. No heat flow, no de Bruijn-Newman constant.
- The quantity `sigma_0` bounds is a **classical named object**: the least
  upper bound `sigma*` of the real parts of the zeros of a Dirichlet series,
  finite by Titchmarsh, *Theory of Functions* section 9.41 (cited by
  Righetti; not read directly here). `STRIP.md` should say so in one line.
- **Michalowski**, arXiv:2602.20313, works the same kernel with 80-digit
  outward-rounded interval arithmetic and no DH and no Lambda bound, so no
  collision; worth reading as a cautionary neighbour, since its version 2
  withdraws a version 1 global sign claim "because the derivative-tail
  enclosure was unsound", which is the failure mode this hunt's tail bounds
  are exposed to.

## Searches run (2026-08-15/16)

"de Bruijn-Newman" + "Davenport-Heilbronn"; "de Bruijn-Newman" + Epstein;
Newman's conjecture Dirichlet L-functions (Stopple; ACM; CMMRSY); Ki-Kim-Lee
upper bound; CNV/Odlyzko lower-bound history; "Davenport-Heilbronn" + heat
flow / backward heat; de Bruijn 1950 Theorem 13; Odzak-Smajlovic Li
coefficients for DH-class functions; arXiv 2023-2026 sweeps for DH zeros;
Dobner full text; Newman-Wu full text; Gritsenko 2017; arXiv:2602.20313
(Polya frequency order of the zeta kernel, 2026, evidence the niche is
active). Added in the 2026-08-16 revision: Stopple full text at source;
Dobner's forward citations (Semantic Scholar only, five records, none
computing Lambda_F for any member of S#; OpenAlex could not be used as a
cross-check because it now meters by budget and returned HTTP 429 with zero
daily allowance, so that sweep is **single-source** and should be repeated
by a human with Google Scholar or MathSciNet); Saias-Weingartner,
Booker-Thorne, Nakamura-Pankowski, Balanzario-Sanchez-Ortiz, Ferry-Ghisa-
Muscutar; digit searches for 1.39513, 1.3951361, 0.8951, 0.895136.
**No publication was found attaching any number, or any heat-flow
computation, to the de Bruijn-Newman constant of DH or of any RH-violating
function.**

## The sentence

> *Superseded.* The original deliverable sentence was: "The sanctioned
> phrasing is: first quantitative two-sided bounds for the de Bruijn-Newman
> constant of an RH-violating L-function." Four things are wrong with it.
> **"L-function"** is the wrong noun: the Davenport-Heilbronn function has no
> Euler product, which is the entire reason it can violate its own Riemann
> hypothesis and why Dobner needs the *extended* Selberg class; the careful
> literature says "the Davenport-Heilbronn zeta function" (Bucur et al.),
> "the Davenport-Heilbronn function" (Bombieri-Ghosh) or "a Dirichlet series
> satisfying a Riemann-type functional equation" (Nakamura-Pankowski).
> **"First quantitative"** is false: Stopple has an unconditional
> quantitative bound on a non-zeta constant of exactly this type, and
> Newman-Wu compute one exactly (`ln 2`) for a measure. **"Two-sided"**
> without a domain restriction is false for the same reason. And the
> sentence carried **no frame**, while the number it names is
> frame-dependent by a factor of 4.

The sentence, as adopted:

> So far as the literature search recorded in `NOVELTY.md` reaches, these are
> the first quantitative bounds, from either side, on the de Bruijn-Newman
> constant of a Dirichlet series with a Riemann-type functional equation
> whose Riemann hypothesis is false. They are stated in the normalization of
> Stopple (arXiv:1301.3158), in which
> `Phi(u) = 4 sum_n a_n n exp(3u/2 - pi n^2 e^{2u}/5)`, and are four times
> smaller than the same constant in the normalization of Newman,
> Rodgers-Tao, Polymath 15 and Dobner.

The footnote, which is mandatory and is not to be compressed:

> Existence, finiteness and nonnegativity of this constant are Dobner's
> (Acta Arith. 2021), for all of the extended Selberg class, with no member
> named and no number given. The upper bound is de Bruijn's 1950
> strip-contraction theorem, restated as Theorem 7 of Newman and Wu (Bull.
> AMS 57, 2020), applied to a zero strip computed here; the mechanism is
> published and surveyed. The strip constant is not new either: Bombieri and
> Ghosh, *Around the Davenport-Heilbronn function*, Russian Math. Surveys 66
> (2011), 221-270, section 6, determine the least upper bound of the real
> parts of the zeros of this very function exactly, `sigma(tau_+, 1) =
> 1.120362`, which is sharper than the elementary
> `sigma_0 = 1.39513615823510972...` derived here. What this work supplies on
> the upper side is an enclosure-carrying elementary derivation of a weaker
> bound on that same quantity, and the assembly of the two sides into a
> strictly positive bracket. Quantitative bounds on de Bruijn-Newman
> constants of objects other than zeta are not new: Stopple bounds
> `Lambda_Kr` for quadratic Dirichlet L-functions from below unconditionally
> (`-1.12929e-7 < Lambda_Kr`) and from above under GRH, and Newman and Wu
> determine such a constant exactly (`ln 2`) for a three-atom measure. The
> qualifier that carries the claim is that the object here violates its own
> Riemann hypothesis. Bombieri and Ghosh was read in full on 2026-08-16
> (`BOMBIERI-GHOSH.md`) and contains no de Bruijn-Newman or heat-flow content
> of any kind. One source bearing on the claim is still unread: academia.edu
> preprint 166936409, which measures survival times of Davenport-Heilbronn
> off-line zeros under this same flow and so may contain, implicitly, a
> float-grade lower bound. One sweep is also single-source: the
> forward-citation search on Dobner ran on Semantic Scholar alone, because
> OpenAlex returned HTTP 429 with no daily allowance, and it should be
> repeated against Google Scholar or MathSciNet.

If one line is needed rather than a paragraph, the safe short form is:

> First quantitative two-sided bounds on the de Bruijn-Newman constant of a
> function that violates its own Riemann hypothesis, in Stopple's
> normalization, subject to two named unread sources.

Do not use "L-function". Do not drop "so far as the search reaches". Do not
drop the frame.
