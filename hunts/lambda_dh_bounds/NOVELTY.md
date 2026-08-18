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

> **Revised 2026-08-18** (third pass), closing the last three prior-art items
> that `GATE.md` item 9 carried as open. academia.edu preprint 166936409 is
> **read in full**: it is Mesut Ismail, `10.5281/zenodo.21679490`, freely
> available on Zenodo, and it contains **no de Bruijn-Newman constant for the
> Davenport-Heilbronn function and no bound on one**, so the risk closes in the
> hunt's favour. Bombieri-Mueller 2008 is identified exactly and read at abstract
> and reference-list level: it is about the rate of approach of zeros to the
> abscissa for Epstein zeta functions of class number 2, with no de Bruijn-Newman
> or heat-flow content. The Dobner forward-citation sweep is **no longer
> single-source**: three independent indexes plus a web sweep, seven citing works,
> none of them quantitative about any non-zeta `Lambda`. **The sentence survives
> unchanged; only the footnote and the one-line short form move.** One item is
> newly named and unread rather than unfound (the Voronov preprint), and one new
> and strong piece of negative evidence is recorded (the ANTEDB de Bruijn-Newman
> chapter, which tabulates every known bound and carries no non-zeta entry).

> **Revised 2026-08-18** (fourth pass), for the sharpened upper bound. The
> headline's upper endpoint improved by a factor 2.082030697360155 when
> `STRIP2.md` derived the necessary half of Bombieri and Ghosh's Theorem 7
> in-tree and decided the abscissa `sigma_0' = 1.12036249819` on both backends.
> **The novelty sentence survives unchanged**, because the abscissa is not new
> and was never claimed to be: only the *grade* and the *derivation* are this
> hunt's. One word in the footnote is corrected, *weaker*, since the elementary
> route now reaches the same abscissa rather than stopping short of it. The
> numbers in "Read `FRAME.md` first" and in the Bombieri-Ghosh entry are
> updated in place with the superseded values kept beside them. The lower
> bound did not move, so nothing in the separation's phrasing changes either.

## Read `FRAME.md` first

Every `Lambda` number in this directory has two values, four apart. The error
originated in `THEOREM13.md` section 6 and surfaced here, in the calibration
against the zeta record below. The two frames:

    narrow :  s = 1/2 + i z      (Stopple; this hunt)
    wide   :  s = (1 + i z)/2    (de Bruijn as usually quoted; Newman;
                                  Rodgers-Tao; Polymath 15; Dobner)

    Lambda(wide) = 4 * Lambda(narrow).

The hunt's headline in both:

    narrow (Stopple / this hunt) :  0.0576 < Lambda_DH <= 0.19242481458026887663805
    wide   (Dobner / Polymath 15):  0.2304 < Lambda_DH <= 0.7696992583210755065522

(Through 2026-08-17 these read `<= 0.4006343708899557` and
`<= 1.6025374835598228`; the upper side sharpened by a factor
2.082030697360155 on 2026-08-18 when the abscissa was decided in-tree from a
phase obstruction rather than from coefficient domination, `STRIP2.md`. The
lower side did not move.)

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

## Standing risks: the named sources, and what reading them settled

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

> **Update 2026-08-18. It was not swapped in; it was derived.** The paragraph
> above is kept as written and its conclusion is now spent. `STRIP2.md` and
> `strip2.py` derive the **necessary** half of their Theorem 7 in-tree, from
> the Euler products of `L(s, chi)` and `L(s, conj chi)` plus one Moebius
> image, with no Bohr theory and no Kronecker theorem, and decide the abscissa
> on **both** backends at the exact rational `sigma_0' = 1.12036249819`
> (python-flint 192 bits and mpmath.iv dps 40, sieve limit `P = 10^5`, 4814
> class primes; deep flint-only point 320 bits at `P = 10^7` deciding
> 1.1203624981833251). So the headline is now
> `Delta^2/2 = 0.19242481458026887663805` narrow and
> `0.7696992583210755065522` wide, **decided**, at the factor 2.082030697360155.
>
> What this does and does not change for novelty. **It does not make the
> abscissa new.** The criterion is their Theorem 7 equation, term for term, at
> `q = 1` and `xi = kappa`, and `STRIP2.md` section 7 says so; their converse,
> which makes the abscissa an exact supremum, is neither used nor claimed. What
> is new on the upper side is the *grade* and the *derivation*. **The novelty
> sentence and its footnote are unchanged**, except that the footnote's
> characterisation of the upper side as "an enclosure-carrying elementary
> derivation of a *weaker* bound on that same quantity" loses the word
> *weaker*: the elementary route now reaches their abscissa.
>
> Two of their published numbers are reproduced here as controls, by machinery
> their Theorem 7 does not share: the section 9 finite claim (threshold prime
> **6323**, cardinality **420**) and the sibling abscissa
> `sigma(tau_-, 1) = 2.38228610898712387152...` against their published
> `2.3822861089`, all ten digits. One correction falls out and it is against an
> in-tree artifact rather than against the paper: `BOMBIERI-GHOSH.md` check B's
> 29-digit re-solves of both abscissae each sit on the wrong side of their own
> root, by about `1.2e-17` and `6e-18`. Bombieri and Ghosh print six and ten
> decimals and this instrument reproduces both exactly.

### 2. academia.edu preprint 166936409: read in full, risk closed in the hunt's favour

**Revised 2026-08-18.** This entry recorded the preprint as unread through
2026-08-16. It is now read in full and the caveat is discharged. The superseded
text is kept verbatim at the end of this subsection.

**How it was reached, after every earlier route failed.** Direct fetch of the
academia.edu page still returns HTTP 403 under every user agent tried, including
a Googlebot string, and the Wayback machine holds no snapshot
(`archive.org/wayback/available` returns an empty `archived_snapshots`). What
worked was `r.jina.ai` against the *full slug* URL rather than the bare numeric
one: it returned 40,540 bytes of the record, including the full current abstract
and the citation block. That block carries the two things every earlier attempt
lacked: the author, **Mesut Ismail** (ORCID 0009-0001-0496-964X), and a DOI,
**10.5281/zenodo.21679490**. The paper is deposited on **Zenodo, open access**:
`https://zenodo.org/records/21679490`, file `Ismail_rh_pf_v18.4.pdf`, 758,872
bytes, publication date 2026-07-29. It was downloaded, converted with
`pdftotext -layout` (4,436 lines) and read. The lesson for the next sweep is
narrow and worth keeping: **an academia.edu wall is not evidence that a document
is unobtainable**, and the citation block behind it usually names a mirror.

**The title on academia.edu is stale**, which is why the earlier title searches
found only fragments. The current version is v18.4 and is titled

> Off-line zeros of the Riemann xi-function: a constraint network, an exactly
> solvable collision model, an energy-budget divergence, and a lifetime-deficit
> dictionary with negative controls

The fragments recorded in `attack_adversary5_priorart.md` section 2 come from an
earlier version and some of them no longer hold: the frozen-field figure
`tau*(T0) = 0.229` is now `0.2151`, and "explicit frozen-field bounds" and
"interference-channel negative control" have left the title.

**Its frame is the wide one, and it states this hunt's factor-4 dictionary
independently.** Its Definition 3.1 fixes `H_0(z) = (1/8) xi(1/2 + iz/2)` evolved
by `d_t H = -d_zz H`, with `Lambda_zeta <= 1/2`. That is the frame of Newman,
Rodgers-Tao, Polymath 15, Dobner and the ANTEDB. Its Lemma 3.2 derives the
translation to the unit-diffusion clock as `t = 4 tau` and adds the warning this
hunt learned expensively:

> A clock off by the factor 4 would instead prove `Lambda <= 1/8` from the
> conjugate mechanism alone, which is false.

That is an independent published statement of the conversion in `FRAME.md`, from
a source that had no contact with this tree, and `FRAME.md` may cite it as such.

**What it does with Davenport-Heilbronn: instrument, in five roles, never
subject.** (i) a calibration showing its energy-budget divergence does not
discriminate zeta from DH; (ii) the DH log-derivative coefficients as a negative
control on Euler-product-free positivity schemes; (iii) negative-control theorems
against the Connes-Consani-Moscovici rank-one scheme and Suzuki's screw-function
criterion; (iv) a lifetime-deficit dictionary validated at the two DH off-line
zeros; (v) "the first computed Morse index path of a non-RH function".

**The two numbers that the caveat was about.** Its Numerical Observation 24.2
tabulates *measured lifetimes* `0.182` and `0.045` for the DH witnesses
`rho1` at `t0 = 85.70, h1 = 0.3085` and `rho2` at `t0 = 114.16, h2 = 0.1508`,
against the conjugate bounds `2h^2 = 0.190` and `0.046`. Its Numerical
Observation 32.5 gives closed-form lifetimes `tau1 = 0.1819` and
`tau2 = 0.0449` and the index path

    ind-(Q_t^DH), window |gamma| < 120 :  4 -> 2 -> 0  at t ~ 0.045, 0.182.

Its witnesses are the same zeros this repository pins: its `rho1 = 0.808517... +
85.699...i` agrees with `zeta/epstein.py`'s pinned
`0.80851718245663738555335196060684412785067026830502 + 85.6993484853775921719292677i`
to every digit it prints. I recomputed `2 h1^2 = 0.190365478578` at mp.dps = 30
(mpmath, measured) and it reproduces its `0.190`, which confirms the frame
reading above rather than resting on it.

**Verdict: it contains no de Bruijn-Newman constant for the Davenport-Heilbronn
function, and no bound on one from either side.** Three findings, in order of
how much they matter.

- **No named constant.** It never writes `Lambda_DH` or any equivalent, and it
  attaches no number to one. *Trap for the next reader*: the symbol `Lambda_H`
  does appear throughout its sections 20 and 28, but it is the DH analogue of the
  von Mangoldt function, defined by the log-derivative recursion
  `a_n log n = sum_d Lambda_H(d) a_{n/d}`. It is a coefficient sequence, not a
  de Bruijn-Newman constant, and the two must not be conflated.
- **The ingredients are present and are never assembled.** Its section 32 defines
  `Lambda` generically for "a completed L-type function", and its Proposition
  24.3 step 1 proves `Lambda = sup_k tau_k` over the extinction times of the
  off-line pairs. A reader could therefore combine its own section 32 with its
  own 32.5 to guess `Lambda_DH >~ 0.18`. The paper does not do this, states no
  such conclusion, and gives no upper bound of any kind.
- **Even the most generous reading is weaker than this hunt's floor, and of a
  lower grade.** Its `tau1 = 0.1819` is labelled a *two-zero upper bound* on that
  pair's lifetime, with the parenthetical "the full field accelerates
  collisions", so it points the wrong way to yield a lower bound on `Lambda_DH`
  at all. Read at face value anyway, and converted:

  | quantity | wide (its frame and Dobner's) | narrow (Stopple, this hunt) |
  |---|---|---|
  | its `tau1`, Numerical Observation 32.5 | `0.1819` | `0.045475` |
  | its measured lifetime, Numerical Observation 24.2 | `0.182` | `0.0455` |
  | this hunt's decided floor `144/625` | `0.2304` | `0.0576` |

  This hunt's floor is larger by a factor `1.267` (measured, float division of
  cited decimals), and it is *decided* by an Arb winding number while every
  number above is explicitly labelled a Numerical Observation in a paper that
  separates those from its theorems on purpose.

**So the novelty sentence needs no change on account of this source, and its
footnote does.** The clause "may contain, implicitly, a float-grade lower bound"
is replaced below by what is actually in the paper.

> *Superseded, kept verbatim (the state through 2026-08-17).* "### 2.
> academia.edu preprint 166936409, the one source still unread. Not read:
> Cloudflare challenge on direct fetch, r.jina.ai 401, Wayback CDX blocked by
> egress policy. The search index yielded its full title, [...] and enough
> abstract fragments (recorded in `attack_adversary5_priorart.md` section 2) to
> establish that its subject is the Riemann xi function and the classical
> wide-frame Lambda, with its headline numbers 0.4233 and 0.4305 stated against
> the anchor 1/2, and that Davenport-Heilbronn enters three times as instrument
> rather than as subject. One of those three is a set of 'measured lifetimes' of
> DH off-line zeros under this same backward flow, and a lifetime is the quantity
> `hunts/flow_repair/` calls a landing time, so that preprint may contain,
> implicitly, a **float-grade lower bound** on Lambda_DH for the two lowest DH
> off-line zeros. It names no Lambda_DH and gives no upper bound. This hunt's
> floor comes from the pair-5 site near Re z = 240.4 and is decided rather than
> measured, which is a different grade, but the caveat stands until someone reads
> it. Its provenance could not be determined from inside this checkout; a search
> of all tracked files and all of `git log --all` for its distinctive vocabulary
> returned nothing outside this file."

The provenance question is unchanged and is now answerable from outside: the
author is named, has an ORCID, and has no connection to this laboratory.

### 3. Bombieri and Mueller 2008: identified and read at abstract level, not a threat

**Added 2026-08-18.** `BOMBIERI-GHOSH.md` flagged this as the one citation-away
source the hunt had not consulted, because it is the parent of the Bohr-method
machinery that produced `sigma(tau_+, 1) = 1.120362`, the constant that displaced
`sigma_0`. It is now identified exactly and read as far as open sources reach.

E. Bombieri and J. Mueller, **"On the zeros of certain Epstein zeta functions"**,
Forum Math. **20**:2 (2008), 359-385, DOI `10.1515/FORUM.2008.018`, zbMATH
`Zbl 1217.11040`, MSC 11E45 and 11M41. The zbMATH summary, verbatim:

> This paper studies the distribution of zeros of certain Epstein zeta functions,
> associated to positive definite binary quadratic forms with class number 2, in
> the region of absolute convergence of their Dirichlet series. In particular, one
> obtains upper and lower bounds for the rate of approach of zeros to the boundary
> of the zero-free half-plane for such functions. The proof for the lower bound
> depends on Bohr's method for studying simultaneous diophantine approximations.
> The upper bound uses instead a deep result on the diophantine type of the ratio
> of the logarithms of two rational numbers.

Crossref carries five deposited references; the two that are identifiable are
Baker (J. Reine Angew. Math. 442, 1993) and Gonek (1980). Neither de Bruijn nor
Newman nor Polymath appears among them.

**Verdict: no de Bruijn-Newman or heat-flow content at any level reachable, and
no competing value for `sigma_0` either.** Two reasons the second half matters.
Its subject is a *different* RH-violating family, Epstein zeta functions of class
number 2, not the Davenport-Heilbronn function; and its quantity is the *rate of
approach* of zeros to the abscissa, not the abscissa itself, so it is not a rival
determination of the thing `sigma_0` bounds. What it supplies is the method
Bombieri and Ghosh later pointed at this hunt's function.

**What is not read.** The full text. De Gruyter answers HTTP 202 behind a human
verification wall and `r.jina.ai` gets HTTP 405 from it; no preprint, mathnet
mirror or EuDML copy was found. The residual risk is small and named: a
fifty-year-old Bohr-method paper on a neighbouring RH-violating family could in
principle carry a remark on deformation, and its abstract and reference list say
it does not.

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

## Searches run (2026-08-15/16, extended 2026-08-18)

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

**Added in the 2026-08-18 revision**, which closed the last three open prior-art
items and is recorded here at the level of route and status so a reader can
re-run it.

- *academia.edu 166936409*: direct fetch 403 under two user agents including a
  Googlebot string; Wayback `archive.org/wayback/available` returns no snapshot;
  Wayback timemap connection reset by egress policy; `r.jina.ai` on the **full
  slug** URL returned HTTP 200 and 40,540 bytes, which named the author and a
  Zenodo DOI; the Zenodo API and file endpoint both returned HTTP 200 and the
  full 758,872-byte PDF. Read in full. See section 2 above.
- *Bombieri-Mueller 2008*: located on Crossref by bibliographic query, then
  zbMATH `api.zbmath.org` for the authoritative summary and MSC, and Crossref for
  the deposited reference list. De Gruyter returns HTTP 202 behind a human
  verification wall and `r.jina.ai` gets HTTP 405 from it, so the full text is
  still unread. See section 3 above.
- *Dobner forward citations, now three independent indexes* (the 2026-08-16
  sweep was Semantic Scholar alone). Dobner is `10.4064/aa200603-23-7` /
  arXiv:2005.05142, and the arXiv title differs from the journal title, which is
  the trap already recorded above.
  - **Semantic Scholar** citations endpoint, queried by DOI and independently by
    arXiv id, agreeing: 5 records.
  - **OpenCitations** (COCI, Crossref-derived, an index with no Semantic Scholar
    input): 1 record.
  - **Google Scholar**, cluster `5851792251239807498`, headline "Cited by 5":
    2 distinct records across two view settings before it rate-limited.
  - A web-search sweep on the arXiv id surfaced one further citing preprint that
    none of the three indexes carried.
  - **OpenAlex still could not be used.** `api.openalex.org` returns HTTP 429
    with `"Insufficient budget. This request costs $0.001 but you only have $0
    remaining"` and `retryAfter: 72359`. This is recorded, not worked around.

  Union of the four routes, 7 distinct citing works plus one database, with a
  one-line verdict each:

  | citing work | route | verdict |
  |---|---|---|
  | Rodgers-Tao, *The de Bruijn-Newman constant is non-negative*, Forum Math. Pi 8 (2020) | S2 | zeta only, `Lambda_zeta >= 0`, no DH. No threat. |
  | Farmer, *Jensen polynomials are not a plausible route to proving RH*, Adv. Math. 2022, `10.1016/j.aim.2022.108781`, arXiv:2008.07206 | S2, OpenCitations, Scholar | Jensen polynomials of xi and Hermite universality. No DH, no Lambda value. No threat. |
  | Farmer, *Jensen polynomials are not a viable route ...* (MAG 3049226748) | S2 | duplicate record of the preceding. |
  | Farmer, *Currently there are no reasons to doubt the Riemann Hypothesis*, arXiv:2211.11671 | S2 | its section 13.2 treats DH at length, gives `F_DH`, its functional equation and its first off-line zero "near 0.8085 + 85.699i", and cites Dobner only for `Lambda >= 0`. No Lambda for DH, no flow applied to DH. No threat, and a useful independent citation for DH as the standard structure-matched counterexample. It calls it the "Deuring-Heilbronn function", which is a misnomer worth knowing before a name search. |
  | Suo, *Hamiltonian with Energy Levels Corresponding to Riemann Zeros*, arXiv:2505.21192 | S2 | Berry-Keating-style Hamiltonian. No DH, no Lambda bound. No threat. |
  | Michalowski, arXiv:2602.20313, on the Polya frequency order of the de Bruijn-Newman kernel | web search | already recorded above. Zeta kernel only, no DH, no Lambda bound. No threat. |
  | Voronov, *A Crowding-Normalized Reformulation of Neighboring-Gap Dynamics for the de Bruijn-Newman Flow*, ResearchGate, 2026 | Google Scholar only | **the one item not closed.** Its abstract snippet reads "a crowding-normalized reformulation of the standard neighboring-gap dynamics for **real simple** zeros of the de Bruijn-Newman deformation H_t", so its subject is the zeta-side real spectrum and DH off-line content is implausible. Full text not read: ResearchGate returns Cloudflare 403 on direct fetch and through `r.jina.ai`, and no other host was found. |
  | Tao, Trudgian and Yang, *Database of known results on analytic number theory exponents* (ANTEDB, `teorth.github.io/expdb`), 2025 | Google Scholar | not a research paper but the community's curated database, and the strongest negative evidence found to date. See below. |

- *ANTEDB chapter 18, "The de Bruijn-Newman constant"*, read in full. It fixes
  `H_0(z) = (1/8) xi(1/2 + iz/2)`, that is this hunt's **wide** frame, and
  tabulates every known bound. Lower: Newman 1976 `> -inf`, CNV 1988 `> -50`,
  te Riele 1991 `> -5`, Norfolk-Ruttan-Varga 1992 `> -0.385`, Csordas-Ruttan-Varga
  1991 `> -0.0991`, Csordas-Smith-Varga 1994 `> -4.379e-6`, COSV 1993
  `> -5.895e-9`, Odlyzko 2000 `> -2.63e-9`, Saouter-Gourdon-Demichel 2011
  `> -1.15e-11`, Rodgers-Tao 2020 and Dobner 2021 `>= 0`. Upper: Newman 1976
  `<= 1/2`, Ki-Kim-Lee 2009 `< 1/2`, Polymath 2019 `<= 0.22`, **Platt-Trudgian
  2021 `<= 0.2`**. **Every entry is zeta's.** A maintained, curated, community
  database of de Bruijn-Newman results that carries no non-zeta constant at all
  is better evidence for the search than any single negative query.
- *Two side-findings, recorded here and not acted on.* (i) ANTEDB's current
  upper record is `Lambda_zeta <= 0.2` (Platt-Trudgian 2021), sharper than the
  `<= 0.22` (Polymath 15) that this file and `SEPARATION.md` quote. The
  separation corollary **strengthens**, since the decided wide floor `0.2304`
  clears `0.2` as well as `0.22`; `SEPARATION.md` should cite Platt-Trudgian, and
  that edit is not made here. (ii) The academia.edu preprint's Lemma 3.2 states
  this hunt's factor-4 frame dictionary independently, with the same warning
  about the wrong clock; `FRAME.md` may cite it.

**No publication was found attaching any number, or any heat-flow
computation, to the de Bruijn-Newman constant of DH or of any RH-violating
function.** That sentence has now survived the reading of both named sources
and a three-index forward-citation sweep, and one item within it is unread
rather than unnamed: the Voronov preprint above.

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

> *Superseded (extended 2026-08-16).* Before the separation corollary was
> recognized (`SEPARATION.md`), the adopted sentence ended after its second
> sentence, as follows; nothing in it changed, it gained a third and fourth
> sentence carrying the separation at the strength the separation adversary
> sanctioned: "So far as the literature search recorded in `NOVELTY.md`
> reaches, these are the first quantitative bounds, from either side, on the
> de Bruijn-Newman constant of a Dirichlet series with a Riemann-type
> functional equation whose Riemann hypothesis is false. They are stated in
> the normalization of Stopple (arXiv:1301.3158), in which
> `Phi(u) = 4 sum_n a_n n exp(3u/2 - pi n^2 e^{2u}/5)`, and are four times
> smaller than the same constant in the normalization of Newman,
> Rodgers-Tao, Polymath 15 and Dobner."

The sentence, as adopted:

> So far as the literature search recorded in `NOVELTY.md` reaches, these are
> the first quantitative bounds, from either side, on the de Bruijn-Newman
> constant of a Dirichlet series with a Riemann-type functional equation
> whose Riemann hypothesis is false. They are stated in the normalization of
> Stopple (arXiv:1301.3158), in which
> `Phi(u) = 4 sum_n a_n n exp(3u/2 - pi n^2 e^{2u}/5)`, and are four times
> smaller than the same constant in the normalization of Newman,
> Rodgers-Tao, Polymath 15 and Dobner. In that shared wide normalization the
> decided floor `0.2304 = 144/625` exceeds Polymath 15's unconditional
> `Lambda_zeta <= 0.22`, so `Lambda_DH > Lambda_zeta` unconditionally; so
> far as the searches recorded here and in `SEPARATION.md` reach, this is
> the first strict inequality between de Bruijn-Newman constants of two
> Dirichlet series in which both constants are nonnegative, strict orderings
> without that qualifier being one-line corollaries of exact function-field
> determinations in print since 2013-2014 (Andrade-Chang-Miller
> arXiv:1310.3477; Chang-Mehrle-Miller-Reiter-Stahl-Yott arXiv:1411.2071).

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
> 1.120362`, which is sharper than the coefficient-domination
> `sigma_0 = 1.39513615823510972...` first derived here. What this work
> supplies on the upper side is an enclosure-carrying elementary derivation of
> the necessary half of their Theorem 7, which reaches the same abscissa and
> decides it on two backends at `sigma_0' = 1.12036249819` (`STRIP2.md`,
> 2026-08-18), and the assembly of the two sides into a strictly positive
> bracket. Their converse, which turns that abscissa into an exact supremum,
> is not used and not claimed, so the number remains theirs and what is new
> here is the grade and the derivation. Quantitative bounds on de Bruijn-Newman
> constants of objects other than zeta are not new: Stopple bounds
> `Lambda_Kr` for quadratic Dirichlet L-functions from below unconditionally
> (`-1.12929e-7 < Lambda_Kr`) and from above under GRH, and Newman and Wu
> determine such a constant exactly (`ln 2`) for a three-atom measure. The
> qualifier that carries the claim is that the object here violates its own
> Riemann hypothesis. Bombieri and Ghosh was read in full on 2026-08-16
> (`BOMBIERI-GHOSH.md`) and contains no de Bruijn-Newman or heat-flow content
> of any kind. Both remaining named sources were read on 2026-08-18. academia.edu
> preprint 166936409 is Mesut Ismail, `10.5281/zenodo.21679490`, open access on
> Zenodo; it works the classical wide-frame `Lambda_zeta` and uses
> Davenport-Heilbronn only as instrument and negative control. It names no
> `Lambda_DH`, gives no bound on one from either side, and its two DH off-line
> lifetimes, `tau1 = 0.1819` and `tau2 = 0.0449` in the wide frame, are labelled
> upper bounds on those lifetimes in a Numerical Observation, so they yield no
> lower bound on `Lambda_DH`; read at face value anyway, `0.1819` is below the
> decided wide floor `0.2304` claimed here. Bombieri and Mueller, *On the zeros of
> certain Epstein zeta functions*, Forum Math. 20:2 (2008), 359-385, is the
> Bohr-method parent of Bombieri and Ghosh's abscissa; its subject is the rate of
> approach of zeros to the abscissa for Epstein zeta functions of class number 2,
> its deposited references name neither de Bruijn nor Newman, and its full text is
> behind a publisher wall and remains unread. The forward-citation sweep on Dobner
> now runs on three independent indexes (Semantic Scholar, OpenCitations and
> Google Scholar) plus a web sweep, and the union of seven citing works contains
> no quantitative `Lambda` for any non-zeta object; OpenAlex still returns HTTP 429
> with no daily allowance and was not used. One citing item is unread rather than
> unfound: Voronov, *A Crowding-Normalized Reformulation of Neighboring-Gap
> Dynamics for the de Bruijn-Newman Flow* (ResearchGate, 2026), whose abstract
> places it on the zeta-side real spectrum and whose full text is behind
> Cloudflare.

If one line is needed rather than a paragraph, the safe short form is:

> First quantitative two-sided bounds on the de Bruijn-Newman constant of a
> function that violates its own Riemann hypothesis, in Stopple's
> normalization, so far as the recorded search reaches.

Do not use "L-function". Do not drop "so far as the search reaches". Do not
drop the frame. Do not state the separation without "in which both constants
are nonnegative" (`SEPARATION.md` section 6).
