# Bombieri and Ghosh, *Around the Davenport-Heilbronn function*: read in full

**RISK STATUS: CLOSED, and it is a mixed verdict.**

The paper was retrieved and read in full this session (50 pages, complete English
translation, not an abstract or a fragment). The three questions the gate asked
have definite answers:

| question | answer |
|---|---|
| (i) does it contain `sigma_0` or an equivalent zero-strip abscissa for DH? | **The number `1.39513615823510972...` is NOT in it. But an equivalent, sharper and exact abscissa for the same function IS: `sigma(tau_+, 1) = 1.120362`.** |
| (ii) any de Bruijn-Newman or heat-flow content? | **None. Zero occurrences of de Bruijn, Newman, heat, Polya, Turan, Lambda or deformation, in the text and in all 28 references.** |
| (iii) anything else bearing on the hunt? | Yes: Righetti's `2.3822861089` is originally theirs, and DH zeros with `Re s > 1` are shown to be extremely rare. |

The short form: **the hunt's de Bruijn-Newman bracket is not anticipated, and the
novelty sentence survives untouched. The hunt's claim to own the zero strip does
not.** Bombieri and Ghosh determined the exact least upper bound of the real parts
of the zeros of the Davenport-Heilbronn function in 2011, and it is smaller than
this hunt's `sigma_0`. That is simultaneously bad news for the originality of
`sigma_0` and good news for the upper bound, which their constant improves by a
factor of 2.08.

---

## 1. Retrieval record

Earlier sessions recorded this source as unreadable ("IOPscience subscription,
mathnet.ru returned 503 on every attempt, no preprint or mirror found"). Two
things were wrong with that attempt, and both are worth recording so the route is
reproducible:

- **The mathnet identifier was wrong.** The tried URLs were `mi.mathnet.ru/umn9410`
  and `mi.mathnet.ru/eng/umn9410`. The paper's mathnet id is **`rm9410`**, not
  `umn9410` (`umn` is the Russian journal abbreviation, not the id namespace).
- **The host `mi.mathnet.ru` returns 503; `www.mathnet.ru` serves normally.**

The route that worked, in full:

```
https://www.mathnet.ru/eng/rm9410                                     (record page)
https://www.mathnet.ru/php/getFT.phtml?jrnid=rm&paperid=9410&what=fullteng&option_lang=eng
```

The second URL redirects to `https://www.mathnet.ru/links/86b2d05efd18c606e9f632710771a092/rm9410_eng.pdf`
and serves the **full English translation, free, no login**: 1,610,005 bytes,
`Pages: 50`, `Creator: LaTeX with hyperref`, `Author: E. Bombieri, A. Ghosh`,
title `Around the Davenport-Heilbronn function`. A Russian original PDF (1747 kB)
is at the same endpoint with `what=fullt&option_lang=rus`.

Text was extracted with `pdftotext -layout`. Everything quoted below is from that
extraction. Every other route confirmed the paper is otherwise closed: Unpaywall
reports `oa_status: closed`, `has_repository_copy: false`, `oa_locations: []`;
OpenAlex reports `is_oa: False`, `any_repository_has_fulltext: False`; Semantic
Scholar reports `openAccessPdf.status: CLOSED`. No sci-hub-style mirror was used
or needed.

The PDF is left in the session scratchpad and is deliberately **not committed**:
it is a copyrighted translation, and the retrieval route above is reproducible in
one command.

Bibliographic facts, confirmed against the article itself: Russian Math. Surveys
66:2 (2011), 221-270 = Uspekhi Mat. Nauk 66:2, 15-66; DOI
10.1070/RM2011v066n02ABEH004740; MSC Primary 11M41, 11M26, Secondary 11E45;
received 04.10.2010; dedicated to the memory of A. A. Karatsuba; bibliography of
28 titles. Both authors at the IAS at the time (Ghosh's affiliation is given as
Oklahoma State).

---

## 2. It is the same function, defined the same way

Section 5.1, verbatim:

> **5.1. The Davenport-Heilbronn series.** Let `xi` be a complex number and define
> the Dirichlet series `f(s, xi) = sum_{n>=1} a(n, xi) / n^s` where
> `a(n, xi) = 1` if `n = 1 mod 5`, `xi` if `n = 2 mod 5`, `-xi` if `n = 3 mod 5`,
> `-1` if `n = 4 mod 5`, `0` if `n = 0 mod 5`.

and, further down the same page:

> These series were introduced by Titchmarsh ([10], Chap. X, 10.25), who noted
> that for `xi = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1)` the function `f(s; xi)`
> satisfies the functional equation
> `(pi/5)^{-s/2} Gamma((1+s)/2) f(s; xi) = (pi/5)^{-(1-s)/2} Gamma((1+(1-s))/2) f(1-s; xi)`,
> which is analogous to the functional equation of Dirichlet series for an odd
> character mod 5, except for the fact that now the root number is 1. This
> function is usually called the Davenport-Heilbronn series. In what follows we
> will write `tau_+` for the above value of `xi`.

This is the hunt's object exactly: the same period-5 coefficient pattern
`(1, kappa, -kappa, -1, 0)`, the same gamma factor `(pi/5)^{-(s+1)/2} Gamma((s+1)/2)`,
the same root number 1. Their `tau_+` is the hunt's `kappa`. Measured, this
session, at dps 40:

```
tau_+ = -phi + sqrt(1 + phi^2)  with phi = (1+sqrt5)/2
      = 0.2840790438404122960282918323931261690911
repo   zeta.epstein kappa
      = 0.2840790438404122960282918323931265126188
difference = -3.4e-34   (the repo call's own precision, not a discrepancy)
```

They also name the *other* root, `tau_- = -phi - sqrt(1+phi^2) = -3.520147021340...`,
which they call "the second Davenport-Heilbronn function". That is Righetti's
function, and section 4 below settles who owns which constant.

---

## 3. Question (i): the zero-strip abscissa. The hunt's number is absent; a sharper one is present

### 3.1 What they define and prove

They define (section 5, p. 240):

> We define `sigma(xi, q)` to be the supremum of the numbers `sigma > 1` for which
> the series `sum_{(n,q)=1} a(n, xi) n^{-s}` vanishes at `s = sigma + it` for some
> `t` in `R`.

So `sigma(xi, 1)` is the **least upper bound of the real parts of the zeros of the
Davenport-Heilbronn function**. Righetti (arXiv:1506.05716) uses the same object
under the name `sigma*` and defines it in the same words, "the least upper bound of
the real parts of such zeros", which corroborates the reading.

They then prove it exactly. **Theorem 7**, verbatim:

> **Theorem 7.** 1) Suppose that `xi` is real. Then `sigma(xi, q)` is the value of
> `sigma > 1` satisfying the equation
> `sum_{p = 2,3 mod 5, (p,q)=1} arctan(p^{-sigma}) = pi/2 - |theta|`.

with `xi = tan(theta)`. The proof route is Bohr's method plus Kronecker's theorem,
legitimate here because `f(s, xi)` is a linear combination of exactly two
L-functions with Euler products (they flag this dependence explicitly in section
10). Section 6 evaluates the prime sum through `log L(., chi_0)` and
`log L(., chi_2)` decomposed into Hurwitz zeta functions.

### 3.2 The published value for the Davenport-Heilbronn function

Section 6, p. 246, verbatim:

> For the Titchmarsh value `tau_+ = -phi + sqrt(1 + phi^2)` we find
>
> `sigma(tau_+, 2) = 1.046712`, `sigma(tau_+, 3) = 1.063679`, `sigma(tau_+, 7) = 1.093482`,
> `sigma(tau_+, 13) = 1.106200`, ..., **`sigma(tau_+, 1) = 1.120362`**.

That is a published zero-strip abscissa for this hunt's function, fifteen years
old, and it is **sharper than `sigma_0`**:

```
B-G   sigma(tau_+, 1) = 1.120362...   exact least upper bound of Re rho
hunt  sigma_0         = 1.395136...   coefficient-domination upper bound on it
```

The two are not the same quantity. `sigma_0` solves `sum_{n>=2} |a_n| n^{-sigma} = 1`
and is an upper bound for the sup of real parts obtained by the triangle
inequality; `sigma(tau_+, 1)` *is* the sup of real parts. The hunt's number is a
cruder bound on the exact quantity Bombieri and Ghosh determined.

### 3.3 Digit searches, so the negative half is on the record

The strings `1.395`, `1.39`, `1.3951`, `0.2840`, `.28407` and `2.4779` return
**zero hits** in the full text. `sigma_0 = 1.39513615823510972106135889...` is not
in this paper, in any precision, and neither is the coefficient-domination
abscissa `2.477958...` for `tau_-`. The mechanism the keyword list advertised
("reciprocals of Dirichlet series, estimates of coefficients") is genuinely there,
but it is used for a different purpose: sections 3, 4 and 7 study the *growth and
distribution of the coefficients* `b_n` of `1/f(s)`, following Landau and Hille,
and relate `sup Re(rho)` to that growth (their Theorem 3 defines
`alpha(f) = sup Re(rho)`; their Corollary 6 gives
`sum_{n<=X} |b_n|^2 / n >> X^{2 sigma* - 1 + o(1)}`). They never write down the
elementary abscissa at which `sum_{n>=2} |a_n| n^{-sigma}` crosses 1.

**So the narrow reading of the risk is negative and the substantive reading is
positive.** The hunt did not duplicate a published decimal. It did compute, by a
weaker method, a bound on a quantity these authors published exactly.

### 3.4 Verification I ran

Two checks, both this session, both graded.

**Check A (independent, finite, exact arithmetic).** Section 9 makes a
self-contained claim that uses none of their Hurwitz-zeta machinery:

> The smallest such set `P` with this property [`sum_{p in P} arctan(p^{-1}) > pi/2`]
> consists of all primes `p = 2, 3 mod 5` with `p <= 6323`, so `|P| = 420`.

Recomputed by direct prime summation (sympy primes, mpmath dps 30), with no shared
code: threshold prime **6323**, cardinality **420**, both exact matches. Their
quoted `arctan(1/2) = 0.463648` and `arctan(1/3) = 0.321751` also match, and their
quoted prime-sum target `0.2767872` for `tau_-` reproduces as
`pi/2 - |arctan(tau_-)| = 0.276787179448522625754266365045`. **Grade: decided**
(finite exact prime set, integer answers).

**Check B (reproduction of their Theorem 7 root).** I solved their Theorem 7
equation by bisection at mpmath dps 30, evaluating the prime sum through
`arctan` expansion plus `sum_k mu(k)/k log L(ks, chi^k)` over the characters mod 5:

| quantity | this session | published | agreement |
|---|---|---|---|
| `sigma(0, 1)` | 1.06702646637238936888624138422 | 1.06702646637238... | all 14 published digits |
| `sigma(tau_+, 1)` | **1.12036249818332508773010350311** | 1.120362 | all 6 published digits |
| `sigma(tau_-, 1)` | 2.38228610898712386578711039387 | 2.3822861089... | all 10 published digits |
| Table 1 at `xi = 0.5` | 1.1806948814902260211555547198 | 1.180694 | all 6 published digits |
| Table 1 at `xi = 1.0` | 1.37507615661900702468621940366 | 1.375076 | all 6 published digits |
| Table 1 at `xi = 2.0` | 1.82527383347867394678095062654 | 1.825273 | all 6 published digits |
| Table 1 at `xi = 3.9` | 2.49569735868266109118068160622 | 2.495697 | all 6 published digits |

**Grade: measured, and honestly labelled a reproduction rather than an independent
route.** After running it I read their section 6 and found that their equation
(6.1) is the same decomposition I had used, so this check confirms their
arithmetic but not their method. Check A is the genuinely independent leg, and it
passed exactly.

---

## 4. Question (ii): no de Bruijn-Newman content, none at all

Case-insensitive counts over the full 50-page extraction:

```
Bruijn 0    Newman 0    heat 0    Polya 0    Turan 0
Lambda 0    deformation 0         zero-free 0
```

The 28-item bibliography contains no de Bruijn, no Newman, no Polya, no
Csordas-Norfolk-Varga, and nothing on entire functions of Laguerre-Polya type. It
runs Hamburger, Potter-Titchmarsh, Davenport-Heilbronn I and II, Cassels, Stark,
Bombieri, Selberg, Voronin, Titchmarsh, Karatsuba, Bombieri-Hejhal, Bohr,
Davenport collected works, Jessen-Tornehave, Borchsenius-Jessen, Gonek,
Bombieri-Mueller, Lee, Voronin, Karatsuba-Voronin, Voronin, Laurincikas, Landau
(twice), Hille (twice), Carlson.

**Nothing in this paper bears on `Lambda_DH`, on `H_t`, or on the backward heat
flow.** The hunt's headline result is not anticipated here, and the adopted
novelty sentence in `NOVELTY.md` needs no change on account of this source.

---

## 5. Question (iii): other things in it that bear on the hunt

**5.1 Righetti's `2.3822861089` is Bombieri and Ghosh's number.** It appears in
their section 6 as `sigma(tau_-, 1) = 2.3822861089...`, and their section 9 adds
that the extreme zero found in a search to height 10,000 is
`rho = 2.37474435 + 1649.8708285 i` among 2,479 zeros of `f(s, tau_-)` with
`Re rho >= 0.5`. `NOVELTY.md` currently attributes this constant to Righetti with
a note that he calls the function "of the Davenport-Heilbronn type studied by
Bombieri and Ghosh". The attribution should be corrected: the constant is theirs,
and Righetti is quoting it.

**5.2 Zeros of the Davenport-Heilbronn function with `Re s > 1` are very rare.**
Section 9 explains why, for `xi` small, such zeros are hard to find: reaching one
requires aligning the arguments of `p^{it}` near `0 mod pi` for hundreds of primes
simultaneously. For `xi = 0` they searched the rectangle
`1/2 <= sigma < 1.2`, `0 <= t < 10000`, found 5,358 zeros, and **found no zero with
real part greater than 1** (their Figure 4). They contrast this with `tau_-`, where
the required prime-sum margin is only `0.2767872` and such zeros are plentiful.
The Davenport-Heilbronn function proper (`tau_+`, prime-sum target `1.2940091`)
sits at the hard end of that spectrum. This is context the hunt should carry: the
strip `Delta` is set by zeros that are real but extraordinarily sparse, which is
consistent with `0.4006` (and even `0.19242`) being visibly loose against the
deepest measured DH zeros at `|Im z| = 0.347`, as `GATE.md` already notes.

**5.3 Zero counting on the critical line.** Section 2.1 surveys Voronin,
Karatsuba's `cT (log T)^{1/2 - eps}`, and reports that Selberg filled the gap to
`c T log T` in an unpublished 1998 IAS lecture, with `N_0(f; T) > c n^{-1} T log T`
for a combination of `n` Dirichlet L-functions. Relevant background for
`census.py`, not a threat to anything.

**5.4 They say what their method does not cover.** Section 10: their sharp results
depend on `f` being a linear combination of just two Euler products, and they note
that Davenport-Heilbronn and Landau already showed such combinations "always have
zeros with real part greater than 1". No claim in the hunt collides with this.

---

## 6. What this obliges the hunt to change

Recorded here; not yet applied to the other artifacts.

1. **`NOVELTY.md` must stop calling `sigma_0` a new number.** The current text says
   the "genuinely new numbers are the Davenport-Heilbronn zero-strip constant
   `sigma_0`" and that "the strip constant `sigma_0 = 1.39513615823510972...` is
   what this work supplies". Both sentences must go. The accurate replacement:
   Bombieri and Ghosh (2011) determine the least upper bound of the real parts of
   the zeros of this function exactly, `sigma(tau_+, 1) = 1.120362`, by their
   Theorem 7; the hunt independently derived a weaker elementary bound
   `sigma_0 = 1.395136...` on the same quantity, and the only thing the hunt's
   version has that theirs does not is an enclosure-carrying derivation at rung 2
   from a two-line triangle-inequality argument that does not invoke
   Bohr-Kronecker theory.

2. **The upper bound can be improved by a factor of 2.08, by citation.** Feeding
   their constant into the same de Bruijn Theorem 13 / Newman-Wu Theorem 7 engine:

   | strip input | `Delta` | `Delta^2/2` (narrow, Stopple) | `Delta^2/2` (wide, Dobner) |
   |---|---|---|---|
   | hunt `sigma_0 = 1.395136...` | 0.895136... | **0.400634370889955694...** | 1.602537483559822777... |
   | B-G `sigma(tau_+, 1) = 1.120362...` | 0.620362... | **0.192424814576128011...** | 0.769699258304512045... |

   ratio of the two upper bounds = 2.08203069740495884852.

   In the wide frame the hunt's decided bracket would become
   `0.2304 < Lambda_DH <= 0.7697`, against `Lambda_zeta <= 0.22`, which is a
   materially better result than the one currently written up.

   **Grade of that improved bound today: cited plus measured, not decided.**
   Their `1.120362` is a six-decimal Mathematica value, and their Theorem 7 rests
   on Bohr-Kronecker machinery this tree has not verified. To carry it at rung 2
   the hunt would have to (a) check Theorem 7's hypotheses in-tree, and (b)
   re-solve the arctan equation with outward-rounded enclosures, which is
   straightforward because the prime sum is monotone decreasing in `sigma`. Until
   then the decided headline stays `0.4006343708899557`, with the sharper number
   quoted as an improvement available from the literature. **Do not silently swap
   the headline for `0.19242`.**

   > **Update 2026-08-18: conditions (a) and (b) are both met, and the headline
   > moved by derivation rather than by swap.** `STRIP2.md` and `strip2.py`
   > derive the **necessary** half of their Theorem 7 in-tree, from the Euler
   > products of `L(s, chi)` and `L(s, conj chi)` plus one Moebius image, with
   > no Bohr theory and no Kronecker theorem, and re-solve the arctan equation
   > with outward-rounded enclosures on **both** backends (python-flint 192
   > bits and mpmath.iv dps 40, sieve limit `P = 10^5`, 4814 class primes; a
   > flint-only deep point at 320 bits and `P = 10^7`). The decided abscissa is
   > the exact rational `sigma_0' = 1.12036249819`, so the headline is now
   > `Delta^2/2 = 0.19242481458026887663805` narrow and
   > `0.7696992583210755065522` wide, **decided**, and nothing was swapped
   > silently: the superseded value is printed beside the new one in
   > `RESULTS.md` section 0, `FRAME.md` section 6 and `GATE.md`. Their converse,
   > which turns the abscissa into an exact supremum, is neither used nor
   > claimed, so the *number* is still theirs and only the grade is this
   > hunt's. Two of their published constants now serve as controls on the new
   > instrument, by machinery their Theorem 7 does not share: the section 9
   > finite claim (threshold prime 6323, cardinality 420) and
   > `sigma(tau_-, 1) = 2.38228610898712387152...` against their published ten
   > digits.
   >
   > **A correction this forces against check B of this file.** At `P = 10^7`
   > and 320 bits, `strip2.py` decides that both of check B's 29-digit
   > re-solves sit on the wrong side of their own root: `sigma(tau_+, 1)` is
   > high by about `1.2e-17` and `sigma(tau_-, 1)` is low by about `6e-18`.
   > This corrects two in-tree re-solves and not the published paper, which
   > prints 1.120362 and 2.3822861089 and which this instrument reproduces
   > exactly. What it does touch is the 18-digit figure
   > `0.192424814576128011...` in the table just above, derived from the
   > `tau_+` re-solve: the decided replacement from the deep point is
   > `0.1924248145761280190` narrow and `0.7696992583045120759956154` wide,
   > agreeing to 17 digits.

3. **`STRIP.md`** should note that the quantity `sigma_0` bounds is not merely a
   classical named object (Titchmarsh section 9.41, already noted) but has been
   *computed exactly for this very function* by Bombieri and Ghosh, and cite
   Theorem 7.

4. **Attribution fix** per section 5.1 above.

5. **`GATE.md` known assumption 9** ("the novelty line assumes Bombieri-Ghosh 2011
   ... contain neither `sigma_0` nor a bound on this constant. Neither has been
   read.") is now half discharged. Bombieri-Ghosh has been read. It contains no
   bound on `Lambda_DH`. It does contain a sharper strip constant. The
   academia.edu preprint 166936409 remains unread.

---

## 7. Residual risk after this reading

- **On `Lambda_DH` itself: closed by this source.** Bombieri-Ghosh cannot contain a
  de Bruijn-Newman bound, because the concept does not appear in it.
- **On the strip constant: closed, and adverse.** The exact constant is published.
  The hunt's originality claim on `sigma_0` does not survive; its
  enclosure-carrying elementary *derivation* still stands as work, but the number
  it bounds was known.
- **Still open, unchanged by this session**: academia.edu preprint 166936409, and
  the single-source forward-citation sweep on Dobner (Semantic Scholar only,
  OpenAlex returned 429) that `NOVELTY.md` flags as needing repetition against
  Google Scholar or MathSciNet.
- **One thing this reading newly suggests checking**: Bombieri-Mueller, "On the
  zeros of certain Epstein zeta functions", Forum Math. 20:2 (2008), 359-385
  (their reference [18]), which is where the `sigma(xi, q)` computation method
  comes from and which the hunt has not consulted. It is about Epstein zeta
  functions, so it is unlikely to carry heat-flow content, but it is the parent of
  the constant that just displaced `sigma_0` and it is one citation away.

---

*Retrieved, read and verified 2026-08-16. Full text: 50 pages, mathnet.ru
`rm9410`, English translation, free. Verification scripts for checks A and B are
in this session's scratchpad (`verify_primes.py`, `verify_bg2.py`); check A is
cheap and worth folding into the hunt's own test set if the improved bound is
ever adopted.*
