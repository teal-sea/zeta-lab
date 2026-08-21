# Adversary 5 (prior art): findings

Scratch analysis, 2026-08-16. Written by an adversary tasked with breaking the
novelty of `0.0576 < Lambda_DH <= 0.4006343708899557`, not with defending it.
Novelty was treated as open throughout. Nothing in this directory was modified.
My own code is in
`/tmp/claude-0/-home-user-zeta-lab/ea2c50e5-c6c1-5be9-ac30-eda79b8fac85/scratchpad/`
(`pa_strip.py`, `pa_righetti.py`).

## Verdict in one paragraph

No source was found that states a numerical bound, from either side, on a de
Bruijn-Newman constant of the Davenport-Heilbronn function or of any other
function known to violate its own Riemann hypothesis. The interval survives as
an original result. But four things in `NOVELTY.md` need correcting or adding,
and one of them is a live risk to the upper bound's novelty rather than to its
correctness: a fifty-page survey devoted to exactly this function, by Bombieri
and Ghosh, is not in the prior sweep at all, and its published keyword list
names the exact mechanism that produces the strip constant. I could not read
it. Until someone does, the strip constant should not be described as new.

## 1. What the prior sweep missed, in order of how much it matters

### 1.1 Bombieri and Ghosh 2011 is absent from `NOVELTY.md`, and is the sharpest risk

E. Bombieri and A. Ghosh, *Around the Davenport-Heilbronn function*, Uspekhi
Mat. Nauk 66:2 (2011), 15-66 = Russian Math. Surveys 66:2 (2011), 221-270,
DOI 10.1070/RM2011v066n02ABEH004740. Fifty pages, both authors at the IAS,
devoted to this single function. It is cited by Righetti (arXiv:1506.05716,
reference [5]) and by Nakamura-Pankowski (arXiv:1909.08301).

The published abstract is one sentence and says nothing. The published keyword
list says a great deal:

> zeros of Dirichlet series, reciprocals of Dirichlet series, estimates of
> coefficients

"Reciprocals of Dirichlet series" plus "estimates of coefficients" is the
standard route to a zero-free half-plane for a series with a dominant leading
coefficient: 1/f(s) has an absolutely convergent Dirichlet expansion exactly
where `sum_{n>=2} |a_n| n^{-sigma} < 1`, which is the defining equation of
this hunt's `sigma_0`. A survey with those keywords, about this function, is
the most likely place in the literature for `sigma_0 = 1.39513615823510972...`
to already be in print, possibly to several digits.

I could not read it. It is behind IOPscience (subscription), mathnet.ru
returned 503 on every attempt, and no preprint or mirror was found. There is a
recorded Bombieri lecture of the same title on YouTube that a human could
watch.

**Action**: this is a named, checkable, high-probability source. Either a human
reads it before the hunt claims the strip constant is new, or the claim is
stated with this source named as unread. It does not touch correctness: my own
independent recomputation of `sigma_0` (below) agrees with `strip_results.json`
to 30 digits.

### 1.2 Stopple 2013 already publishes this hunt's exact normalization

`NOVELTY.md` cites Stopple (arXiv:1301.3158) only as one of the "generalized
Newman lines, all at negative-or-zero values". That undersells it. Stopple's
equation (1) and the line above it are:

> Xi(t, chi) := (D/pi)^{(s+1)/2} Gamma((s+1)/2) L(s, chi)
>             = int_0^inf Phi(u, chi) cos(ut) du,
> Phi(u, chi) = 4 sum_{n=1}^inf chi(n) n exp(3u/2 - n^2 pi exp(2u)/D)

Set D = 5 and replace `chi(n)` by the period-5 coefficients `a_n`, and this is
character for character the hunt's

    Phi_DH(u) = 4 e^{3u/2} sum_{n>=1} n a_n exp(-pi n^2 e^{2u} / 5),
    F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s),  H_0 = Xi_DH.

Stopple then defines `Lambda_{-D}` per discriminant and `Lambda_Kr = sup
{Lambda_{-D}}` in that frame, and proves `-1.12929e-7 < Lambda_Kr`, with
`Lambda_Kr <= 0` only under GRH.

Two consequences, pulling in opposite directions.

- **For the hunt**: adversary 1's complaint that the interval is stated in a
  frame no cited source uses is now only half true. There *is* a published
  de Bruijn-Newman-type constant defined with precisely this `Phi` and this
  `e^{tu^2}` kernel, in a refereed paper on generalized Newman conjectures.
  The hunt should cite Stopple as its normalization precedent and stop
  presenting the frame as its own choice. The factor-4 dictionary against
  Newman, Rodgers-Tao, Polymath 15 and Dobner still has to be stated, because
  Stopple never states it either.
- **Against the hunt**: Stopple is a direct precedent for "quantitative bounds
  on a de Bruijn-Newman constant of an object other than zeta", and one of his
  two sides is unconditional. So the novelty cannot rest on the words
  "quantitative", "generalized", or "for an object other than zeta". It rests
  only on the qualifier *RH-violating*, and on *both sides unconditional*.

### 1.3 The upper bound's engine is current survey material, not just a 1950 scan

`THEOREM13.md` reconstructs de Bruijn's Theorem 13 from an image-only scan and
treats confirming its all-zeros form as a standing task. That work is not
wasted, but a clean modern restatement exists in a source `NOVELTY.md` already
cites for something else. Newman and Wu, *Constants of de Bruijn-Newman type
in analytic number theory and statistical physics*, Bull. AMS 57 (2020)
(arXiv:1901.06596), Theorem 7, page 8, verbatim from the arXiv PDF:

> **Theorem 7** Suppose that the function F satisfies (10), (11) and the zeros
> of the entire function (9) lie in the strip |Im z| <= Delta. Then all the
> roots of the entire function
>     int_{-inf}^{inf} F(t) e^{lambda t^2 / 2} e^{izt} dt
> lie in the strip
>     |Im z| <= max(Delta^2 - lambda, 0)^{1/2}.

They attribute it to [DB50] and note that [KKL09] later supplied the second
property. With the multiplier written `e^{lambda t^2 / 2}` the flow reaches
real-rootedness at `lambda = Delta^2`; with the hunt's `e^{t u^2}` that is
`t = Delta^2 / 2`. This is the hunt's dictionary, restated in a Bulletin of the
AMS survey in 2020, with a strip hypothesis and no positivity hypothesis on
Phi.

**Action**: cite Newman-Wu Theorem 7 alongside de Bruijn 1950. It is a
checkable, typeset, refereed statement of the engine. And it settles the
honest framing of the upper side: the mechanism is standard, published and
surveyed, and what this hunt supplies is the strip constant it is fed.

### 1.4 A ten-digit abscissa constant for a Davenport-Heilbronn type function is already published

Righetti, *On the density of zeros of linear combinations of Euler products
for sigma > 1* (arXiv:1506.05716), page 4, states that for

    f(s, tau) = (1/2)[(1 - i tau) L(s, chi_1) + (1 + i tau) L(s, conj chi_1)],
    tau = -(1+sqrt5)/2 - sqrt(1 + ((1+sqrt5)/2)^2),

the real parts of the zeros "are dense up to sigma* = 2.3822861089 ...", proved
in his PhD thesis, p. 66. He calls `f(s, tau)` "of the Davenport-Heilbronn type
studied by Bombieri and Ghosh".

That `tau` is not an unrelated parameter. Writing `phi = (1+sqrt5)/2`, the two
roots of `x^2 + 2 phi x - 1 = 0` are `kappa = -phi + sqrt(1+phi^2) =
0.28407904384041229603...` and `tau = -phi - sqrt(1+phi^2) =
-3.5201470213402019924...`, and `kappa * tau = -1` exactly. I verified all
three numerically (`pa_righetti.py`). So Righetti's function is the *other*
root of the same quadratic: same construction, sibling function.

I then checked whether his constant is this hunt's construction in disguise.
It is not. Solving `sum_{n>=2} |a_n| n^{-sigma} = 1` for the period-5 sequence
`(1, c, -c, -1, 0)` gives

| c | coefficient-domination abscissa |
|---|---|
| `kappa` (this hunt's function) | 1.395136158235109721061359 |
| `tau` (Righetti's function) | 2.477958026532674935112887 |

against Righetti's published 2.3822861089. His `sigma*` is strictly smaller,
as it must be: denseness of zero real parts up to `sigma*` is a lower-bound
statement and is harder than the triangle-inequality upper bound, and the
naive bound is not sharp because `log 2` and `log 4` are dependent.

So Righetti owns a different constant for a different member of the family, in
the opposite direction. But he owns the nearest published decimal to the one
this hunt is claiming, for a function he himself calls Davenport-Heilbronn
type, and a reader will meet the two numbers together. Cite him, and say which
is which.

### 1.5 The quantity `sigma_0` bounds is a classical named object

Righetti's opening lines, verbatim:

> Let L(s) be a Dirichlet series and let sigma* = sigma*(L) be the least upper
> bound of the real parts of the zeros of L(s). Then it is well known that
> sigma* is finite (see e.g. Titchmarsh [37, Section 9.41]).

The hunt's strip is therefore an explicit numerical upper bound on a classical
quantity with a classical finiteness theorem behind it, not a new kind of
statement. `STRIP.md` should say so in one line. This costs the hunt nothing
and removes an easy objection.

### 1.6 Zero-free regions for the Davenport-Heilbronn function are an active named topic

Bucur, Ernvall-Hytonen, Odzak and Smajlovic, *On a Li-type criterion for
zero-free regions of certain Dirichlet series with real coefficients*, LMS J.
Comput. Math. (2016). Abstract, verbatim:

> The Li coefficients lambda_F(n) of a zeta or L-function F provide an
> equivalent criterion for the (generalized) Riemann hypothesis. In this paper
> we define these coefficients, and their generalizations, the tau-Li
> coefficients, for a subclass of the extended Selberg class which is known to
> contain functions violating the Riemann hypothesis such as the
> Davenport-Heilbronn zeta function.

`NOVELTY.md` mentions "Odzak-Smajlovic Li coefficients for DH-class functions"
in the search list but does not name this paper, whose title is literally
zero-free regions for a class containing the Davenport-Heilbronn function. It
should be named. It uses no heat flow and states no de Bruijn-Newman constant,
so it does not threaten the claim.

Note also its usage: "the Davenport-Heilbronn **zeta function**", not
"L-function". See section 4.

## 2. The academia.edu preprint: mostly recovered, still not read

`NOVELTY.md`'s standing caveat was id 166936409, unread. Every automated route
still fails: Cloudflare managed challenge on direct fetch, `r.jina.ai` returns
401 on IP reputation, the Wayback availability API rate-limited and the CDX
endpoint is blocked by egress policy. It remains unread in full.

However the search index has it, and repeated targeted queries returned
different fragments of the abstract each time, so a good deal is now known.
Full title:

> Off-Line Zeros of the Riemann xi-Function: A Constraint Network, an Exactly
> Solvable Collision Model, Explicit Frozen-Field Bounds, a Lifetime-Deficit
> Dictionary for Weil Positivity, and an Interference-Channel Negative Control

Fragments recovered, each returned by the search index as text from that
document:

- "the de Bruijn-Newman constant measures how long hypothetical off-line zeros
  of xi survive under the backward heat flow; Weil's criterion measures whether
  a windowed quadratic form built from primes and the Gamma-factor can go
  negative. These are two currencies for one quantity, with explicit exchange
  rates."
- "The two-zero ladder reads 0.4233 (static) and 0.4305 (dynamic, exact closed
  form), against the classical anchors Lambda <= 1/2 (de Bruijn) and Lambda <
  1/2 (Ki)."
- "the budget-extremal estimate tau*(T0) = 0.229 at the verification height
  T0 = 3 x 10^12; the bound decreases along future verification records as
  tau*(T) ~ 9.4 / log T, crossing 0.2 near T ~ 1.25 x 10^15."
- "A measured supply-envelope calibration at a Davenport-Heilbronn frequency
  quantifies both: the positivity envelope exceeds the resonance demand by a
  factor 3.0."
- "at both off-line zeros of the Davenport-Heilbronn function the measured
  lifetimes fall inside the predicted deficit windows, with exchange rates
  0.653 and 0.821 against a theoretical spread of approximately 8."
- "four measured faces of the Davenport-Heilbronn counterexample, and a
  negative-control theorem proving the Connes-Consani-Moscovici rank-one scheme
  cannot converge for Davenport-Heilbronn data."

Read together these settle the shape of the thing. Its object is the Riemann
xi function and the classical Lambda; its headline numbers (0.4233, 0.4305,
0.229) are bounds on *that* Lambda, stated against the anchors 1/2, so they sit
in the wide frame, not this hunt's. The Davenport-Heilbronn function enters
three times, all as instrument rather than as subject: a frequency for a
Weil-positivity calibration, a negative control for a rank-one scheme, and,
the one that matters here, a validation set of measured off-line-zero
lifetimes under the de Bruijn-Newman backward flow.

**The residual risk, stated plainly.** A lifetime of an off-line zero under the
backward flow is the same physical quantity `hunts/flow_repair/` calls a
landing time, and any such number is a float-grade lower bound on Lambda_DH
whether or not the author says the words. So it is possible that a June 2026
preprint contains, implicitly, a float-grade lower bound on Lambda_DH for the
two lowest Davenport-Heilbronn off-line zeros. Three things bound the damage:
it names no Lambda_DH, it gives no upper bound at all, and the hunt's floor
comes from the pair-5 site near Re z = 240.4 rather than from the two lowest
zeros. The lower side of this hunt is also decided rather than measured, which
is a different grade. But the caveat should stay, now with its content named
rather than guessed from a title.

**Provenance.** `NOVELTY.md` asks that this be checked against the laboratory's
own sibling outputs. I searched this tree for its distinctive vocabulary
(Apollonius, frozen-field, lifetime-deficit, interference-channel,
Connes-Consani-Moscovici, supply envelope, resonance demand) across all
tracked files and all of `git log --all`. None of it appears anywhere except
in `NOVELTY.md` itself. So it is not an artifact of this repository. Whether it
came from elsewhere in the family is not answerable from inside this checkout,
and the honest statement is that I could not determine its provenance.

## 3. What I searched, and what came back empty

Beyond the sweep already recorded in `NOVELTY.md`:

- **Dobner's forward citations.** Semantic Scholar
  `paper/arXiv:2005.05142/citations` returns five records, of which one
  (Rodgers-Tao 1801.05914) is a reference miscoded as a citation and two are
  the same Jensen-polynomial paper in two versions. The remaining two are
  Farmer's "Currently there are no reasons to doubt the Riemann Hypothesis"
  (arXiv:2211.11671) and a Berry-Keating style Hamiltonian construction
  (arXiv:2505.21192). Neither computes Lambda_F for any member of S#.
  OpenAlex could not be used as a cross-check: the API now meters by budget
  and returned HTTP 429 with zero daily allowance. So the citation sweep is
  single-source and should be repeated by a human with Google Scholar or
  MathSciNet. Published version: Acta Arithmetica (2021), under the title
  "A proof of Newman's conjecture for the extended Selberg class"; the arXiv
  title is different ("A New Proof of Newman's Conjecture and a
  Generalization"), which is a real trap for a title search.
- **Newman-Wu, read in full.** No occurrence of Davenport, Heilbronn or
  Epstein anywhere in the text. The `ln 2` example is Case 2 of their
  classification, a three-atom symmetric measure, and their statement is an
  exact equality: the set of admissible b is `[ln 2, inf)`. Confirms
  `NOVELTY.md`'s reading.
- **Stopple's two-sidedness.** Unconditional lower bound only; the upper side
  is GRH-conditional. Verified from the paper text.
- **Saias-Weingartner** (arXiv:0807.0783), **Booker-Thorne** (arXiv:1306.6362),
  **Righetti** (Monatshefte 180, 2016), **Nakamura-Pankowski**
  (arXiv:1909.08301): all prove the *existence* of infinitely many zeros with
  sigma > 1 for combinations of L-functions. None states an upper abscissa.
- **Balanzario and Sanchez-Ortiz** (Math. Comp. 76, 2007): the AMS PDF is
  blocked to automated fetch, but its indexed summary says only that "most of
  the zeros off the critical line have real part greater than 1". No strip
  constant surfaced.
- **Ferry, Ghisa and Muscutar** (arXiv:1602.06328), read in full: an opinion
  article correcting an earlier note, arguing Spira's points are true zeros.
  No strip, no heat flow.
- **Michalowski**, arXiv:2602.20313 (submitted 23 Feb 2026, revised 20 Jul
  2026), on the Polya frequency order of the de Bruijn-Newman kernel. An
  outside author working the same kernel with 80-digit outward-rounded
  interval arithmetic. No Davenport-Heilbronn, no Lambda bound, so no
  collision. Worth reading anyway as a cautionary neighbour: version 2
  withdraws a version 1 global sign claim "because the derivative-tail
  enclosure was unsound", while the direct counterexample survives. That is
  the same failure mode this hunt's tail bounds are exposed to.
- **Digit searches** for 1.39513, 1.3951361, 0.8951, 0.895136: nothing.
- **Titchmarsh, Theory of Functions, Section 9.41**: cited by Righetti for
  finiteness of `sigma*`. Not read directly.

Empty on the central question. No source attaches a number to a de
Bruijn-Newman constant of the Davenport-Heilbronn function, or of any
RH-violating function, under any notation.

## 4. Is the framing defensible? Four repairs

The proposed sentence is "first quantitative two-sided bounds for the de
Bruijn-Newman constant of an RH-violating L-function". Four separate problems,
none fatal.

**(a) "L-function" is the wrong noun and a referee will say so.** The
Davenport-Heilbronn function has no Euler product. That is the entire reason it
can violate its own Riemann hypothesis, and it is why Dobner needs the
*extended* Selberg class. The literature that handles it carefully calls it
"the Davenport-Heilbronn zeta function" (Bucur et al.), "the Davenport-Heilbronn
function" (Bombieri-Ghosh) or "a Dirichlet series satisfying a Riemann-type
functional equation" (Nakamura-Pankowski). Calling it an L-function in a
novelty sentence hands a reviewer a free objection and, worse, overstates the
result by implying the bounds apply to something with arithmetic content.

**(b) "two-sided" needs a domain restriction.** Newman-Wu determine a
de Bruijn-Newman type constant *exactly* (`ln 2`), which is two-sided in the
strongest sense; `Lambda_zeta` has unconditional two-sided bounds
(`0 <= Lambda <= 0.22`); Stopple has one unconditional side and one conditional.
So "first two-sided bounds for a de Bruijn-Newman constant" is simply false.
The whole weight sits on *RH-violating*, and the sentence must make that
visible rather than burying it as an adjective.

**(c) The frame has to be in the sentence.** The number is frame-dependent by
a factor of 4 (adversaries 1 and 3). Fortunately section 1.2 gives the fix:
the frame is Stopple's, it is published, and naming it converts a weakness into
a citation.

**(d) The upper side must not be sold as a mechanism.** Newman-Wu Theorem 7 is
a 2020 Bulletin of the AMS statement of the exact implication used. What is
supplied here is the strip constant, and even that may be in Bombieri-Ghosh.
The honest phrasing separates "we applied a published theorem" from "we
computed the constant it needs".

## 5. Recommended sentence

Headline, for `RESULTS.md` and any abstract:

> So far as the literature search recorded in `NOVELTY.md` reaches, these are
> the first quantitative bounds, from either side, on the de Bruijn-Newman
> constant of a Dirichlet series with a Riemann-type functional equation whose
> Riemann hypothesis is false. They are stated in the normalization of Stopple
> (arXiv:1301.3158), in which `Phi(u) = 4 sum_n a_n n exp(3u/2 - pi n^2
> e^{2u}/5)`, and are four times smaller than the same constant in the
> normalization of Newman, Rodgers-Tao, Polymath 15 and Dobner.

Mandatory footnote, not optional and not to be compressed:

> Existence, finiteness and nonnegativity of this constant are Dobner's
> (Acta Arith. 2021), for all of the extended Selberg class, with no member
> named and no number given. The upper bound is de Bruijn's 1950
> strip-contraction theorem, restated as Theorem 7 of Newman and Wu (Bull. AMS
> 57, 2020), applied to a zero strip computed here; the mechanism is published
> and surveyed, and the strip constant `sigma_0 = 1.39513615823510972...` is
> what this work supplies. Quantitative bounds on de Bruijn-Newman constants of
> objects other than zeta are not new: Stopple bounds `Lambda_Kr` for quadratic
> Dirichlet L-functions from below unconditionally and from above under GRH,
> and Newman and Wu determine such a constant exactly (`ln 2`) for a three-atom
> measure. The qualifier that carries the claim is that the object here
> violates its own Riemann hypothesis. Two sources bearing on it were not read:
> Bombieri and Ghosh, *Around the Davenport-Heilbronn function*, Russian Math.
> Surveys 66 (2011), 221-270, whose published keywords name reciprocals of
> Dirichlet series and estimates of coefficients, the mechanism that yields
> `sigma_0`, and which may therefore already contain the strip; and academia.edu
> preprint 166936409, which measures survival times of Davenport-Heilbronn
> off-line zeros under this same flow and so may contain, implicitly, a
> float-grade lower bound.

If the hunt wants one line rather than a paragraph, the safe short form is:

> First quantitative two-sided bounds on the de Bruijn-Newman constant of a
> function that violates its own Riemann hypothesis, subject to two named
> unread sources.

Do not use "L-function". Do not drop "so far as the search reaches". Do not
drop the frame.

## 6. Recommended edits to `NOVELTY.md`

1. Add Bombieri-Ghosh 2011 as an unread source, with its keyword list quoted,
   and mark it a blocker on the strip constant's novelty.
2. Upgrade the Stopple entry: he publishes this hunt's `Phi` and this hunt's
   heat kernel, and one of his two bounds is unconditional.
3. Add Newman-Wu Theorem 7 as the modern statement of de Bruijn's engine.
4. Add Righetti's `sigma* = 2.3822861089...` for the sibling root
   `tau = -1/kappa`, with the note that it is a different constant in the
   opposite direction, and record the numeric check that separates them.
5. Add Bucur-Ernvall-Hytonen-Odzak-Smajlovic by name.
6. Replace the standing caveat's guess about preprint 166936409 with the
   recovered abstract fragments in section 2 above, and record that its
   provenance could not be determined from inside this checkout.
7. Record that the Dobner citation sweep is Semantic Scholar only, because
   OpenAlex is now metered and returned no allowance, and that the arXiv and
   journal titles of that paper differ.

## 7. Reproduction

    .venv/bin/python /tmp/.../scratchpad/pa_strip.py       # sigma_0, independent route
    .venv/bin/python /tmp/.../scratchpad/pa_righetti.py    # kappa, tau, kappa*tau = -1,
                                                          # both abscissae

`pa_strip.py` builds `sum_{n>=2} |a_n| n^{-s}` from Hurwitz zeta at `r/5` and
solves for the root, touching none of this directory's code. It returns
`sigma_0 = 1.39513615823510972106135889733`, `Delta = 0.895136158235109721...`,
`Delta^2/2 = 0.400634370889955694446954776081`, agreeing with
`strip_results.json` to every digit printed. The strip constant is right. The
only open question about it is whether it is first.
