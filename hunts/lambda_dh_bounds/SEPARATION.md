# SEPARATION: Lambda_DH > Lambda_zeta, unconditionally

Written 2026-08-16, after the gate closed (`GATE.md`, verdict YES) and after
a dedicated novelty adversary attacked the claim's phrasing. This page
elevates the comparison that `FRAME.md` section 7 and `NOVELTY.md` carried as
a calibration footnote to a named claim, at exactly the strength the
adversary sanctioned and not more. Vocabulary per `MISSION.md`: *measured* is
one float route, *decided* is an enclosure whose exact endpoints settle a
sign or an integer, *cited* is somebody else's theorem; a composite takes its
weakest grade.

## 1. The claim

> **In the shared normalization of Newman, Rodgers-Tao, Polymath 15 and
> Dobner (`s = (1+iz)/2`, the wide frame of `FRAME.md`), the de
> Bruijn-Newman constant of the Davenport-Heilbronn function strictly
> exceeds the de Bruijn-Newman constant of the Riemann zeta function:**
>
>     Lambda_DH > Lambda_zeta,   unconditionally.
>
> Composite grade: **cited plus decided** (weakest step cited), and the
> decided link carries the `M2` prose lemma recorded in `GATE.md`.

The chain, every link graded, with the sources pinned at source in
`POLYMATH-PIN.md`:

    0 <= Lambda_zeta                     cited: Rodgers-Tao arXiv:1801.05914,
                                         Theorem 1 ("One has Lambda >= 0"),
                                         pinned verbatim in POLYMATH-PIN.md
                                         section 2
    Lambda_zeta <= 0.22                  cited: Polymath 15 arXiv:1904.12438,
                                         Theorem 1.1 ("We have Lambda <= 0.22"),
                                         unconditional per their abstract,
                                         pinned verbatim in POLYMATH-PIN.md
                                         section 1
    0.22 = 11/50 < 144/625 = 0.2304      exact rational arithmetic,
                                         cross-multiplied:
                                         144 * 50 = 7200 > 6875 = 11 * 625,
                                         pinned by
                                         tests/test_lambda_dh_separation.py
    0.2304 = 4 * (36/625) < Lambda_DH    this hunt: winding count N = 1 for
                                         H_{36/625} (narrow frame) over a box
                                         whose interior has Im z >= 3/1024 in
                                         exact rationals, decided
                                         (python-flint 0.9.0 (Arb), 420 bits,
                                         winding_results.json; second witness
                                         mpmath dps 130,
                                         crosscheck_dhflow_results.json);
                                         strictness cited (Dobner
                                         arXiv:2005.05142 Theorem 1, closed
                                         half-line); frame factor 4 derived in
                                         FRAME.md section 3
    Lambda_DH <= 1.6025374835598228      this hunt: 4 x the narrow Delta^2/2
                                         interval, sigma_0 bisected on both
                                         backends with exact rational sign
                                         decisions (decided,
                                         strip_results.json), fed to de Bruijn
                                         1950 Theorem 13 (cited)

Assembled, in the wide frame where all four cited sources live:

    0 <= Lambda_zeta <= 0.22 < 0.2304 < Lambda_DH <= 1.6025374835598228.

The last link is not needed for the separation; it is printed because the
claim should travel with the whole bracket.

## 2. The exact rational core, and frame invariance

The strict middle inequality is a comparison of two rationals and is checked
by cross-multiplication, not by floats:

    144/625 > 11/50    because    144 * 50 = 7200 > 6875 = 11 * 625.

Frame invariance: divide every Lambda by 4 to reach the narrow frame
(Stopple arXiv:1301.3158, `s = 1/2 + iz`, this hunt's own):

    0 <= Lambda_zeta <= 0.055 < 0.0576 = 36/625 < Lambda_DH <= 0.4006343708899557,

and the middle comparison is the *same* cross-multiplication, because the
factor 4 cancels: `0.055 = 11/200` and `36 * 200 = 7200 > 6875 = 11 * 625`.
The inequality `Lambda_DH > Lambda_zeta` reads identically in both frames,
as an inequality between constants of one frame must. Both computations are
pinned by `tests/test_lambda_dh_separation.py`.

## 3. Why the quantitative floor is load-bearing

Strict positivity alone does not separate. `Lambda_DH > 0` is an immediate
corollary of Dobner's Theorem 1 plus any computed off-line zero (Spira 1994),
and it has been available since 2020 without anyone displaying it; but
`Lambda_DH > 0` is compatible with `Lambda_DH <= 0.22` and so decides nothing
against zeta's window. The separation exists only because the decided floor
is *quantitative* and happens to clear Polymath 15's bound: 0.2304 > 0.22,
with `144/625 - 11/50 = 13/1250 = 0.0104` to spare in the wide frame. Had
Polymath 15's bound come out above 0.2304, or the decided floor below 0.22,
this page would not exist. The direction of future movement is asymmetric:
any further sharpening of the zeta upper bound only widens the separation,
so what the claim is hostage to is not progress but the correctness of the
cited 0.22 itself, and of the decided floor.

## 4. What it means, and what it does not

**What it means.** `Lambda_zeta` is confined to `[0, 0.22]` (Rodgers-Tao;
Polymath 15). The Davenport-Heilbronn function's constant sits strictly above
that entire window: the backward-heat flow time this counterexample needs
before all its zeros become real exceeds the whole remaining uncertainty
window for zeta's own constant. The flow-time failure margin of the
counterexample is not merely positive; it is larger than everything zeta
still has left to resolve.

**What it does not mean.** Nothing here is evidence about the Riemann
hypothesis (`docs/08`; house rule). The separation is a decided property
distinguishing DH from zeta **through DH's already-known off-line zeros**,
which is gate-3 framing (`MISSION.md` WP4): the same pipeline pointed at zeta
produces no positive floor, because no off-line zero of zeta is known, so the
number separates the two functions only through what was already known to
separate them. It quantifies the difference; it does not discover it. Nor is
the inequality surprising: `Lambda_zeta <= 0` is equivalent to RH while
`Lambda_DH > 0` follows from DH's off-line zeros, so under RH the separation
is trivially expected. The content is that it now holds *unconditionally*,
with a decided quantitative gap, whether or not RH is true.

## 5. The adversary's verdict and caveats

A dedicated novelty adversary attacked the phrasing "first proven strict
inequality between the de Bruijn-Newman constants of two Dirichlet series"
on 2026-08-16. Its verdict, verbatim:

> VERDICT: the claim DIES as phrased; the result survives under a repaired
> phrasing.

Its kills and clearances, quoted verbatim from its report (the report's
final sentence arrived truncated mid-word at "The ln 2 e"; the truncation is
recorded rather than reconstructed, and the `ln 2` case it was evidently
reaching is already carried in `NOVELTY.md`: Newman-Wu determine a constant
of this type exactly, `ln 2`, for a three-atom measure, not a Dirichlet
series):

> **Kill 1: Andrade-Chang-Miller, arXiv:1310.3477 (2013), read in full this
> session** (PDF fetched and read page by page). Their L-functions
> `L(s, chi_D) = sum_{f monic} chi_D(f) |f|^{-s}` (their eq. 3.1-3.2) are
> literally Dirichlet series, and the paper itself calls `Lambda_D` a "De
> Bruijn-Newman constant" (their Section 3.2). They prove:
> - **Lemma 3.18 / Theorem 1.9: an exact closed form**,
>   `Lambda_{D_p} = log(|a_p(D)|/(2 sqrt p))` for deg D = 3 (a_p the
>   Frobenius trace of the elliptic curve y^2 = D(T)).
> - **Remark 3.10**: `D = T^3 + T` over F_3 has `Lambda_D = -infinity`,
>   exactly.
> - **Appendix A**: `D = T^5+T^4+T^3+2T+2` over F_5 has
>   `Lambda_D ~= -0.189`, exact as the log of a root of an explicit quartic.
> - **Appendix B**: a table of seven named D over F_3 with seven distinct
>   numerical lower bounds.
> - **Lemma 3.11**: `Lambda_D < 0` strictly whenever the zeros are simple.
>
> **Kill 2: Chang-Mehrle-Miller-Reiter-Stahl-Yott, arXiv:1411.2071 (2014)**
> (abstract fetched verbatim): "In contrast with previous work, we are able
> to exhibit specific L-functions for which Lambda_D = 0, and thereby prove
> a stronger statement: max_{L in F} Lambda_L = 0." So **exactly determined
> constants, including exact zeros, for named Dirichlet series** are
> published.
>
> Consequence: strict orderings between exactly determined de Bruijn-Newman
> constants of two named Dirichlet series (same field, same normalization)
> have been immediate one-line corollaries of published statements since
> 2013-2014, e.g. `Lambda_{T^3+T} = -infinity < -1.44e-1 <=
> Lambda_{T^3+2T+1}` inside ACM's own tables, or `-infinity < 0 = Lambda_D`
> across ACM/CMMRSY. Even an ordering against zeta is composable from print
> since 2013: `Lambda_{T^3+T} = -infinity < Lambda_zeta` (finite by Newman
> 1976). Nobody displays these inequalities because in function fields they
> are trivial (RH is a theorem there), but a referee will produce them in
> one paragraph. The unqualified phrase is indefensible.
>
> **What did NOT kill, verified this session:**
> - **Stopple 1301.3158** (ar5iv full text queried): no comparison between
>   `Lambda_Kr` and zeta's constant anywhere; `Lambda_Kr` is a sup over
>   discriminants not including zeta; his bounds are negative/
>   GRH-conditional. No strict ordering between two named constants.
> - **ACM/CMMRSY number-field side**: conjectures only; no positive
>   constant, nothing beating 0.22.
> - **Newman-Wu 1901.06596, full text extracted with pdftotext and
>   grepped**: the survey **never compares constants across objects**; 0.22
>   appears only as zeta's own bound (lines 21, 78, 1005 of extracted
>   text); no occurrence of Davenport, Heilbronn, or any cross-object
>   ordering.

## 6. The sanctioned phrasing

What the kills remove is the unqualified word "first" over all Dirichlet
series: in function fields, where the Riemann hypothesis is a theorem, every
constant in print is exactly determined and non-positive (with `-infinity`
and exact `0` attained), so strict orderings there, including orderings
against zeta through the `-infinity` examples, are one-line corollaries of
statements published since 2013-2014, displayed by nobody because they are
trivial. What survives every named kill is the qualifier that both constants
are nonnegative, which no function-field pair and no `-infinity` composite
can satisfy. The claim, at the strength the adversary's evidence sanctions:

> The strict inequality `Lambda_DH > Lambda_zeta` holds unconditionally, by
> `Lambda_zeta <= 0.22` (Polymath 15, cited) against `Lambda_DH > 0.2304 =
> 144/625` (this hunt, decided modulo two cited theorems), in the shared
> normalization of Newman, Rodgers-Tao, Polymath 15 and Dobner. So far as
> the searches recorded in `NOVELTY.md` and in this page reach, it is the
> first strict inequality between de Bruijn-Newman constants of two
> Dirichlet series in which both constants are nonnegative. It is not the
> first strict inequality between such constants outright: in function
> fields such orderings are immediate corollaries of exact determinations
> published since 2013-2014 (Andrade-Chang-Miller arXiv:1310.3477;
> Chang-Mehrle-Miller-Reiter-Stahl-Yott arXiv:1411.2071).

Do not drop "so far as the searches reach". Do not drop "in which both
constants are nonnegative". Do not display the chain without the frame.

## 7. Grade, in full

Weakest-step accounting, per `MISSION.md`'s vocabulary contract:

| link | grade |
|---|---|
| `0 <= Lambda_zeta` | cited (Rodgers-Tao Theorem 1) |
| `Lambda_zeta <= 0.22` | cited (Polymath 15 Theorem 1.1, unconditional) |
| `11/50 < 144/625` | exact rational arithmetic, pinned by test |
| `144/625 < Lambda_DH` | decided (winding N = 1, python-flint 0.9.0 (Arb), 420 bits; second witness mpmath dps 130) modulo cited (Dobner Theorem 1) and the frame factor 4 (derived, `FRAME.md` section 3); carries the `M2` prose lemma |
| `Lambda_DH <= 1.6025374835598228` | decided strip constant fed to cited theorem (not needed for the separation) |

Composite: **cited plus decided**. The separation inherits, through its
decided link, the `M2` blind spot recorded in `GATE.md` (the one prose
analytic step no cross-route exercises, whose lesion table shows wrong
silent integers from deflation 75); and, through its cited links, the
correctness of Polymath 15's Theorem 1.1, Rodgers-Tao's Theorem 1 and
Dobner's Theorem 1 as published, none of which is verified in-tree. It is
not a claim this directory proves on its own, and per `MISSION.md` it is not
promoted anywhere outside this hunt.
