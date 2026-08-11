# 25 — The director run: the laboratory pointed at itself

**2026-08-10/11.** An operator handed the laboratory over with no theorem, no
direction, and no assurance that the agenda was the right agenda. The standing
objective was to produce the most genuine mathematical information obtainable
from this tree and its resources *while minimizing the probability that the
laboratory fools itself*, and the explicit instruction was that finding an
existing conclusion of this repository to be wrong counts as a result.

This document is the record. The run's own scaffolding — programs, budget,
claim ledger, graveyard, intervention ledger — is in `hunts/director_run/`.
Nothing here is evidence for or against RH.

---

## 1. How the run was organised

Nine investigators with deliberately conflicting mandates, run in parallel with
isolated contexts, and a director that allocated, verified and integrated.
Separation was the instrument, not a formality: **the generator of a claim never
also judged it.** Three of the run's four most useful outputs came from an agent
whose only reward was destroying another agent's work.

| role | count | what it was rewarded for |
| --- | --- | --- |
| Skeptic | 3 | defects in recorded claims; destroying explorer output |
| Explorer / program | 3 | volume, diversity, feasibility measurements |
| Replicator | 1 | *disagreeing* with the original, from spec alone |
| Knownness | 1 | killing a survivor with a citation |
| Auditor | 1 | a planted fault nothing catches |

The programs, their theses and objections, and the initial budget are in
`hunts/director_run/PROGRAMS.md`, written before the first result returned so
the allocation can be scored against what happened. The scoring rule was fixed
in advance and included the clause that **"nobody has attacked it yet" scores as
a penalty, not as survival**.

---

## 2. What died — the repository's own claims

Six confirmed defects, every one of them in a claim this tree already had in
writing. Each was reproduced by the director independently of the agent that
found it before being recorded here.

### 2.1 `rigor.py` could return a wrong proof — the most serious finding

`zeta/rigor.py` is the only module entitled to the word *certified*, and its
contract is that a nonzero `proven_sign` **is a theorem**. `_exact` converted
unrecognised numeric types by parsing `str(value)` — the *printed decimal* — as
exact. `numpy.float64` is a `float` subclass and was safe; `numpy.float32`,
`float16`, `longdouble` and `sympy.Float` are not.

```
np.float32(21.02203941345215)   exact value 11021603/524288
                                 repr parses as 525551/25000  — a different point
true Z there            = +2.561519159e-7
proven_sign  (before)   = -1        on BOTH backends
enclose_Z    (before)   = [-4.1065861495e-7, -4.1065861495e-7]   width 3.6e-46
```

A 1e-46-wide enclosure that does not contain the value it claims to enclose, and
a *wrong* proven sign. The two-backend cross-check — the habit that entitles the
module to the reserved word — could not see it, because the fault is **upstream
of the split**: both backends consume the same converted abscissa.

Fixed: conversion goes through the exact binary value when widening to float64
is lossless, and raises `TypeError` otherwise. Pinned by
`tests/test_rigor.py::test_a_numpy_float32_is_its_binary_value_not_its_repr`
and a companion that the lossy case is refused rather than guessed.

**The general lesson, which is worth more than the bug:** a cross-check between
two independent implementations bounds only the part of the pipeline that is
actually duplicated. Here `_exact`, the contour and subdivision policy, the
grid policy, and the final interval summation of `S(T)`/`N(T)` are shared, so
the cross-check certifies the ζ and log Γ *evaluators* against each other and
not the pipeline. That is now stated where the claim is made.

### 2.2 `sign` was read off an enclosure a step had failed to establish

Also `rigor.py`. When the Fejér prime cutoff proof `log(n_max+1) > 2b` cannot be
closed, the code records the failure in `uncertified_steps` and then continues
with `prime_tail = 0` — an enclosure asserting the prime sum is exactly
complete, which is precisely what it just failed to prove. `sign`, documented as
*proven*, was computed from that enclosure and came back nonzero.
`positivity_proven` was already gated on `certified`; `sign` now is too.
Regression test in `tests/test_rigor_weil.py`.

### 2.3 The exact Sturm branch of `li.is_hyperbolic` returned a false positive

`zeta/li.py` advertises `"sturm"` as *exact* — "the polynomial held in memory
converts to ℚ[X] without error", a decision procedure. It ran on the *balanced*
coefficients, and `_balance` multiplies by `mp.power(s, j)` at working
precision, which rounds. So the "exact" branch decided a different polynomial
from the one the caller passed:

```
X² − 2X + (1 + 10⁻⁴⁵)      (no real roots)
dps 15, 20 → hyperbolic=True, n_real_exact=1, agree=True
```

`agree=True` is the aggravating part: the root finder was fooled identically, so
the built-in disagreement flag could not fire. `_to_rational`'s much-documented
guard prevented a *second* re-rounding; the first one happened one step earlier.
Fixed by running Sturm on the input coefficients — `X ↦ sX` with `s > 0` is a
bijection of the real line, so the Sturm count never needed balancing; only the
root finder did. Now `agree=False` at low dps, which is the honest state: the
tolerance test is fooled, the decision procedure is not.

### 2.4 A "load-bearing" completeness guard with no power

`zeta/detector.py`'s `online_list_is_complete` was documented as cross-checking
the cached Davenport–Heilbronn on-line ordinates against an **independent**
count. Its reference was `zeta.epstein.zeros_on_line` — *the same technique on
the same function*, on a grid measured to be **1.4×–1.8× coarser** than the one
that produced the cached list. A pair closer than either step is invisible to
both, identically: zero power against the exact failure mode the docstring names.
Two investigators reached this independently.

The genuinely independent count already existed in the tree and was not used.
`method="strip"` now applies the argument principle over `Re s ∈ [−0.5, 1.5]`
and checks `strip = on-line + 2·(off-line members)`. Measured: deficit 0 on
(1, 60] and (60, 90] once the known quadruple at `γ ≈ 85.699` is accounted for
— so the cached list *is* complete, which is good news that was previously
unestablished rather than established. It costs ~20 s against ~1 s, which is why
the cheap route remains the default; it now reports `independent: False` in
data rather than claiming the opposite in prose.

### 2.5 "The detector quantifies the violation" — only if handed the answer

The same module's headline said the peak height recovers `|β − ½| = 0.3085` to
1.3e-14. That number comes from evaluating the residue *at* `OFFLINE_ZERO_IM`,
i.e. at thirteen correct decimals of the answer. Run end to end on the module's
own pipeline — `residue_scan` on the grid the tests use, argmax, invert — it
recovers **0.0221 against 0.3085, a 92.8 % error**, because the inversion
`sqrt(log(r/4)/a)` is infinitely steep at `r = 4` and the whole signal lives in
the fourth decimal of the residue. Detection is unconditional; quantification is
conditional on an independently located ordinate. The docstring now says so
where the claim is made, not only in the callee.

### 2.6 A scan whose control column could never read False

`li_positivity_scan(method="zeros")` is `head + tail + boundary`, all three
nonnegative termwise (the boundary term because the route feeds it
`S_T = −1/2` by construction). Its `positive` column is structurally `True` for
every n, whatever the zeros do. By this repository's own admission rule for
batteries — *a battery that could never fail* — that is a defect. The rows now
carry `can_report_negative`, and the docstring says which route's sign carries
information (the default `"cauchy"` one).

---

## 3. What died — a strategic conclusion, and the correction is the result

The tree recorded, in five places, and **used once to close a research avenue**:

> "`ζ(s−δ)` has the same coefficients … Any coefficient functional — `c_p`
> included — is therefore blind to the position of the critical line by
> construction."

Three things are wrong with it, and the third matters.

1. **The citation.** `docs/18` §6, which all five places cite, says *ordinate*
   statistics. That claim is exactly correct and is untouched by any of this:
   `ζ(s−δ)` has literally the same ordinates, so an ordinate statistic cannot
   distinguish it from ζ.
2. **The premise.** `ζ(s−δ)` has coefficients `n^δ a_n`. The twist is precisely
   the information whose visibility is at issue, so "up to a shift" cannot carry
   the inference that follows it.
3. **The universal is false, and this tree contains the counterexample.** The
   coefficients determine the function, hence its zeros. Concretely,
   `zeta/criteria.py` face 1 already records Titchmarsh 14.25(B)/(C):
   `M(x) = O(x^{½+ε})` for all ε > 0 ⟺ RH — a criterion in the coefficients of
   `1/ζ` alone.

**What is true is sharper and has a number in it.** For `ζ(s−δ)` the local
parameter is `α_p = p^δ`, so the local-positivity gate's own closed form gives
`c_p = 2x/(1+x)` with `x = p^{δ−½}`, and

> `c_p ≤ d` holds **exactly when `δ ≤ ½`**, simultaneously at every place.

So the conclusion `docs/24` needed — a PASS cannot locate the critical line —
survives, with a witness (`δ = 0.1` passes, and its zeros sit on `Re s = 0.6`)
instead of a false universal. Blindness is a property of a statistic *invariant
under the twist* `a_n ↦ n^δ a_n`, not of coefficient provenance.

**The consequence for the agenda.** `hunts/local_positivity/CORRECTIONS.md` §4
proposed promoting the repetition across three instruments to a `ROADMAP.md`
standing constraint on the whole coefficient-side programme. That call was
explicitly left to a director. **The answer is no**, and adopting it would have
closed, on a false premise, a programme that already contains a working member.

**And the mathematics is not new — the knownness gate killed that outright.**
The threshold is the Selberg-class Euler-product axiom's `θ < ½`; Conrey–Ghosh
(1992) remark 2 records the shift observation itself, as motivation for the
axioms; the automorphic form is the Jacquet–Shalika bound
`|log_p |α_p|| < ½`, which Sarnak states as sharp, with a known Luo–Rudnick–
Sarnak improvement; the real vertical shift is the standard arithmetic-versus-
analytic *normalization*, with its own LMFDB knowl; and "log-derivative
supported on prime powers ⟺ Euler product" is the literal wording of the axiom.
Confidence that nothing mathematical here is new: ~0.9. **The finding is a
correction to this repository, not a contribution to number theory** — and
saying so is the point of having a knownness role.

Two attempted generalisations were destroyed in the process, by a skeptic and by
the prior-art search independently and with different counterexamples: the claim
that "the abscissa of the partial sums of the coefficients of `1/f` equals
`sup Re(zeros of f)`" **in general** is false (`f(s) = exp(2^{-s})` is entire and
zero-free with partial sums `Θ(1)`; `f(s) = 1/(1 − 2·2^{-s})` likewise). It is a
theorem about ζ, needing analytic continuation and a vertical growth bound on
`1/f`, not a general fact. That correction is recorded here because the internal
report had leaned on it.

---

## 4. What survived

### 4.1 The flagship certified number, independently replicated

`rigor.enclose_weil_functional` reports `W(h) ≈ 8.86e-18` for the near-tight
Gaussian `a = 0.2` — eighteen digits of cancellation out of pieces of size ~2 —
with an enclosure ~1e-51 wide. A replicator was given **the mathematical
statement only**, forbidden from reading `weil.py`, `rigor.py`, `core.py`, the
tests or any document, and forbidden from importing the package at all.

It reproduced `W(h) = 8.860364360447289768506902298134e-18`, converged to 43
digits, agreeing with an independently computed **zero-side** sum
`Σ_ρ h(γ_ρ)` to 43 digits at dps 60 and 62 at dps 80; and its own from-scratch
Arb enclosure has radius **1.600e-51**, reproducing the reported width. It also
established what the director most wanted tested — that the number is a
*converged* quantity and not a truncation residue: the prime tail beyond
`n_max = 2·10⁵` is bounded by 3.0e-79, sixty-one orders below the answer, and
raising `n_max` four orders changes nothing.

Two by-products are worth more than the confirmation:

- **The width is diagnosable and is not about arithmetic.** The 1.6e-51 radius
  is, to every digit, the archimedean *analytic tail bound* at `R = 24`. The
  certified enclosure's width is a statement about how far out one integrates,
  not about precision or primes.
- **A too-short integration range flips the sign of a positivity number.** At
  `R ≤ 12` the replicator's `W` comes back **negative**. In a laboratory where a
  certified negative `W` would disprove RH, that is a failure mode worth having
  in writing.

The replicator also reported its own near-miss honestly: an intermediate state
of the replication was a plausible "NOT REPLICATED at the 14th digit", caused by
binding `mpf('0.2')` at import time when `mp.dps` was still 15. The signature —
an error that refuses to move under *every* convergence knob — is this
repository's standing artifact signature, pointing at a mis-bound constant
rather than a discrepancy. Recorded as a methodological rule: **with eighteen
digits of cancellation, the parameter needs as much precision hygiene as the
arithmetic.**

### 4.2 The Lean arm rebuilds from nothing, with zero `sorry`s

No Lean toolchain existed in this environment. elan was installed from scratch,
the Mathlib cache fetched (8681 files), and `lake build` completed all 8715 jobs
successfully. Every occurrence of the string `sorry` under `lean/ZetaLean/` is
in prose about the rule. The repository's loudest verification claim reproduces
on a cold machine.

### 4.3 Rung 3 is feasible — and the previously recorded cause was wrong

The formal arm's flagship target was blocked on a trade the previous session
called *"the one genuinely unresolved thing in rung 3"*: the centre cell fails
by 37 %, and the stated cause was that raising the exponential Taylor order
`nExp` is the only fix while `nExp` is what inflates the literals. This was
attacked with the bit-exact Python mirror, needing no Lean at all.

Every published number reproduced. **The stated cause did not.** Measured, the
box width is *bit-identical* under `nExp ∈ {16, 20, 24, 28}` and under `p`, and
saturates in `nLog`. The residual floor is the width of the **κ enclosure** —
`kappaI`, 6e-7 wide in `DHAssembly.lean` — multiplying every `m ≡ 2, 3 (mod 5)`;
an analytic check (`Σ m^{−0.8085} = 6.905` over those m, times 6e-7 = 4.1e-6)
accounts for the measured 2.9e-6 floor. The trade the session recorded as the
blocker does not exist.

Three separate defects were isolated, two of them arithmetic errors in the plan:

1. **The centre pays its tail radius twice.** `normBound(B.inflate r)` is the L1
   norm, `max|re| + max|im| + 2r`, and the plan budgeted `r` once. Since
   `2·r_c = 7.47e-4 > ε′ = 5e-4`, the centre **could not have passed at any
   Taylor order, any precision, any κ**. Raising `K` to 444 (+415 terms out of
   ~80 000) gives margin **1.164**.
2. **The grid's β was predicted, not measured.** Setting `β := normLower`, which
   the generator already computes, makes the claim exact by construction; the
   cell condition then carries ≥10× slack.
3. **The boxed-`s` width model is low by 2.3×, and all 11 sampled big boxes
   fail** (margins 0.57–0.66). The constant `ρ_W ≈ 5.9` against the planned 2.6
   is **scale-invariant in δ and invariant under every parameter** — it is the
   rectangle representation of a rotating complex value under repeated
   squaring. Removing it needs a polar or mean-value enclosure: an architectural
   change worth ~2× on the whole certificate, not a re-plan.

A configuration with real headroom exists — measured margins 1.164 (centre) and
1.139 (big box), ≥10× on the grid inequality — at ~130k certified terms against
79.5k, with **the same literal sizes** (endpoint size is set by the coarsening
precision alone, measured). The cheapest single improvement found: coarsening
the exponent argument once before `expCr` cuts the largest intermediate rational
5–8× and makes it independent of `nLog`, at a width cost invisible in five
significant figures.

Sample sizes are stated rather than implied: 26 of 104 grid sites, 11 of 110 big
boxes (all on one edge), one re-planned box, one machine under heavy load. The
`ρ_W` measurement has not been made on the low-σ left edge, which is where the
cost concentrates and where the model is least tested.

---

## 5. What surprised the director

- **The two-backend cross-check is weaker than the repository believed, and the
  defect that proves it is real rather than planted.** Both backends agreed on
  a wrong sign. Independence has to be traced to the *inputs*, not asserted at
  the level of implementations.
- **Two of the six defects are in guards** — a completeness check with no power,
  a truncation guard that resolved "cannot decide" into the favourable verdict.
  The safety machinery is where this tree's remaining errors live, not the
  mathematics. That is a prediction the next session can test.
- **The knownness gate paid for itself immediately** and killed the run's most
  attractive-looking result. An internal correction that felt like a discovery
  turned out to be the Selberg-class axioms.
- **The adversarial separation produced its best output when it turned on its
  own side.** The skeptic assigned to destroy the shift result sustained the
  numbers, destroyed the inferences, *and found a worse defect the original had
  missed* — that the local gate returns false FAILs with named witness primes on
  `δ ∈ [0.4877, 0.5]`, where every place genuinely satisfies the bound.

---

## 6. What was fixed, and what was left alone

Fixed with a regression test: §2.1, §2.2, §2.3. Fixed with corrected contracts
and data fields: §2.4, §2.5, §2.6, and the local-positivity gate (a third
verdict `INDETERMINATE` for the knife edge, `FAIL` where the weighted local
series genuinely diverges — which *is* the violation — and a truncation bound
that reads the actual geometric ratio instead of maxing over computed terms; the
old one was violated sixfold at `p = 2, δ = 0.49`). The hunt's recorded verdicts
are unchanged by the repair: ζ and `L(χ)` PASS, Davenport–Heilbronn and both
Epstein forms FAIL, and the Ramanujan violator still FAILs.

**Left alone deliberately:** a repo-wide lexical test for the reserved word. The
rule is enforced by a grep under `hunts/` only, and one violation was found and
fixed in `zeta/weil.py`'s comments — but a survey found seven legitimate uses of
"certify/certifies" in ordinary English inside `zeta/`, so a lexical test would
need an allowlist longer than its own content. **That is itself a finding about
the apparatus**: the discipline the repository calls a hard rule is mechanically
enforced in one directory and by review everywhere else.

---

## 7. Where to go next

- **The formal arm.** Re-plan rung 3 at the measured constants (`nLog = 36`,
  `K_centre = 444`, `β := normLower`, `w₂ = 1/4`, `M = 4`, `L = 22`), and
  measure `ρ_W` on the low-σ left edge first — it is the one number the cost
  estimate leans on that has not been sampled where it matters.
- **The architectural question worth more than the re-plan.** `ρ_W ≈ 5.9` is a
  representation artifact. A polar or mean-value enclosure of `m^{-s}` would buy
  ~2× on the entire certificate and is the only change here that is mathematics
  rather than parameters.
- **Guards are the frontier.** Two of six defects were in controls. A pass over
  every guard in the tree, asking only *"what does this fire on, and has that
  been measured?"*, is the highest-expected-yield audit left.
- **Report a blindness radius wherever a lesion threshold is reported.** The
  tree already measures how large a planted violation must be before a detector
  sees it (`ε*`). The twist direction is a second axis of the same kind, costs a
  bisection, and for `c_p` has an exact closed form.

## Where to go to read more

- `hunts/director_run/` — programs, claim ledger with dispositions, graveyard,
  intervention ledger.
- `docs/24` §6 — the corrected paragraph; `hunts/local_positivity/CORRECTIONS.md`
  §4 — the proposal that must not be adopted, and why.
- `HANDOFF.md` — the rung-3 record this run corrects.
