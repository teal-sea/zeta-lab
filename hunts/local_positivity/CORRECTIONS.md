# CORRECTIONS: session 2026-08-10, local positivity attempt

One documentation defect found in the repository, one new hunt to file, and one
process note. Ordered by what needs a decision from you.

---

## 1. `Λ ≤ 0.2` is misattributed in two docs

**Status: real defect, fix is one line each.**

`docs/05-de-bruijn-newman.md` §3 is **correct and is the authority**: it states
both bounds with primary citations:

> Polymath15 pushed it to `Λ ≤ 0.22` (Res. Math. Sci. 6 (2019), paper 31), and
> feeding Platt–Trudgian's verification of RH up to `3·10^12` back into the same
> machinery gives the current record `Λ ≤ 0.2` (Bull. Lond. Math. Soc. 53 (2021)).

`zeta.heatflow.lambda_facts()` agrees, listing them as separate entries with
separate authors, and flags both as **non-strict**, the only known strict upper
bound is Ki–Kim–Lee's `Λ < 1/2` (Adv. Math. 222 (2009)).

Two downstream docs disagree with each other, and one attributes the record to
the wrong people:

| file | line | says | problem |
| --- | --- | --- | --- |
| `docs/08-why-it-is-hard.md` | 318 | "**Polymath15** (2018) drove the upper bound to `Lambda <= 0.22`" | correct, but reads as current record; the record is 0.2 |
| `docs/12-how-hard-problems-die.md` | 264 | "`Λ ∈ [0, 0.2]` pinned from both sides" | correct value, no citation |
| `docs/12-how-hard-problems-die.md` | 330 | "Feeding Platt–Trudgian's `3·10^12` into the Polymath15 machinery is what gives `Λ ≤ 0.2`" | **attribution error**, 0.2 is Platt–Trudgian's own published bound, not a Polymath15 result |

Line 330 is the substantive one. The phrasing "the Polymath15 machinery ... gives
`Λ ≤ 0.2`" credits the sharpened bound to the collaboration; it is Platt and
Trudgian's, in their own 2021 paper. `docs/05` §3 says this correctly, so the
error is local to `docs/12`.

**Suggested edits, minimal:**

- `docs/08` line 318, after "`Lambda <= 0.22`", add: *"(sharpened to `Λ ≤ 0.2`
  by Platt–Trudgian, 2021, see `docs/05` §3)"*.
- `docs/12` line 264, after "`Λ ∈ [0, 0.2]`", add: *"(Rodgers–Tao below;
  Platt–Trudgian above, `docs/05` §3)"*.
- `docs/12` line 330, replace *"into the Polymath15 machinery is what gives
  `Λ ≤ 0.2`"* with *"into the same machinery is what let Platt–Trudgian sharpen
  Polymath15's `Λ ≤ 0.22` to `Λ ≤ 0.2`"*.

**Why it is worth fixing rather than tolerating.** It is a citation defect in
exactly the class `ROADMAP.md` exists to prevent, a fact stated three times at
three precisions, where the most-read summary (`docs/08` §6, the "what is
tractable" list a newcomer starts from) carries the stalest number. It also
propagated: my own first draft of the route map inherited the error from
`docs/12` and had to be corrected. That is the failure mode of a fact with no
single source of truth in the tree; `docs/05` §3 should be cited from both sites
rather than paraphrased.

---

## 2. New hunt: `hunts/local_positivity/`

**Status: complete, self-contained, filed as a hunt and not a department.**

An ontology attempt in the sense of `docs/09` §4, run to its wall. Deliverables:

- `localpos.py`, the module. Standalone: it imports `zeta.epstein` only for
  `kappa` and for the cross-check, and reproduces every reference row itself.
- `24-the-local-positivity-attempt.md`: the record, in `docs/` house style,
  filed against `docs/09` §5.1's pseudo-solution taxonomy.
- `localpos_gate.png`, three panels: the kernel at `p = 2`, thresholds across
  places, measured detector power.

**Why a hunt and not a department.** Its rivals are Davenport–Heilbronn and the
disc −23 Epstein forms, the *zeta* department's rivals. Per `harness/README.md`
and the `dossier/` precedent in `ROADMAP.md`, a department whose battery is
another department's battery is not a department. It borrows the zeta battery,
which is the correct relationship. Suggested placement:

```
hunts/local_positivity/
    MISSION.md          <- section 1 of doc 24
    localpos.py
    results.json        <- reference_table() + lesion_sweep() + null_distribution()
docs/24-the-local-positivity-attempt.md
figures/localpos_gate.png
```

> **Corrected 2026-10-21 ("Later correction" at the end of this file).** The
> closed form below does not give the converse of the equivalence it is
> offered for, which now rests on a separate derivation that has not been
> independently reviewed. The example under "The honest boundary" is not in
> the Selberg class, and its `65.24` is a truncation of a divergent series.
> The 60-angle control under "Controls" holds for its margins, but the gate
> as it now stands FAILs 22 of those 60 angles.

**What it establishes.** The place-local kernel
`K_p^{(d)}(θ) = d + 2Σ λ_m p^{−m/2}cos(mθ)` has the closed form
`Σ_j (1−|α_j|²/p)/|1−α_j p^{−1/2}e^{iθ}|²`, so `c_p ≤ d` is **exactly** the local
bound `|α_j| ≤ √p`, a decision procedure, not a heuristic, computed from
coefficients alone. Measured: ζ's threshold is exactly `2/(√p+1)` to 12 digits
with truncation bounded below `3.4e-14` (an elementary floating-point bound that
carries no enclosure at any step, so it makes no claim in the ball-arithmetic
regime `zeta/rigor.py` owns, and does not use that regime's reserved word); the
closed form pins the failure point at `√p` to 8 digits.

Reference table (degrees read off each object's own gamma factors, never chosen):

| subject | d | max_p c_p | verdict |
| --- | --- | --- | --- |
| ζ | 1 | 0.828427 | PASS |
| L(χ) quadratic mod 5 | 1 | 0.828427 | PASS |
| genuine degree-2 factor (φ=0.9) | 2 | 1.579671 | PASS |
| Davenport–Heilbronn | 1 | 1.836068 | FAIL at p = 2, 3 |
| DH-family t = 0 | 1 | 1.333333 | FAIL at p = 2 |
| Epstein (1,1,6) principal | 2 | 5.995074 | FAIL at p = 2, 3 |
| Epstein (2,1,3) non-principal | 2 | 6.461868 | FAIL at p = 2, 3 |

Controls, all in the module:

- **Decoy**: swapped coefficients move the verdict by 15 orders of magnitude
  (`a_{p^k}=2^k` → excess `+9.6e14`; random ±1 → `+8.4e3`; ζ → `−0.172`). This is
  the control whose absence made the Imposter Gauntlet vacuous (`docs/15`).
- **Null**: against 300 random period-5 sequences, 100 % fail, median excess
  `+5.88`; DH sits at the **6th percentile**, i.e. an unusually mild failure.
- **Lesion**: interpolating ζ → DH, the blindness threshold is `ε* = 0.184`.
  A PASS means "no violation above ~18 % of the way from ζ to DH at the tested
  places", and nothing stronger.
- **PASS side not vacuous**: across 60 Satake angles the genuine degree-2
  family keeps margin ≥ `0.343`.

**Where it dies, and this is the load-bearing part.** The prime side decomposes
place by place as `−Σ_p log p (Q_p(f) − ‖f‖²)` with `Q_p = (1−1/p)‖Φ_p f‖²`, a
genuine norm at every place: Requirement C achieved locally, from prime data
only, with no zeros in any definition. Reconstruction agrees with
`zeta.weil.explicit_formula_sides` to 22 digits. But `Q_p − ‖f‖²` is **not** of
definite sign (52 of 60 places positive, 8 negative), so the local norms do not
assemble into a global one, and local positivity is compatible with either sign
of `W`. Files under `docs/09` §5.1 taxonomy item #5, *finite approximants*.

**The honest boundary, stated so nobody overclaims it.** The gate is *not* a test
for "has an Euler product": a genuine degree-2 product with `α = 2.3, 1/α`,
legitimate in the Selberg class, violating Ramanujan, is rejected at `p = 5`
with `c_p = 65.24`. It tests the local Selberg bound, and `localpos.scope()`
says so in the module rather than only in prose.

---

## 3. Process note: three bugs, all caught by a reference case passing

Worth recording because it is evidence for a rule the repo already has.

Four errors occurred while building this, and three were caught not by a
counterexample failing but by a **reference case behaving wrongly**:

1. `L(χ₅)` scored negative, my diagonal normalisation was ζ-specific, not
   forced. A genuine Euler product must pass; it did not, so the statistic was
   wrong.
2. A genuine degree-2 factor scored negative: I had taken a real part that
   broke the Satake structure.
3. Davenport–Heilbronn *passed*: I had let the degree float instead of reading
   it off the functional equation. This is the dangerous one: the gate looked
   like it worked, and the failure was silent.
4. A Gram-block discriminator scored ζ negative and was discarded outright.

Each was found because the battery was calibrated **in both directions**. A
battery that only ever rejects is indistinguishable from a correct one until you
make it pass something it should pass, which is precisely why
`harness/README.md` requires at least one reference claim expected to pass and
one expected to fail, and why `tests/test_department_conformance.py` re-derives
verdicts rather than trusting labels. Error #3 would have shipped as a working
gate under a rejection-only battery.

Suggested addition to `docs/17-the-falsification-harness.md`, which currently
records five claims refuted by existing controls: this is the complementary
case, **three instrument defects caught by the calibration requirement**, one
of which produced a plausible-looking correct verdict for the wrong reason.

---

## 4. Standing observation for `ROADMAP.md`

This is the third independent statistic to hit the same wall from a different
direction:

- `zeta/factorization.py`'s `D(f)`: coefficient-side, Gate 4 (`docs/18` §6)
- the Fourier quasicrystal separation (`docs/18` §4)
- `localpos.py`'s `c_p`: coefficient-side, local Selberg bound

All three read arithmetic; none can read the *position* of the critical line.

> **Superseded 2026-08-11 (`docs/25`). The proposal in this section must not be
> adopted, and the reason given for it is wrong.** `docs/18` §6 says *ordinate*
> statistics, not coefficient statistics; `ζ(s−δ)` has coefficients `n^δ a_n`,
> not the same ones; and `c_p` in fact reads that twist, with threshold exactly
> `δ = ½` (`c_p = 2x/(1+x)`, `x = p^{δ−½}`: the Selberg-class axiom's `θ < ½`).
> What is true is the weaker statement that these three particular statistics
> are invariant, or nearly so, under the twist. The universal is refuted inside
> this repository by `criteria.py` face 1: `M(x) = O(x^{½+ε}) ⟺ RH` is a
> criterion in the coefficients of `1/ζ` alone (Titchmarsh 14.25(B)/(C)).

That tension is not an artifact of any one attempt, and three independent
instruments landing on it is a measurement rather than a coincidence. It belongs
in `ROADMAP.md` under known gaps as a *standing constraint on the whole
coefficient-side programme*: any Requirement-A-compliant statistic is blind to
the critical line by construction, so a future candidate that claims to see it
must explain where the zero-information enters without violating provenance.

---

## Later correction: the closed form does not establish the local iff

**What is false, and where it was stated.** The docstring of
`localpos.satake_kernel` said the rational expression
`Σ_j (1−|α_j|²/p)/|1−α_j p^{−1/2}e^{iθ}|²` is nonnegative for all `θ` exactly
when every `|α_j| ≤ √p`. That is false. For `p = 2` and `α = (3√2, 0, 0, 0)`
the expression is `3 − 8/(10 − 6 cos θ)`, which stays in `[1, 5/2]` while one
parameter exceeds `√p`. Its defining Fourier series has coefficients of
magnitude `3^m` and diverges, so the rational expression is not its sum there.
The step that read the iff off the closed form (the module docstring, section 2
of this record under "What it establishes", `MISSION.md`, and `docs/24` §2) is
therefore not a valid argument for the converse.

**What the counterexample does not refute.** The iff for `c_p` as the module
defines it. `gate()` never evaluates the rational expression (`satake_kernel`
is called only by `satake_check`). On exactly this input `threshold()` reports
regime `"divergent"` and `gate(..., 4, primes=[2])` returns FAIL, both now
pinned by `test_closed_form.py`. The recorded verdicts and `results.json`,
whose `scope()` line is a statement about `c_p`, stand as historical
measurements; their wording "exact" and "decision procedure" is graded below.

**One reading of `c_p`, used everywhere from now on.** `c_p` is the least
diagonal `c` for which every finite Toeplitz section with diagonal `c` and
off-diagonals `s_m = λ_m p^{−m/2}` is positive semidefinite. On an absolutely
summable sequence this equals the cosine-series minimum the module evaluates
(the standard Toeplitz–symbol correspondence). On a growing sequence it is
`+∞`, which is the module's existing `"divergent"` convention. At
`|α_j| = √p` the two readings part: the cosine series diverges, while the
least PSD diagonal can stay finite. For `ζ(s − ½)` it is exactly `1 = d`
(measured `1.000000` on every section `N = 5, 50, 200, 400`), and on that
input `gate()` reports INDETERMINATE; it does not do so at every input on the
bound (finding 3 below).

**Derivation of both directions (written in this landing, 2026-10-21; not
independently reviewed).** Assumptions: a degree-`d` Euler factor at `p` with
real coefficients, so its Satake parameters are real or come in conjugate
pairs; write `β_j = α_j/√p`, so `s_m = Σ_j β_j^m` is real for `m ≥ 1`.

1. *Forward: every `|α_j| ≤ √p` gives `c_p ≤ d`.* The section with diagonal
   `d` is the sum over `j` of the Hermitian Toeplitz matrices with entries
   `β_j^{i−k}` for `i ≥ k` and conjugates above the diagonal (the sum matches
   because `s_m` is real). For `|β_j| < 1` that matrix holds the Fourier
   coefficients of the Poisson kernel `(1−|β_j|²)/|1−β_j e^{iθ}|² ≥ 0`, hence
   is PSD; for `|β_j| = 1` it is the rank-one Gram matrix `v v*` with
   `v_i = β_j^i`. Each has unit diagonal, so the sum is PSD with diagonal `d`.
2. *Converse: some `|α_j| > √p` gives `c_p = +∞`.* A PSD matrix has every
   `2×2` principal minor nonnegative, so `|s_m| ≤ c` for all `m`. But
   `Σ_{m≥1} s_m z^m = Σ_j β_j z/(1 − β_j z)` is rational with a pole at `1/β`
   for each nonzero `β` among the `β_j`, residue `−k/β` for multiplicity `k`.
   Copies of one `β` add and distinct `β` give distinct poles, so nothing
   cancels. With `R = max_j |β_j| > 1` the radius of convergence is `1/R`, so
   `limsup |s_m|^{1/m} = R > 1` and `s_m` is unbounded: no finite `c` works.

Measured support for step 2, pinned by `test_closed_form.py`: a single
parameter with `|β| = 1.05` has least PSD diagonal `1.2806`, `77.31` and
`1.770e5` on the sections `N = 5, 50, 200`.

**Grade after this correction.** The forward direction is derived. The
converse is not established by the closed form; for `c_p` read as the least PSD
diagonal it rests on the derivation in step 2, which is elementary but
unreviewed, so the iff as a whole is an unreviewed derivation, pending external
verification, and the words "exact" and "decision procedure" in the original
record should be read at that grade. The `c_p = 65.24` recorded for the
`α = 2.3, 1/α` violator is a finite-depth truncation in the `"divergent"`
regime (`2.3/√5 ≈ 1.0286 > 1`), where the module's own convention is
`c_p = +∞`; the FAIL it records stands, the number is not the value.

**Found while landing this correction (2026-10-21).** Five findings, measured
in the landing worktree on top of `origin/main` at `fb647bfc7`. They lie
outside the closed-form question but concern the same instrument or the same
sentences. Each is pinned in `test_closed_form.py`, none changes a verdict in
the reference table, and this landing does not change `gate()`.

1. *`gate()` misreads oscillating weights, in both directions.* `threshold()`
   decides summable, divergent or boundary from two weighted terms about a
   decade apart near the truncation edge, a test added on 2026-08-11 (commit
   `5eed14344`; `docs/25` §6; C-LOCPOS-01). For a conjugate pair of Satake
   parameters the weights oscillate, so that comparison can fall on either
   side of 1 whatever their envelope does. Inside the bound,
   `α = 0.9·√2·e^{±0.2i}` at `p = 2` is called divergent and FAILs although
   `c_p ≈ 1.894 < d = 2`. Outside it, `α = 1.2·√7·e^{±0.4i}` at `p = 7` is
   called summable and PASSes although `c_p = +∞` (least PSD diagonal above
   `10^9` on the `N = 120` section). On it, `α = √2·e^{±0.9i}` at `p = 2`
   FAILs although `c_p = d = 2` exactly.
2. *The 60-angle positive control regressed when that test went in.* Section
   2 above records that "across 60 Satake angles the genuine degree-2 family
   keeps margin ≥ 0.343". Re-run on 60 equally spaced angles `φ` from 0.05 to
   `π − 0.05` (`α = e^{±iφ}`, the default 25 primes), which reproduces that
   minimum margin (`0.3434`), the statement still holds for the margins of the
   truncated `c`. But the current gate's *verdict* on the family is FAIL at 22
   of the 60 angles, while the module as first committed (`e3e4426b4`,
   2026-08-10) passes all 60 when re-run. `docs/25` §6 and C-LOCPOS-01 report
   the hunt's recorded verdicts unchanged by the repair. That holds for the
   verdicts `docs/25` §6 lists (ζ, `L(χ)`, Davenport–Heilbronn, both Epstein
   forms, the violator), and the reference table, the lesion threshold
   `ε* = 0.1841` and the null distribution reproduce exactly, but the 60-angle
   control was not among them.
3. *INDETERMINATE on the bound holds only for steady weights.* `threshold()`'s
   comments equated its regime test with the bound: a ratio above 1 "is
   exactly `|alpha| > sqrt(p)`", and the boundary regime is "`|alpha| =
   sqrt(p)` to numerical resolution". That holds when the weighted terms near
   the edge keep a steady modulus. `ζ(s − ½)`, the single real parameters
   `+√2`, `−√3` and `+√97`, and the pair `±√5` all give INDETERMINATE, and for
   one real parameter the verdict changes within a relative `10^{−6}` of `√p`
   (PASS below, INDETERMINATE inside, FAIL above; measured at `p = 2, 97`).
   For a conjugate pair on the bound the gate can say FAIL (`φ = 0.9`,
   `p = 2`) or PASS (`φ = 2.0`, `p = 2`, with the regime called summable),
   where `c_p = d` exactly. The comments are now scoped; the code is
   unchanged.
4. *The honest-boundary example is not in the Selberg class.* Section 2
   above, `MISSION.md`, `docs/24` §5, the case log, `docs/37`,
   `ramanujan_violator` and the `note` stored in `results.json` called
   `α = 2.3, 1/α` legitimate in, or allowed by, the Selberg class. At `p = 5`
   it is excluded twice over: by `docs/09` §3's axiom (5) (Ramanujan,
   `a_n ≪ n^ε`) and by its axiom (4) (`b_n ≪ n^θ` with `θ < ½`, which needs
   `|α| < √5`). It is a genuine Euler factor outside the local bound, which is
   all the honest boundary needs, and the gate rejects it for that reason.
   `results.json` keeps its note as the historical record.
5. *The violator's `65.24` moves with the truncation depth.* Beyond the grade
   above: the same call reads 22.46 at depth 23 (`tol = 1e-8`), 65.24 at the
   default depth 41 and 110.80 at depth 52 (`tol = 1e-18`), and the least PSD
   diagonal of its `N = 200` section exceeds `10^3`.

Two smaller points, both pinned as well:

- *An excess the gate cannot resolve reads as PASS.* In the summable regime a
  place whose truncated `c` exceeds `d` by less than ten tail estimates is no
  witness, so the verdict is PASS rather than undecided. For `ζ(s − δ)` at
  `δ = 0.49`, `p = 2`, the truncated `c` is 15.99 against `d = 1`, the tail
  estimate is 149.9, and the PASS is right only because the true
  `c_p = 0.9965` lies below `d`.
- *A rejected universal still stood in the module docstring.* C-SHIFT-01 lists
  the `localpos.py` docstring among the places that stated "no coefficient
  functional can read the position of the critical line". The director run
  corrected `provenance_report()`, `docs/24` §6 and the case log, but the
  docstring's "Why the kernel is the thing" section still stated it until this
  landing.

A repair of the regime test is a deliberate act: it has to re-measure the
hunt's recorded numbers and change the tests that pin findings 1 to 3. This
landing records and pins the defect and leaves the gate as it is. Nothing here
is evidence for or against RH.
