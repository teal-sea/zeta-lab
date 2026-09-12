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
