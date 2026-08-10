# MISSION: Local positivity — a norm at every place, and no norm globally

**Agent Persona:** The Hunter (ontology-attempt edition)
**Scope:** `hunts/local_positivity/` only. Nothing outside this directory is
modified except the case-log entry in `hunts/README.md` and the record at
`docs/24-the-local-positivity-attempt.md`.

## Objective

`docs/09` §5.1 states the positive target: not "prove the Weil form is
positive" (that is RH restated), but **factorization** — construct, from prime
data alone, a structure in which the Weil quadratic form is a norm square, so
its sign becomes formal. Requirements A (arithmetic provenance), B (exact trace
realization), C (structural positivity).

Every serious program is stuck at Gates 1 and 2. This hunt asks whether
Requirement C can be reached *one place at a time*, where the local structure is
small enough to write down:

> **Does the prime side of the explicit formula factor, place by place, into a
> manifest norm — and if it does, does local positivity buy anything global?**

The answer is yes to the first and **no to the second**, and the second is the
result. Recorded so the avenue is not reopened.

## The construction (derived in the module, not recalled)

For `f(s) = Σ aₙn^{-s}` with `a₁ = 1`, let `λ_m = b_{p^m}/log p` be the local
log-derivative coefficients at `p`. The place-`p` kernel is the Toeplitz form

    K_p^(d)(θ) = d + 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ)

and the statistic is the normalization-free threshold

    c_p := − min_θ 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ),   so  K_p^(d) ≥ 0 ⟺ c_p ≤ d.

Nothing is fitted: `c_p` is a minimum, and `d` is read off the object's own
gamma factors. With Satake parameters `α_j` the series has the closed form

    K_p^(d)(θ) = Σ_j (1 − |α_j|²/p) / |1 − α_j p^{−1/2} e^{iθ}|²

so `c_p ≤ d` is **exactly** the local bound `|α_j| ≤ √p` — a decision procedure,
not a heuristic. Writing `Φ_p f = Σ_{m≥0} p^{−m/2} f(· − m log p)`, the prime
side decomposes as `−Σ_p log p (Q_p(f) − ‖f‖²)` with `Q_p = (1−1/p)‖Φ_p f‖²`,
a norm at every place.

## Instruments

`localpos.py`, which writes `results.json`. Entry points: `gate`,
`reference_table`, `lesion_sweep`, `null_distribution`, `ramanujan_violator`,
`satake_check`, `epstein_local_check`, `scope`, `provenance_report`.

The laboratory is used for three things only: `zeta.epstein.kappa` for the DH
coefficient, `zeta.epstein.epstein_representation_count` for the Epstein
cross-check, and `zeta.weil.explicit_formula_sides` for the decomposition
comparison. The gate itself imports nothing from `zeta/`.

## The standing checklist, answered

1. **Rival.** Davenport–Heilbronn and both disc −23 Epstein forms — the zeta
   department's own rivals. All three FAIL, at `p = 2, 3`. The trap is noted:
   these *are* the rival set, so the gate is calibrated in the other direction
   too (ζ, `L(χ)`, and a genuine degree-2 factor must PASS, and do).
2. **Decoy / surrogate.** Swapped coefficients move the verdict by 15 orders of
   magnitude, which is the control whose absence made the Imposter Gauntlet
   vacuous (`docs/15`). Against 300 random period-5 sequences, 100% fail with
   median excess +5.88, and **DH sits at the 6th percentile** — an unusually
   mild failure, echoing `ROADMAP.md`'s 27th-percentile calibration with a
   different statistic.
3. **Lesion.** Interpolating ζ → DH, the blindness threshold is `ε* = 0.184`.
   A PASS means "no violation above ~18% of the way from ζ to DH at the tested
   places", and nothing stronger. The PASS side is not vacuous either: across
   60 Satake angles the genuine degree-2 family keeps margin ≥ 0.343.
4. **Precision response.** ζ's threshold matches its closed form `2/(√p+1)` to
   12 digits with truncation bounded below 3.4e-14; the closed form pins the
   Ramanujan failure point at `√p` to 8 digits. The statistic responds to
   precision the way a real quantity does.

## Honest scope

Nothing here is evidence for RH. Every bound in this hunt is elementary floating
point, carrying no enclosure at any step, so nothing here makes a claim in the
ball-arithmetic regime `zeta/rigor.py` owns — and this file does not use that
regime's reserved word, which `tests/test_hunt_probe_discipline.py` forbids
anywhere under `hunts/` except the case log. The gate is **not** a test for
"has an Euler product": a genuine
degree-2 product with `α = 2.3, 1/α` — legitimate in the Selberg class,
violating Ramanujan — is rejected at `p = 5` with `c_p = 65.24`. It tests the
local Selberg bound, and `scope()` says so in the module rather than only here.

## Disposition

Instrument kept; no claim promoted. The construction reaches Requirement C
locally and fails to globalise: `Q_p − ‖f‖²` is not of definite sign (52 of 60
places positive, 8 negative), so local positivity is compatible with either
sign of `W`. Filed under `docs/09` §5.1 taxonomy item #5, *finite approximants*.

A hunt, not a department: its rivals are the zeta department's rivals, and per
`harness/README.md` a department whose battery is another department's battery
is not a department. Full record in `docs/24-the-local-positivity-attempt.md`.
