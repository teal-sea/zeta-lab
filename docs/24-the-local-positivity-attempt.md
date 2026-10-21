# 24. The local positivity attempt, run to its wall

*An ontology attempt in the sense of `docs/09` §4: propose a structure, push it
at the gates, and record exactly where it bleeds. It bleeds at the place
`docs/09` §5.1 predicts, which is the useful part.*

## The short version

Requirement C of `docs/09` §5.1 asks for a construction in which the Weil
quadratic form is the norm square of a naturally defined operator, so its sign
becomes formal. This document reports an attempt that **achieves exactly that,
one place at a time, and fails to globalise**, the local norms exist, are
canonical, are built from prime data alone with no zeros anywhere in the
definitions, and do not assemble into a global one because the per-place
residual is not of definite sign (measured: 52 of 60 places positive, 8
negative).

What survives is not a proof strategy but an instrument: a place-local
criterion `c_p ≤ d` that reads the local bound `|α_j| ≤ √p`, computed
from coefficients alone. The forward direction is derived; the converse is not
established by the closed form and rests on an unreviewed derivation (§2 and
`hunts/local_positivity/CORRECTIONS.md`, "Later correction", 2026-10-21). It
passes ζ and Dirichlet L-functions, fails Davenport–Heilbronn and both
discriminant −23 Epstein forms, and, unlike the Imposter Gauntlet of
`docs/15`, which "never actually consults ζ", it demonstrably reads its input.
Code: `localpos.py`. Every number below is
recomputed by the module, and every reference verdict re-derives.

---

## 1. The construction

For a Dirichlet series `f(s) = Σ aₙ n^{-s}` with `a₁ = 1`, write the local
log-derivative coefficients `λ_m = b_{p^m}/log p` at the place `p`. Define the
**place-p kernel**

```
    K_p^{(d)}(θ) = d + 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ)
```

and the normalisation-free threshold `c_p`, the least diagonal for which every
finite Toeplitz section with off-diagonals `λ_m p^{−m/2}` is positive
semidefinite, so the form with diagonal `d` is PSD exactly when `c_p ≤ d`. On a
summable sequence `c_p = −min_θ 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ)`, which is what
the module evaluates; on a growing sequence `c_p = +∞` (the module's
`"divergent"` regime); at `|α_j| = √p` the cosine series diverges while the
least diagonal can stay finite (exactly `d` for `ζ(s − ½)`, where the gate
reports INDETERMINATE; §2 records where the gate's regime reading goes wrong).
This one reading is used throughout. Nothing is fitted: `c_p` is a minimum,
and `d` is the degree read off the object's own gamma factors.

**Why the kernel is the thing.** Let `Φ_p f = Σ_{m≥0} p^{−m/2} f(· − m log p)`
be the one-sided local shift-average. Then the prime side of the Riemann–Weil
explicit formula decomposes place by place:

```
    prime term  =  − Σ_p log p · ( Q_p(f) − ‖f‖² ),    Q_p(f) = (1 − 1/p)·‖Φ_p f‖²
```

Measured against `zeta.weil.explicit_formula_sides` for the autocorrelation
pair: reconstruction `−0.154060343334` against the module's `−0.154060343334`,
agreeing to 22 digits once the place sum runs to `p ≤ 8000`. Each `Q_p ≥ 0`
*by construction*, it is a norm. That is Requirement C's norm identity,
obtained locally and canonically.

## 2. The derivation behind the statistic

If the place has a genuine Euler factor with Satake parameters `α_j`, then
`λ_m = Σ_j α_j^m` and, inside the bound, the series sums in closed form:

```
    K_p^{(d)}(θ)  =  Σ_j  (1 − |α_j|²/p) / |1 − α_j p^{−1/2} e^{iθ}|²
```

a sum of manifestly nonnegative terms when every `|α_j| < √p` and the
coefficients are real (parameters real or conjugate-paired). Checked
numerically: series `2.7203325546805037` against closed form
`2.7203325546805086` at `p = 7`, degree 2.

What this establishes is the **forward direction**: every `|α_j| ≤ √p` gives
`c_p ≤ d` (derived; at `|α_j| = √p` each parameter contributes a rank-one PSD
Toeplitz matrix with unit diagonal). An earlier version of this section read
the converse off the closed form, and that step is invalid: at `p = 2`,
`α = (3√2, 0, 0, 0)` the rational expression is `3 − 8/(10 − 6 cos θ) ≥ 1`
although one parameter exceeds `√p`, and the Fourier series it was supposed to
sum diverges. The gate is not fooled by that input, since it never evaluates
the rational expression: `threshold` reports `"divergent"` and `gate` returns
FAIL. The converse for `c_p` as defined in §1 rests on a separate argument: a
PSD section with diagonal `c` has `|s_m| ≤ c`, and `s_m = Σ_j (α_j/√p)^m` is
unbounded once some `|α_j| > √p` (no cancellation among the parameters
prevents it), so `c_p = +∞`. That derivation is written out in
`hunts/local_positivity/CORRECTIONS.md` ("Later correction") and is not
independently reviewed, so the iff is an unreviewed derivation, pending
external verification, not a decision procedure on the strength of the closed
form.

The gate is not a decision procedure on its own account either. It truncates
the series and reads the regime off two weighted terms a decade apart near the
truncation edge, and for a conjugate pair of Satake parameters the weights
oscillate, so that reading can land on either side of the bound: measured
2026-10-21, `α = 0.9·√2·e^{±0.2i}` at `p = 2` FAILs although `c_p ≈ 1.894 < 2`,
`α = 1.2·√7·e^{±0.4i}` at `p = 7` PASSes although `c_p = +∞`, and the
unit-modulus degree-2 family of §4's 60-angle control gets FAIL at 22 of the 60
angles (the original gate of 2026-08-10 passed all 60). In the summable regime
an excess smaller than ten tail estimates is read as PASS rather than as
undecided (for the shift `ζ(s − δ)` of §6 at `δ = 0.49`, `p = 2`, the truncated
`c` is 15.99 against `d = 1` with a tail estimate of 149.9, while the true value
is 0.9965). All of this is pinned in
`hunts/local_positivity/test_closed_form.py`, and the gate itself is
unchanged.

The ζ case has
the exact closed form `c_p = 2/(√p + 1)`, reproduced to 12 digits at
`p = 2, 3, 5, 7, 97` with an explicit truncation bound below `3.4e-14`. (The
bound is elementary, `2·max|λ|·p^{−(M+1)/2}/(1−p^{−1/2})`, and computed in
floating point, so it is *not* certified in the sense `zeta/rigor.py` owns.)

## 3. The gate

Degree `d` is forced by each object's own functional equation, never chosen.

| subject | γ-factor | d | max_p c_p | verdict |
| --- | --- | --- | --- | --- |
| ζ | `π^{-s/2}Γ(s/2)` | 1 | 0.828427 | **PASS** |
| L(χ) quadratic mod 5 | `Γ(s/2)`, even χ | 1 | 0.828427 | **PASS** |
| genuine degree-2 Euler factor (φ = 0.9) | control | 2 | 1.579671 | **PASS** |
| Davenport–Heilbronn | `(π/5)^{-(s+1)/2}Γ((s+1)/2)` | 1 | 1.836068 | **FAIL** at p = 2, 3 |
| DH-family t = 0 | same γ-factor | 1 | 1.333333 | **FAIL** at p = 2 |
| Epstein (1,1,6), principal | `(2π/√23)^{-s}Γ(s)` | 2 | 5.995074 | **FAIL** at p = 2, 3 |
| Epstein (2,1,3), non-principal | `(2π/√23)^{-s}Γ(s)` | 2 | 6.461868 | **FAIL** at p = 2, 3 |

All seven reference claims re-derive, `localpos.reference_table()` recomputes
this table rather than storing it, and a row whose verdict disagrees with its
expectation is a failure of the gate, not of the subject. This is `docs/09`
Gate 3 with a crisp answer to "where exactly does Davenport–Heilbronn fail to
embed?": **at p = 2, with excess 0.836**, because its local kernel is not
positive semidefinite.

The Epstein rows use `localpos.epstein_local`, which counts ideal classes
rather than enumerating lattice points: `zeta.epstein.epstein_representation_count`
is exact but enumerative, and cannot reach the `p^k` with `k ≈ 90` that the
`p = 2` truncation needs. `localpos.epstein_local_check()` asserts the two
agree on all 35 prime powers small enough for both, which is what licenses the
shortcut.

## 4. The controls, which are the point

**Decoy, does the statistic read its input?** The failure mode `docs/15`
records for the Imposter Gauntlet is a predicate that ignores its argument.
Swapping the coefficients moves the verdict: `a_{p^k} = 2^k` scores an excess
of `+9.6e14`, random ±1 coefficients score `+8.4e3`, against ζ's `−0.172`. The
gate consults its input.

**Null, is a nonzero excess meaningful?** Against 300 random period-5 real
sequences, the null median excess is `+5.88` and **100 %** fail. DH sits at the
**6th percentile**, i.e. Davenport–Heilbronn is an unusually *mild* member of
the class of things that fail, not an exotic near-miss. Matching `docs/18` §6's
finding with a different statistic.

**Lesion, where is the detector blind?** Interpolating ζ → DH coefficientwise,
the smallest detected violation is `ε* = 0.184`. A PASS therefore means "no
violation above ~18 % of the way from ζ to DH at the tested places", and
nothing stronger. The PASS side is not vacuous either: across 60 Satake angles
the genuine degree-2 family keeps a margin of at least `0.343`. (Those are
margins of the truncated `c`. Since the regime test was added on 2026-08-11
the gate's verdict on that family is FAIL at 22 of the 60 angles, §2.)

## 5. The honest boundary

**The gate is not a test for "has an Euler product."** A genuine degree-2 Euler
factor with `α = 2.3, 1/α`, violating Ramanujan, is **rejected** at `p = 5`.
The place is in the `"divergent"` regime (`2.3/√5 ≈ 1.0286`), so `c_p = +∞` by
the module's convention; the `65.24` printed there is the series truncated at
depth 41 (22.46 at depth 23, 110.80 at depth 52), not the value. This section
used to call that factor legitimate in the Selberg class; it is not, since
`docs/09` §3's axioms (4) (`θ < ½`, which needs `|α| < √5` at `p = 5`) and (5)
(Ramanujan) both exclude it. The gate reads the
local bound `|α_j| ≤ √p` (forward direction derived, converse an unreviewed
derivation, §2). For a single parameter the failure point is exactly `√p`
(`1.41421356` for p = 2, `9.84885780` for p = 97): the closed form's one
summand changes sign there, §2's derivation puts the jump of `c_p` from `≤ d`
to `+∞` at the same place, and the gate's verdict changes within a relative
`10^{−6}` of it (measured at p = 2 and 97). Claiming it detects
Euler products would be an overclaim; it detects Euler products *with a
Ramanujan-type bound*.

## 6. Where it bleeds, and why that was predictable

The construction satisfies Requirement A completely: `c_p` is a functional of
`{a_{p^k}}` alone, no zeros, no ξ-phases, no counting functions. It achieves
Requirement C locally. It fails at the globalisation, and the failure is
measurable rather than rhetorical:

```
    W(h)  =  [pole + arch]  −  Σ_p log p · ( Q_p(f) − ‖f‖² )
```

with `pole + arch = 0.1540603435` and the norm side `0.1540603433`, leaving
`W = 1.24e-10`. Every `Q_p ≥ 0`, but **`Q_p − ‖f‖²` is not of definite sign**,
52 positive and 8 negative over the first 60 places. So local positivity is
compatible with either sign of `W`, and buys nothing globally. The arithmetic
supplies the quadratic form; the geometry still has to explain the sign, and
the sign lives in the *balance* between the archimedean term and the norm sum,
not inside either.

This lands in the pseudo-solution taxonomy of `docs/09` §5.1 as a variant of
#5 (*finite approximants*): a positive structure obtained at each place without
control of the limit. Naming it that way is the correct filing.

**A second reason no fix helps, corrected 2026-08-11, and it is weaker than
what stood here.** The paragraph this replaces read: *"By `docs/18` §6, `ζ(s−δ)`
has the same coefficients up to a shift … Any coefficient functional, `c_p`
included, is therefore blind to the position of the critical line by
construction."* Three things were wrong with it. The citation is wrong:
`docs/18` §6 says **ordinate** statistics, which is a different and correct
claim. The premise is wrong: `ζ(s−δ)` has coefficients `n^δ a_n`, and the twist
is exactly the information at issue. And the universal is **false**, the
coefficients determine the function, hence its zeros, so some coefficient
functional must see them, and one is already in this tree: Titchmarsh 14.25(B)/(C)
gives `M(x) = O(x^{½+ε}) ⟺ RH`, a criterion in the coefficients of `1/ζ` alone
(`zeta/criteria.py`, face 1).

What is true is sharper and has a number in it. For `ζ(s−δ)` the local parameter
is `α_p = p^δ`, so `c_p = 2x/(1+x)` with `x = p^{δ−½}`, and

> `c_p ≤ d` holds **exactly when `δ ≤ ½`**, simultaneously at every place,

with `c_p` the least PSD diagonal of §1. For `δ < ½` that is the formula
above; at `δ = ½` the cosine series diverges but the least PSD diagonal is
exactly `1 = d` (measured on every section up to `N = 400`), and the gate
reports INDETERMINATE there; for `δ > ½` the power sums `p^{m(δ−½)}` are
unbounded and `c_p = +∞`. So the answer to `c_p ≤ d` is yes for every
`δ ≤ ½` and no beyond, and the gate agrees where it was pinned (PASS at `δ = 0.1`,
INDETERMINATE at `½`, FAIL at `0.6`; close below `½` its PASS is the default
for an excess it cannot resolve, §2): `δ = 0.1` is a function the
gate passes whose zeros sit on `Re s = 0.6`, which is the conclusion this
section needs, a PASS cannot locate the critical line, obtained with a
witness instead of a false universal. That threshold is not new: it is the
Selberg-class Euler-product axiom's `θ < ½` (Conrey–Ghosh 1992, remark 5, which
also records the shift observation itself in its remark 2) and, on the
automorphic side, the Jacquet–Shalika bound `|log_p |α_p|| < ½`, which Sarnak
states as sharp. The blindness of a coefficient statistic is a property of the
particular statistic, of its invariance under the twist `a_n ↦ n^δ a_n`, not
of coefficient provenance.

## 7. What is worth keeping

The instrument, not the strategy. `c_p ≤ d` is a cheap, coefficient-only Gate 3
test (forward direction derived, converse an unreviewed derivation, §2) with
measured power and a stated blindness threshold, the thing to
run in an afternoon on the next proposed ontology, which is what `docs/09` §5
asks for and what `docs/15` failed to deliver. As an attack on RH this is a
closed avenue, and it is recorded here so nobody reopens it.

## Where to go next

- `docs/09` §5.1: Requirements A/B/C and the pseudo-solution taxonomy this
  attempt files under.
- `docs/18` §6, the coefficient-side Gate 4 statistic `D(f)`, and the
  ordinate-blindness argument that bounds every construction of this shape.
- `docs/15`: the Imposter Gauntlet, whose vacuity the decoy control here is
  designed to prevent.
- `zeta/weil.py`: the explicit-formula convention this decomposition is
  validated against.
