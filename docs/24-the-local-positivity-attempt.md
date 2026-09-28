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
criterion `c_p ≤ d` that is **exactly** the Selberg-class bound `|α_j| ≤ √p`,
computed from coefficients alone. It passes ζ and Dirichlet L-functions,
fails Davenport–Heilbronn and both discriminant −23 Epstein forms, and, unlike
the Imposter Gauntlet of `docs/15`, which "never actually consults ζ", it
demonstrably reads its input. Code: `localpos.py`. Every number below is
recomputed by the module, and every reference verdict re-derives.

---

## 1. The construction

For a Dirichlet series `f(s) = Σ aₙ n^{-s}` with `a₁ = 1`, write the local
log-derivative coefficients `λ_m = b_{p^m}/log p` at the place `p`. Define the
**place-p kernel**

```
    K_p^{(d)}(θ) = d + 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ)
```

and the normalisation-free threshold `c_p := −min_θ 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ)`,
so that `K_p^{(d)} ≥ 0 ⟺ c_p ≤ d`. Nothing is fitted: `c_p` is a minimum, and
`d` is the degree read off the object's own gamma factors.

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

## 2. The theorem behind the statistic

If the place has a genuine Euler factor with Satake parameters `α_j`, then
`λ_m = Σ_j α_j^m` and the series sums in closed form:

```
    K_p^{(d)}(θ)  =  Σ_j  (1 − |α_j|²/p) / |1 − α_j p^{−1/2} e^{iθ}|²
```

a sum of manifestly nonnegative terms exactly when `|α_j| ≤ √p`. Checked
numerically: series `2.7203325546805037` against closed form
`2.7203325546805086` at `p = 7`, degree 2. So the gate is a *decision
procedure* for the local Selberg bound, not a heuristic, and the ζ case has
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
the genuine degree-2 family keeps a margin of at least `0.343`.

## 5. The honest boundary

**The gate is not a test for "has an Euler product."** A genuine degree-2 Euler
product with `α = 2.3, 1/α`, legitimate in the Selberg class, violating
Ramanujan, is **rejected** at `p = 5` with `c_p = 65.24`. The gate tests the
local bound `|α_j| ≤ √p`, and the closed form pins the failure point at exactly
`√p` (`1.41421356` for p = 2, `9.84885780` for p = 97). Claiming it detects
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

> `c_p ≤ d` holds **exactly when `δ ≤ ½`**, simultaneously at every place.

So `c_p` is blind on `|δ| ≤ ½` and not beyond it: `δ = 0.1` is a function the
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

The instrument, not the strategy. `c_p ≤ d` is a cheap, exact, coefficient-only
Gate 3 test with measured power and a stated blindness threshold, the thing to
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
