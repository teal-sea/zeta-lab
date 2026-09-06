# 06. Hilbert–Pólya, Berry–Keating, and the GUE

*Or: the spectral dream. Why "there ought to be a differential equation behind this" is the right
instinct, why nobody has produced the equation, and why the zeros nevertheless behave, measurably, on
your laptop, like the energy levels of a chaotic quantum system.*

## The short version

If you could exhibit a self-adjoint operator `H` whose spectrum is exactly the ordinates `γ_n` of the
non-trivial zeros, RH would follow in three lines, because self-adjoint operators have real spectrum.
That is the Hilbert–Pólya idea: a **strategy, not a theorem**. Nobody has built such an operator out of
anything but the zeros themselves. Two things keep it from being wishful thinking. First, the explicit
formula (`docs/04-explicit-formula.md`) has the exact shape of a *trace formula*, spectral side =
geometric side, zeros on the left, primes on the right. That is also the shape of Selberg's trace
formula for hyperbolic surfaces (where the analogue of RH is a **THEOREM**), of Gutzwiller's
periodic-orbit formula in quantum chaos, and of the Lefschetz fixed-point formula over finite fields
(where RH is a **THEOREM**: Weil 1948, Deligne 1974). Second, the zeros *statistically* behave like
eigenvalues of a large random Hermitian matrix from the Gaussian Unitary Ensemble: Montgomery's pair
correlation `1 − (sin πr/πr)²`, recognised by Dyson over tea at the IAS in 1972, confirmed by Odlyzko's
computations at astronomical height. Below, everything is labelled THEOREM, CONJECTURE, or HEURISTIC.

---

## 1. Hilbert–Pólya: what it buys, and what it does not

Write the zeros as `ρ = 1/2 + iγ`. Then `RH ⟺ every γ is real`: the functional equation
(`docs/03-functional-equation.md`) already forces zeros into conjugate quadruples, and RH says the
quadruples collapse onto the line. If `H` is self-adjoint and `Hv = λv` with `v ≠ 0`,

```
λ ⟨v,v⟩ = ⟨Hv, v⟩ = ⟨v, Hv⟩ = λ̄ ⟨v,v⟩   ⟹   λ = λ̄.
```

**CONJECTURE (Hilbert–Pólya).** There is a naturally defined self-adjoint operator whose eigenvalues
are the `γ_n`. Then RH.

Two caveats, both load-bearing.

**(a) As literally quoted, it is vacuous.** If RH is true then every `γ_n` is real and the diagonal
operator `(a_n) ↦ (γ_n a_n)` on `ℓ²` is self-adjoint with exactly that spectrum. So "some self-adjoint
operator exists" is *equivalent* to RH, not a route to it. All the content is in *naturally*: the
operator must come from arithmetic or geometry, built without knowing where the zeros are.

**(b) Self-adjoint is strictly stronger than symmetric.** Any operator with spectrum `{γ_n}` is
unbounded, and for unbounded operators mere symmetry (`⟨Hu,v⟩ = ⟨u,Hv⟩` on a domain) is not enough: it
does force any *eigenvalues* to be real, but the spectral theorem, and with it a spectrum contained in
`ℝ`, and a complete set of eigenvectors, needs self-adjointness. A symmetric operator with mismatched
deficiency indices can have spectrum filling an entire half-plane. Self-adjointness is a statement
about *domains*: `H` and `H*` must have the same one. That is why "boundary conditions" recurs below as
the sticking point. It is the whole problem in disguise.

The attribution is folklore, neither Hilbert nor Pólya published it. The commonly cited source is a
1982 letter from Pólya to Odlyzko recalling that in Göttingen (around 1912–14) Landau asked him for a
*physical* reason to believe RH, and he suggested the `γ` might be eigenvalues of a self-adjoint
operator. Hilbert's role is undocumented. The name is a label, not a citation.

---

## 2. Weyl's law already rules out most candidates

Use the one hard piece of data: the density of zeros. From `docs/03-functional-equation.md` and
`zeta/zeros.py`,

```
N(T) = (T/2π) log(T/2π) − T/2π + 7/8 + S(T),      S(T) small
```

so the mean gap near height `T` is `2π/log(T/2π)`. At `T = 1419` (the 1000th zero) that predicts
`1.159`; the measured mean gap over the last 100 of the first 1000 zeros is `1.171`. At the 10²²-nd
zero, height `T ≈ 1.37 × 10²¹`, the mean gap has shrunk only to `≈ 0.134`.

Compare Weyl's law: for the Laplacian on a compact `d`-manifold, `#{√λ ≤ T} ~ c·T^d`. Ours grows like
`T log T`, which is not `T^d` for any integer `d`. **So `H` is not the Laplacian of any manifold.** The
`T log T` shape is what one degree of freedom on a logarithmically non-compact phase space gives. That
is where Berry and Keating start, and it is also, as we will see in §5, a proof that the most
seductive analogy in the subject cannot work.

---

## 3. Berry–Keating: H = xp

**Status: HEURISTIC**, a semiclassical model, not a construction. (Berry raised "zeta as a model for
quantum chaos" in the mid-1980s; the `xp` proposal is developed in Berry–Keating's work of the late
1990s, including their 1999 *SIAM Review* survey.)

Take `H(x,p) = xp` on a one-dimensional phase space. Hamilton's equations give `ẋ = x`, `ṗ = −p`, so
`x(t) = x₀e^t`, `p(t) = p₀e^{−t}`: every trajectory rides a hyperbola `xp = E` at exponential speed.
This is the simplest *hyperbolic* flow there is, with Lyapunov exponent exactly `1`. Remember that `1`.

### 3.1 The counting function comes out right

Semiclassically, the number of states below energy `E` is the phase-space area below `E` divided by the
Planck cell `2πħ` (set `ħ = 1`). The region `0 < xp ≤ E` has infinite area, so regularise with `x ≥ l_x`,
`p ≥ l_p`:

```
Area = ∫_{l_x}^{E/l_p} (E/x − l_p) dx = E·log( E/(l_x·l_p) ) − E + l_x·l_p
```

(computed symbolically, not by hand-waving). Choose the cutoffs to enclose one Planck cell,
`l_x·l_p = 2πħ = 2π`, and divide by `2π`:

```
N(E) = (E/2π) log(E/2π) − E/2π + 1 .
```

Against Riemann–von Mangoldt, `(T/2π)log(T/2π) − T/2π + 7/8`: **the two leading terms agree exactly.**
The constant comes out `1` rather than `7/8`; the discrepancy is attributed to a Maslov-type phase that
a crude rectangular cutoff cannot be expected to capture. Two matching terms of a two-term asymptotic
out of a one-line integral is the first reason anyone takes `xp` seriously.

### 3.2 Why the primes are periodic orbits

Gutzwiller's trace formula (**THEOREM**, in the semiclassical asymptotic sense, for chaotic systems)
says the oscillating part of the density of states is a sum over *classical periodic orbits*, an
unstable primitive orbit of period `T_p` traversed `k` times with Lyapunov exponent `λ` contributing
with amplitude falling like `T_p·e^{−kλT_p/2}`.

Now the explicit formula in the same shape. Differentiating the formula for `ψ` (see the
`prime_spectrum` docstring in `zeta/explicit.py`) gives, with `u = log x`,

```
Σ_{n≥2} Λ(n) δ(u − log n)  =  e^u  −  2 e^{u/2} Σ_{γ>0} cos(γ u)  −  1/(e^{2u} − 1)
```

Read `u` as *time* and `γ` as *energy*. The "orbits" are the terms `n = p^k`: period `T = k log p`,
amplitude `Λ(n)/√n = (log p)·p^{−k/2}`. Put `T_p = log p` and `λ = 1` into Gutzwiller's
`T_p e^{−kλT_p/2}` and you get exactly `(log p)·p^{−k/2}`. **Every prime behaves like a primitive
periodic orbit of period `log p`, and every orbit has the same instability exponent `λ = 1`**, the
exponent of the `xp` flow. That is the second reason anyone takes `xp` seriously.

You can *see* the orbits: `zeta.explicit.prime_spectrum` evaluates `−2 Σ_{γ>0} w(γ) cos(γu)` from a list
of zeros and returns a spike train with a peak at `u = log p^k`, of height `Λ(n)/√n`, and nowhere else.

### 3.3 The unresolved problems

1. **No discrete spectrum.** The symmetrised `Ĥ = (xp + px)/2 = −i(x d/dx + 1/2)` on `L²(0,∞)` really is
   self-adjoint, but its spectrum is *all of `ℝ`, continuously*: `ψ_E(x) = x^{−1/2+iE}` satisfies
   `Ĥψ_E = Eψ_E` for **every** real `E`, and none of them is normalizable. (`Ĥ` generates dilations;
   under the Mellin transform that built `ξ` in `docs/03-functional-equation.md` it is just
   multiplication by `E`.) So `xp` has no eigenvalues at all until you truncate phase space or impose
   boundary conditions, and **no truncation is known that yields the `γ_n`**. Regularising the *count*
   (§3.1) is easy; regularising the *operator* is the whole problem, exactly the symmetric-versus-
   self-adjoint distinction of §1(b).
2. **The sign is wrong.** In Gutzwiller the orbit sum *adds* to the density of states; in the explicit
   formula the prime sum enters the density of zeros with the opposite sign. The zeros look less like
   emission lines than like absorption lines, missing frequencies in a continuum. Connes' construction
   (§4) reproduces precisely that.
3. **Time-reversal symmetry must be broken** (§8). Under `p → −p`, `xp → −xp`, so `xp` is not
   time-reversal invariant in the usual sense, consistent with the GUE statistics, but no honest
   dynamical system realising the required structure is known.
4. **Circularity.** The orbits of period `log p` with weight `log p` were *read off* the explicit
   formula. No independently defined system is known whose length spectrum is `{k log p}`. Until one
   exists, this is a translation of the problem, not a solution.

Attempts to promote the heuristic to an operator continue; I believe Bender, Brody and Müller proposed
a PT-symmetric candidate in 2017 (verify before quoting it). It does not prove RH, the required
self-adjointness is exactly what is not established.

---

## 4. Connes: the adelic trace formula

**Status: a THEOREM in a restricted (semilocal) setting; the general case is *equivalent* to RH rather
than a proof of it.**

Connes (*Selecta Mathematica*, 1999) builds a noncommutative space, the adèle class space `𝔸_ℚ/ℚ*`,
carrying an action of the idèle class group, and shows a trace formula for that action has the exact
shape of Weil's explicit formula, with the zeros appearing as an *absorption* spectrum (§3.3, point 2).
He proves the trace formula with only finitely many places included; the full statement, all places at
once, is equivalent to RH.

That equivalence predates the framework:

**THEOREM (Weil's positivity criterion).** RH holds if and only if a certain explicit Hermitian form,
obtained by feeding `f ⋆ f̄*` into the explicit formula, is positive semi-definite for all admissible
test functions `f`.

Internalise it: *we already know what kind of input proves RH.* It is a positivity. What is missing is
any source for it. Hold that thought, in the function-field world the positivity has a known source,
and knowing where it comes from there is what makes the failure over `ℤ` so precise.

---

## 5. Selberg: the dream realised, for the wrong object

**Status: THEOREM (Selberg, 1956).** Let `X = Γ\ℍ` be a compact hyperbolic surface.

- `Δ` on `X` is self-adjoint and non-negative; write its eigenvalues `λ_n = 1/4 + r_n²`.
- Closed geodesics play the role of primes. The **prime geodesic theorem** gives `~ e^L/L` primitive
  closed geodesics of length `≤ L`, *exactly* `π(x) ~ x/log x` under `x = e^L`. So `ℓ ↔ log p`.
- The **Selberg zeta function** `Z(s) = Π_{primitive γ} Π_{k≥0}(1 − e^{−(s+k)ℓ_γ})` has its non-trivial
  zeros at `s = 1/2 ± i r_n`.
- The **Selberg trace formula** equates a spectral sum over `r_n` with a geometric sum over geodesic
  lengths: structurally identical to `docs/04-explicit-formula.md`.

RH for `Z` is then a theorem for an almost embarrassing reason: `Δ` is self-adjoint with `λ_n ≥ 0`, so
`r_n` is real whenever `λ_n ≥ 1/4` and `s = 1/2 ± ir_n` sits on the critical line. The exceptions are
the finitely many *exceptional eigenvalues* `0 ≤ λ < 1/4`, giving imaginary `r` and hence finitely many
zeros on the real segment `(0,1)`, the structural analogue of Siegel zeros. Hilbert–Pólya, delivered.

**Why it does not transfer.** One soft reason, one decisive one.

- *Soft:* the logic runs backwards. Selberg is *handed* the surface; the "primes" (geodesic lengths) are
  an output of the geometry. Over `ℚ` we have the primes and no surface.
- *Decisive:* the counting laws disagree. Weyl's law on a surface of area `A` gives
  `#{r_n ≤ T} ~ (A/4π)·T²`. Riemann's zeros grow like `(T/2π)·log T`. **No hyperbolic surface has the
  right density of states.** This is not "we have not found it yet", it is a proof that this door is
  closed. Whatever `H` is, it is a one-degree-of-freedom object (§2). The Selberg picture is the right
  *shape* and the wrong *size*.

---

## 6. Function fields: where RH is a theorem, and what is missing over ℤ

The most instructive comparison in the subject. Let `C` be a smooth projective curve of genus `g` over
`F_q`, and `Z(C,T) = exp( Σ_{n≥1} #C(F_{q^n})·T^n/n )`.

**THEOREM (Weil, 1948; Hasse in the 1930s for elliptic curves).** `Z(C,T) = P(T)/((1−T)(1−qT))` with
`P ∈ ℤ[T]` of degree `2g`, and if `P(T) = Π_{i=1}^{2g}(1 − α_i T)` then

```
|α_i| = √q      for every i,
```

which under `T = q^{−s}` puts every zero exactly on `Re(s) = 1/2`. That *is* RH for `C`.
**THEOREM (Deligne, 1974)** extends it to smooth projective varieties of any dimension over `F_q`.

**The geometry available there** is everything Hilbert–Pólya asks for:

- *An honest operator*: **Frobenius** `F` acting on ℓ-adic cohomology `H¹(C̄, ℚ_ℓ)`, a vector space of
  dimension exactly `2g`.
- *An honest trace formula*: the **Lefschetz fixed-point formula**,
  `#C(F_{q^n}) = q^n + 1 − Σ_i α_i^n = Σ_j (−1)^j tr(F^n | H^j)`. Counting points, the "primes", *is*
  taking traces of powers of one operator, whose eigenvalues are the `α_i`. Here the explicit formula
  is not merely trace-formula-*shaped*; it *is* a trace formula.
- *An honest substitute for self-adjointness*: **positivity.** `F` is not Hermitian, but on the Jacobian
  the Rosati involution `†` attached to a polarisation is a *positive* involution and `F F† = q`. An
  operator with `F*F = q` against a positive-definite form has `|α|² = q`. Weil's original argument runs
  this through intersection theory on the surface `C × C`, where the needed inequality is of
  Castelnuovo–Severi / Hodge-index type. **The engine of the proof is a positivity from intersection
  theory on a surface.**

**What is missing over ℤ**, precisely:

1. **No base to take a product over.** Weil needs the surface `C ×_{F_q} C`. `Spec ℤ` is curve-like of
   dimension one, but there is no field beneath it: `ℤ ⊗_ℤ ℤ = ℤ`, so the product collapses. No surface,
   no intersection theory, no Hodge index. (Hence the "field with one element" programmes: Soulé,
   Deitmar, Connes–Consani, all **conjectural**; no proof of RH has come from them.)
2. **No single global Frobenius.** Over `F_q` one operator governs all the point counts. Over `ℚ` there
   is a Frobenius per prime and no known object on which they act simultaneously with a Lefschetz
   formula. Constructing an arithmetic cohomology for `Spec ℤ` is Deninger's programme; the sought
   statement, `ξ` as a regularised determinant of an infinitesimal generator, is **conjectural**, and
   I would check its precise formulation before quoting it.
3. **No home for the archimedean place.** Over `F_q` all places are alike. Over `ℤ` the Γ-factor in `ξ`
   *is* the place at infinity, and it has no known interpretation as a fibre of anything.
4. **Finite versus infinite dimensional.** RH for a curve concerns the `2g` eigenvalues of a matrix,
   finite linear algebra, `Z` a rational function of `q^{−s}`. RH over `ℤ` concerns an entire function
   of order 1 with infinitely many zeros. Every finiteness the proof leans on evaporates.

One more asymmetry: over function fields even the *statistics* are theorems. **THEOREM (Katz–Sarnak,
1999)**, via Deligne's equidistribution theorem: for various families of curves over `F_q` the
normalised Frobenius eigenvalues follow random-matrix laws in the large-`q` limit. Over `ℤ` that is
the conjecture we turn to now.

---

## 7. Montgomery, Dyson, and the pair correlation

In 1972 Hugh Montgomery, then a graduate student, was studying the *spacings* of zeros. At tea at the
Institute for Advanced Study he was introduced to Freeman Dyson and described the pair-correlation
function he had found. Dyson recognised it at once: it is the pair correlation of eigenvalues of a
random matrix from the **Gaussian Unitary Ensemble**, which he had computed a decade earlier while
modelling nuclear energy levels.

### 7.1 Unfolding, and why it is not a fudge

Gaps shrink like `2π/log(T/2π)`, so raw gaps at height 100 and 10²⁰ are not comparable. *Unfolding*
applies the smooth counting function to each zero so the mean spacing becomes exactly 1. Following
`zeta.statistics.unfold`:

```
γ̃_n = θ(γ_n)/π        (θ = Riemann–Siegel theta, zeta.statistics.riemann_siegel_theta)
```

This is not ad hoc. Because `N(T) = 1 + θ(T)/π + S(T)` is an *identity* (see the module docstring of
`zeta/zeros.py`), we get exactly `γ̃_n = n − 1 − S(γ_n)`. **The spacing statistics of the unfolded zeros
are precisely the statistics of the fluctuation `S(T)`.** Over the first 1000 zeros I measure
`max |γ̃_n − (n−1)| = 1.234`, i.e. `|S| ≤ 1.24` there, and mean unfolded spacing `0.99997`.

### 7.2 The statement

**CONJECTURE (Montgomery, 1973).** As `T → ∞` the density of pairs of zeros at unfolded separation `r`
tends to the GUE / sine-kernel two-point function

```
R₂(r) = 1 − ( sin(πr) / (πr) )²        (zeta.statistics.montgomery_prediction)
```

**THEOREM (Montgomery, 1973, assuming RH).** The corresponding asymptotic holds for test functions
whose Fourier transform is supported in `(−1,1)`. Outside that range it is conjectural, and that is
where all the arithmetic difficulty lives. Rudnick and Sarnak (1996) extended restricted-support
agreement to `n`-level correlations and to general automorphic `L`-functions; Hejhal had earlier
handled the triple correlation. Every such result carries a support restriction. **No unconditional,
unrestricted GUE statement about `ζ` is known.**

### 7.3 Level repulsion versus Poisson

Two null models for a unit-density sequence:

- **Poisson** (independent levels, expected for a generic *integrable* system): `P(s) = e^{−s}`,
  *maximal* at `s = 0`. Levels clump; tiny gaps are common.
- **GUE**: `P(s) ~ s²` as `s → 0`, quadratic **level repulsion**, because a degeneracy of a Hermitian
  matrix is a codimension-3 condition, so near-degeneracies are rare. The Wigner surmise is
  `P(s) = (32/π²)s²e^{−4s²/π}` (verified symbolically to have unit mass and unit mean, variance
  `3π/8 − 1 = 0.1781`); the exact law is a Fredholm determinant of the sine kernel, and the surmise is
  good to about a percent. `zeta/statistics.py` supplies both (`wigner_surmise_gue`,
  `gue_spacing_exact`) plus `poisson_spacing`.

Here are the first 1000 zeros (`γ ≤ 1419.4`), unfolded, against a simulated GUE (400 matrices of size
300, central 20% of each spectrum, 23600 spacings) and against Poisson:

```
                        zeros(1000)    GUE (sim)    Wigner surmise    Poisson
mean spacing               1.0000        1.0000          1.0000        1.0000
variance of spacing        0.1444        0.1808          0.1781        1.0000
P(spacing < 0.2)           0.0030        0.0089          0.0084        0.1813
smallest gap observed      0.1376, —,
```

A Poisson process puts 18% of gaps below 0.2; the zeros put 0.3% there. They are not random points,
they are **rigid**. And the pair correlation from those same 1000 zeros (pairs binned by unfolded
separation, normalised to unit density; edge effects here are well under 1%):

```
   r      empirical    1 − (sin πr/πr)²
 0.05       0.000            0.008
 0.25       0.110            0.189
 0.45       0.330            0.512
 0.65       0.820            0.810
 0.85       1.000            0.971
 1.05       0.940            0.998
 1.45       1.070            0.953
 2.05       0.970            0.999
 3.05       0.930            1.000
```

The **correlation hole** near `r = 0` is already visible in a thousand zeros.

### 7.4 Be honest about the fit

Those numbers are *more* rigid than GUE at this height: variance 0.144 against 0.180, correlation hole
too deep. That is not noise, and not a failure of the conjecture. Convergence is genuinely slow and the
finite-height deviations are systematic and **arithmetic**, modelled well by semiclassical formulas
that put the prime sum back in (the Bogomolny–Keating and Berry work on arithmetic corrections). The
primes are still fingerprinting the statistics; only in the limit do they average away.

**Odlyzko's computations** are why the conjecture is believed so strongly: from his 1987 *Mathematics of
Computation* paper on spacings, through large-scale computations around the 10²⁰-th zero in the late
1980s and later around the 10²²-nd, he evaluated enormous consecutive blocks at heights where the mean
gap is `≈ 0.13`. There the empirical spacing and pair-correlation curves sit on the GUE predictions to
plotting accuracy. (I do not quote the exact zero-counts from his paper titles from memory, `10²⁰` and
`10²²` are the landmarks; check the counts before repeating them.)

---

## 8. The quantum-chaos framing

**CONJECTURE (Bohigas–Giannoni–Schmit, 1984).** The spectral statistics of a quantum system with a
chaotic classical limit follow random-matrix theory: **GOE** (β = 1) with time-reversal symmetry,
**GUE** (β = 2) with that symmetry broken.

Zeta is GUE. So: *the zeros look like the spectrum of a quantised chaotic system with broken
time-reversal symmetry.* The mechanism joining the two conjectures is the orbit sum of §3.2. In a
time-reversal-invariant system every orbit has a partner traversed backwards with the same period; the
two contributions add coherently, doubling the fluctuation variance and producing GOE, whose repulsion
is only linear (`P(s) ~ s`). In the explicit formula each prime power appears **once**, with no partner,
the structure of a system without time-reversal symmetry, giving quadratic repulsion. That is the
cleanest heuristic for GUE over GOE, and the sharpest structural demand on any hypothetical `H`: it
cannot be a real symmetric operator, or the statistics come out wrong. It also explains both why `xp`
is attractive (hyperbolic ⇒ chaotic; `xp → −xp` under `p → −p` ⇒ no naive time-reversal symmetry) and
why it is not enough (§3.3).

---

## 9. Scorecard

| Statement | Status |
|---|---|
| A *natural* self-adjoint `H` with spectrum `{γ_n}` exists | **CONJECTURE** (Hilbert–Pólya) |
| Semiclassical `xp` reproduces `(T/2π)log(T/2π) − T/2π` | **THEOREM** (an integral), of a *model* |
| Quantised `xp` gives the `γ_n` | **HEURISTIC**; unresolved (domain, sign, orbits) |
| Weil's positivity criterion ⟺ RH | **THEOREM** |
| Connes' trace formula, semilocal case | **THEOREM**; full case ⟺ RH |
| RH for the Selberg zeta of a compact hyperbolic surface | **THEOREM** (up to finitely many exceptional eigenvalues) |
| No hyperbolic surface has zeta's density of states | **THEOREM** (Weyl: `T²` vs `T log T`) |
| RH for curves / varieties over `F_q` | **THEOREM** (Weil 1948 / Deligne 1974) |
| Pair correlation, restricted support, assuming RH | **THEOREM** (Montgomery, 1973) |
| Pair correlation, full range; full GUE statistics | **CONJECTURE**; numerically overwhelming |
| Random-matrix statistics for families over `F_q` | **THEOREM** (Katz–Sarnak, 1999) |

The pattern is hard to miss. Wherever the geometry is *handed to us*, a hyperbolic surface, a curve
over a finite field, the spectral dream is a theorem, and its engine is either self-adjointness or a
positivity from intersection theory. Over `ℤ` we have the trace formula, the statistics, the density of
states, and no geometry.

---

## Where to go next

- **`zeta/statistics.py`**, the laboratory for this document: `zero_ordinates` (bulk zeros by a
  vectorised Riemann–Siegel scan), `unfold` and `nearest_neighbour_spacings` (§7.1),
  `wigner_surmise_gue` / `gue_spacing_exact` / `poisson_spacing` (§7.3), `pair_correlation` and
  `montgomery_prediction` (§7.2), `form_factor` for the Fourier-side view. Then
  `level_repulsion_report(gammas)`, KS statistics against exact GUE, the surmise, and Poisson, and
  `compare_to_random_matrix(...)`, which draws actual GUE matrices (`gue_eigenvalues`, `unfold_gue`)
  and runs a two-sample KS test: zeros against matrices, no fitted model in between. Plot the spacing
  histogram against both `(32/π²)s²e^{−4s²/π}` and `e^{−s}`; the two curves are nowhere near each
  other, and the data picks one without ambiguity.
- **`zeta/explicit.py`**, `prime_spectrum` and `spectrum_peaks`: the periodic-orbit sum made audible.
  Every peak is an "orbit" of period `log p^k`.
- **`docs/04-explicit-formula.md`**: the trace formula you already have. This document is an attempt
  to name the operator whose trace it is. **`docs/05-de-bruijn-newman.md`**, the other main attack:
  deform `ξ` by heat flow instead of diagonalising it. **`docs/08-why-it-is-hard.md`**, the barriers,
  collected.
- **Experiment.** Split your zeros into a low block and a high block and compare spacing variances
  against `0.178`. The high block should sit closer. That drift *is* the arithmetic correction of
  §7.4, the primes, on their way to averaging out.
