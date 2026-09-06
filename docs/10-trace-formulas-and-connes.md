# 10. Trace Formulas and the Connes Program

*"The explicit formula looks like modal analysis. So what is the structure, and who gets to tap it?"*

## The short version

A **trace formula** is an exact accounting identity between two lists: the resonant frequencies of
a system (its *spectrum*) and its closed round-trip paths (its *geometry*). You have already
verified one, the theta identity of `docs/02-theta-heat-and-modularity.md` is the trace formula of
a circle. The **Weil explicit formula** is the same kind of identity with the zeros of zeta as the
modes and the prime powers as the orbits; `zeta/weil.py` evaluates both sides independently and
measures their agreement at `~1e-31`. Weil distilled from the formula a **THEOREM**: RH is
*equivalent* to a certain quadratic form never going negative, `zeta.weil.weil_functional` computes
that form from primes alone, and its measured margin above zero is controlled by the lowest zero,
`γ₁ = 14.1347…`. In one parallel world the dream is already a theorem: Selberg's trace formula for
hyperbolic surfaces, where self-adjointness does the work. Over the integers we have the trace
formula and no operator; Connes' noncommutative-geometry **PROGRAM** is the most developed attempt
to build the missing space, on which RH becomes exactly a positivity statement about a flow. A deep
reformulation, not a proof. Everything below is labelled THEOREM, CONJECTURE, or PROGRAM.

---

## 1. What a trace formula is: a tool you already own

Start from matrices, where the word "trace" lives: for a symmetric matrix, the trace, the sum of
the diagonal, equals the sum of the eigenvalues. One number, computable two ways: from the entries
(how the system is built) or from the spectrum (how it rings). Any identity of that shape is a trace
formula. Engineers meet this daily as **modal analysis**: tap a structure and record the response,
in the frequency domain, peaks at the natural frequencies (the *spectral* readout); in the time
domain, echoes at the round-trip travel times of pulses bouncing through the structure (the
*geometric* readout). Same signal, two descriptions, each determining the other.

The baby case in this repository is the heat kernel of `docs/02-theta-heat-and-modularity.md`,
evaluated at coincident points, the trace of the heat operator on a circle:

```
    Σ_{n ∈ ℤ}  exp(-4π²n²t)     =     Σ_{m ∈ ℤ}  (4πt)^(-1/2) exp(-m²/(4t))

    [spectral side: one term per mode,      [geometric side: one term per closed
     eigenvalue 4π²n² of -d²/dx²]            path winding m times, length |m|]
```

Left: every vibration mode of the circle, weighted by how much survives diffusion for time `t`.
Right: every closed walk around the circle, weighted by how likely a random walker is to complete
it. The identity is Poisson summation, `zeta.core.theta_heat_poisson_defect` measures its defect
at `0.0` to 40 digits (`docs/02` §7). Modes left, closed orbits right, an exact equals sign
between: that is the entire concept, and the rest of this document is that concept wearing heavier
machinery.

> **Plain-words recap.** A trace formula says the list of frequencies at which a system rings and
> the list of its closed round-trip paths carry the same information, tied by an exact identity,
> not an analogy. You verified one in `docs/02`: heat on a circle, modes left, windings right.

---

## 2. The Weil explicit formula *is* a trace formula

`docs/04-explicit-formula.md` built von Mangoldt's identity, the prime staircase `ψ(x)` as a
smooth term minus one wave per zero, and its dual: a bare sum of cosines over the zeros develops
spikes at exactly `u = log p^k` (`zeta.explicit.prime_spectrum`). The rigorous symmetric statement
is the **Riemann–Weil (Guinand–Weil) explicit formula**, phrased with a *test function*, the shape
of the tap: probe both sides with a smooth window `h` and its Fourier partner `g`, instead of
asserting an identity between spike trains.

**THEOREM (the explicit formula; Riemann 1859 in outline, von Mangoldt 1895, Guinand and Weil in
this symmetric form, c. 1948–1952).** Let `h(r)` be an even test function, analytic and rapidly
decaying on a strip `|Im r| ≤ 1/2 + δ` (fine print in Section 3), with Fourier partner
`g(u) = (1/2π) ∫ h(r) e^(-iru) dr`. Write every non-trivial zero as `ρ = 1/2 + iγ_ρ`, so `γ_ρ` is
real exactly when that zero obeys RH, and sum over all zeros with multiplicity, both signs of `γ`.
Then, in the convention implemented by `zeta/weil.py`:

```
    Σ_ρ h(γ_ρ)  =  h(i/2) + h(-i/2)                                  [the pole of ζ at s = 1]
                 + (1/2π) ∫ h(r) [Re ψ(1/4 + ir/2) - log π] dr       [ψ = Γ'/Γ, digamma]
                 - 2 Σ_{n≥2} Λ(n) n^(-1/2) g(log n)                  [Λ as in docs/04]
```

Conventions differ across the literature (factors of `2π`, where `log π` sits, one- versus
two-sided sums), so the module trusts nothing unmeasured: the placement above was *calibrated* by
computing the zero side (from cached, independently verified zeros) and the arithmetic side
(Γ-factors, primes, quadrature, no zeros anywhere) separately, for test functions from three
unrelated families, and requiring agreement; `tests/test_weil.py` re-runs the calibration.
Re-measured while writing this document, for the Gaussian window `h(r) = exp(-0.01 r²)` at
`dps = 30`:

```
    zero side  (the first 28 pairs ±γ suffice)    0.299396022507559155789163943544
    ---------------------------------------------------------------------------
    h(i/2) + h(-i/2)   [= 2e^(a/4) exactly]      +2.005006255211590
    archimedean integral                         -1.705593433712344
    prime-power sum    (n = 2,3,4,5,7 only)      -0.000016798991687
    ---------------------------------------------------------------------------
    arithmetic side, total                        0.299396022507559155789163943544

    |zero side - arithmetic side|  ≈  7e-32
```

Read the table as physics. The zeros are the **modes**: 90.6% of the spectral side is the first
zero pair at `γ₁ = 14.1347…`, the fundamental; a decay envelope certifies everything past the 28th
zero negligible at this precision. The prime powers are the **closed orbits**: each `n = p^k`
enters at "time" `log n = k·log p`, the `k`-th traversal of a primitive orbit of length
`log p`: and here 99.99998% of the prime side is the single shortest orbit, `n = 2`, at
`log 2 = 0.693`. The pole and digamma
lines are, in the geometric programs of `docs/09-new-ontologies.md`, the contribution of the *place
at infinity*, the one place with no prime. And note the cancellation: terms of size 2 conspire to
reproduce a spectral side of size 0.3 to thirty-one digits. The identity has no slack anywhere
(Section 3 pushes it through *eighteen orders* of cancellation, and it still balances).

The instrument, briefly. `zeta.weil` builds admissible pairs `(h, g)` in closed form,
`gaussian_pair(a)`, `fejer_pair(b)` (whose triangle-shaped `g` has *compact support*, making the
prime sum exactly finite: `n ≤ 54` for `b = 2`), `autocorrelation_pair(coeffs, …)`, and
`explicit_formula_sides(h, g)` returns both sides plus explicit bounds on every truncation; the
residual must sit inside the accounted error, and the tests assert exactly that.

> **Plain-words recap.** Probe the zeros with a smooth window and you get a number; the explicit
> formula computes the same number from the primes plus two "infinity" terms, exactly, measured
> here to thirty-one digits. Zeros play the modes; prime powers play the closed orbits, with
> lengths `log p, 2 log p, …`. It is a trace formula with the trace, the underlying operator and
> space, missing.

---

## 3. Weil's positivity criterion

Ask the engineer's question: what forces every mode frequency real, no growing solutions? For
physical systems the answer is always some positivity: positive definite mass and stiffness
matrices, a passive network, an energy that cannot go negative. Weil found the exact statement.

Let `W(h) = Σ_ρ h(γ_ρ)`, the spectral side, hence by Section 2 also computable from the primes with
no zeros involved; that arithmetic-side evaluation is exactly `zeta.weil.weil_functional(h, g)`. Say
`h` is of **positive type** if `h = |f̂|²` on the real axis for some test function `f`,
equivalently, its Fourier partner `g` is a self-correlation `f ⋆ f~`. Such `h` are automatically
`≥ 0` on the real axis, but *not* off it.

**THEOREM (Weil, 1952; refined 1972).** RH holds **if and only if** `W(h) ≥ 0` for every admissible
`h` of positive type.

One direction is immediate: under RH every `γ_ρ` is real, where `h ≥ 0`. The other is the content:
a zero off the line has a genuinely complex `γ`, so `h` gets evaluated off the real axis, where
`|f̂|²` no longer means anything positive, and one can engineer an admissible `h` making
`W(h) < 0`. So `W`, quadratic in `f` the way `x ↦ xᵀAx` is quadratic in `x`, is positive
semidefinite *exactly* when RH holds: an explicitly computable infinite-dimensional "stiffness
matrix", built from primes and Gamma factors, with no negative directions.

The honest fine print: the **admissible class**. The precise smoothness, decay, and analyticity
conditions on the test functions differ between Weil's papers, Bombieri's treatments, and the
textbooks (compactly supported smooth `f` versus analyticity-in-a-strip formulations). The
equivalence is robust across the usual choices, and every pair built by `zeta.weil` is of positive
type under any of them, but neither this document nor the module re-derives the minimal
hypotheses; check a source before leaning on the exact class. Note also that a window with `g`
supported inside `(-log 2, log 2)` has *no prime terms at all*, positivity in such
restricted-support regimes has been proven in the literature (commonly cited; scope unverified
here). The difficulty is uniform positivity over *all* admissible windows, where every prime gets a
vote.

What does measurement say? `positivity_probe` scans families of positive-type pairs and certifies
the sign of `W` (escalating precision until the sign clears the noise floor);
`near_tightness_report` asks what controls the margin. Measured, and pinned in `tests/test_weil.py`:

- Every computed `W` is positive, but the infimum over each family is `0`, approached as the window
  concentrates on the zero-free gap `(-γ₁, γ₁)`.
- Along the Gaussian family the collapse is exponential with exponent *the first zero*: the fitted
  slope of `log W` against `a` is `-199.79051`, against the prediction `-γ₁² = -199.79045`,
  because `W ≈ 2h(γ₁)` once the window sees no other zero. At `a = 0.2`, `W = 8.86e-18` out of
  pieces of size ~2, eighteen orders of cancellation, and the formula still balances.

Be clear what all that observed positivity is worth as evidence (`docs/00-orientation.md` §6):
**nothing**. Each `W(h) ≥ 0` reflects zeros already verified on the line; a true negative value
would disprove RH, but no finite list of successes supports it, `docs/07-equivalences-and-criteria.md`
§7 is blunt that the criterion admits no meaningful numerical test *of RH*. The measurements' value
is reconnaissance, they locate where the form is tightest, and the criterion's value is
structural: it names the *kind* of input a proof needs. Not a clever inequality; a source of
positivity. In the one parallel universe where this criterion has been proven, the source was
geometric: an intersection-theory inequality on a surface (`docs/09` §1.3). That is why every
program in this document is a hunt for geometry.

> **Plain-words recap.** RH is equivalent to: a specific quadratic form, an infinite "stiffness
> matrix" written down from primes and Gamma factors, is never negative over a class of smooth
> test windows (a theorem, with fine print on the window class). The lab computes the form from
> primes alone and finds it positive but *asymptotically tight*, the margin controlled by the
> lowest zero, an observation about verified zeros, not evidence for RH. The criterion matters
> because it names the missing ingredient: a reason for positivity.

---

## 4. Selberg: the world where the dream works

There is a setting where all of this, trace formula, zeta function, positivity, RH, is simply
true, with proofs. What exists there is a parts list for what is missing here
(`docs/06-hilbert-polya-and-gue.md` §5 has the fuller story).

Take a **compact hyperbolic surface**: a finite drumhead of constant negative curvature, closed on
itself, no boundary. Its Laplacian, the operator whose circle version gave Section 1's modes, is
**self-adjoint**, the operator property that forces a real spectrum (the three-line argument of
`docs/06` §1); write the eigenvalues `λ_n = 1/4 + r_n²`. The primes' role is played by the **closed
geodesics**, closed orbits of a free particle on the surface, quantitatively so: about `e^L / L`
primitive closed geodesics have length up to `L`, which is the Prime Number Theorem
`π(x) ~ x/log x` under `x = e^L`. Geodesic length corresponds to `log p`, exactly Section 2's orbit
lengths.

**THEOREM (Selberg, 1956).** The spectral sum over the `r_n` equals a geometric sum over closed
geodesic lengths, structurally identical to the explicit formula. Package the geodesics into a
**Selberg zeta function** `Z(s)`, a product over primitive geodesics the way zeta is a product over
primes; its non-trivial zeros sit at `s = 1/2 ± i r_n`. Self-adjointness makes every `r_n` with
`λ_n ≥ 1/4` real, so "RH" for `Z` is a **THEOREM**, up to at most finitely many exceptional
eigenvalues `0 ≤ λ < 1/4`, which give finitely many zeros on the real segment.

What exists there and not here? Everything arrives *in the right order*. Selberg starts with the
space; the operator comes with it, self-adjointness included; the "primes", the geodesic lengths,
are an *output* of the geometry. Over the rationals the order is inverted: we possess the orbit
lengths `{k·log p}` and the trace formula they satisfy, and no space, no operator, no reason. And
one door is provably closed: by Weyl's law a hyperbolic surface has about `T²` modes below
frequency `T`, while zeta has `(T/2π) log T` zeros below height `T`, **no hyperbolic surface has
the right density of states** (`docs/06` §5). Whatever is being traced in Section 2 is something
stranger than a surface.

> **Plain-words recap.** On a curved closed drumhead the whole story is a theorem: trace formula,
> a prime number theorem for geodesics, and "RH", from self-adjointness, with finitely many
> exceptions. The enabling ingredient: the *space comes first*; the primes are read off it. For the
> integers we have the primes and no space, and a counting argument proves no ordinary surface can
> ever be that space.

---

## 5. Connes: noncommutative geometry and the adele class space

**Status: PROGRAM.** Deep theorems inside its own formalism; not a proof of RH, and not claimed to
be by its author.

First, noncommutative geometry, in two paragraphs. Quantum mechanics taught physics that a system
need not be a point moving in a space; it can be described entirely by its **algebra of
observables**, position, momentum, energy as operators (infinite matrices), measurement outcomes
read off their spectra. When the observables commute, this is ordinary geometry in disguise: a
commutative observable algebra is secretly the functions on an honest space, which can be rebuilt
from it (a classical **THEOREM** of operator theory, due to Gelfand and Naimark, stated here
qualitatively). When they do *not* commute, position and momentum being the founding example,
there is no underlying point-space at all, yet the algebra remains perfectly good to compute with:
it still supports measure, dimension, dynamics, and crucially **trace**. Connes' noncommutative
geometry develops exactly that: *define* a space to be its algebra of observables, and do geometry
with algebras where points fail.

Points fail, in practice, at **bad quotients**: glue together the points of each orbit of a group
action, and if the orbits are dense the classical quotient is mush, no continuous function
survives to tell points apart, while the observable-algebra description stays rich. That is the
situation with the primes. The **adeles** of the rationals are, in one sentence, all completions of
the rationals bundled into one object: the reals plus one `p`-adic number system per prime, the
`p`-adics measure a number as small when it is divisible by a high power of `p` (a pointer, not a
course; this repo does not develop them). The **adele class space** is the quotient of the adeles
by multiplication by nonzero rationals, a bad quotient of precisely the hopeless kind, on which
every prime acts at once. It carries a natural **scaling flow**, the noncommutative cousin of the
dilation operator from the Berry–Keating story (`docs/06` §3).

**THEOREM (Connes, 1999, Selecta Mathematica).** In a restricted ("semilocal") setting, finitely
many places at a time, a trace formula holds for this flow, and its shape is Section 2's formula:
the primes appear on the geometric side, one term per place, the archimedean terms arising from the
place at infinity. The zeros enter as an **absorption spectrum**, missing lines cut from a
continuum rather than emission peaks, matching the otherwise-puzzling sign of the prime sum
(`docs/06` §3.3). The full statement, all places at once, is **equivalent to RH**: in this frame RH
becomes exactly the Weil positivity of Section 3, now read as a statement about a trace on a
genuinely existing (noncommutative) space.

Honest status. What the program has certainly achieved is a *reformulation with structure*: the
explicit formula is no longer a trace formula in search of a space, a space exists, the trace is
honest, and "what is being traced," "why these orbit lengths," and "where does the Gamma factor
live" all get answers in one formalism (Gate 4 of `docs/09-new-ontologies.md` §5 passed by
construction, Gate 2's slot for positivity built in). What it has not achieved is the positivity
itself, which Section 3 showed is the entire remaining content of RH. Connes and Consani have
continued the program (the "scaling site"; work around 2020–2021 proving positivity in restricted
settings); as in `docs/09` §4.2, I have not verified the current scope of those results, and
neither author claims a proof. Finer details, which operator algebra, which measure, how the
semilocal formula is proven, are deliberately not stated here, because I cannot vouch for them
from memory; Connes' 1999 paper is the primary source.

> **Plain-words recap.** Quantum mechanics showed a system can *be* its algebra of observables;
> noncommutative geometry does geometry with such algebras, which keep working on glued-up
> quotients where ordinary geometry sees mush. Connes built such a space from all completions of
> the rationals, found a scaling flow on it, and proved, in a restricted setting, a trace formula
> with the primes on the geometric side: the explicit formula, with a space attached at last. RH
> becomes "a certain trace is non-negative." That positivity is open: a deep reformulation, not a
> proof.

---

## Where to go next

- **`docs/04-explicit-formula.md`**: Section 2's identity derived from residues; watch the orbits
  rise out of a bare sum over the modes with `zeta.explicit.prime_spectrum`.
- **`docs/06-hilbert-polya-and-gue.md`**, the operator side: Hilbert–Pólya, Berry–Keating's
  `H = xp` (whose flow is the classical shadow of the scaling flow above), Selberg in full, and the
  function-field world where trace formula *and* positivity both exist.
- **`docs/09-new-ontologies.md`** and **`docs/11-f1-and-the-missing-geometry.md`**, why "find the
  space" is the field's considered response to `docs/08-why-it-is-hard.md`, and the `F1`/Deninger
  routes that triangulate the same missing object. **`docs/07-equivalences-and-criteria.md`** §7
  places Weil positivity among the other RH-equivalences.
- **In code**: `zeta/weil.py`, build a pair with `gaussian_pair` / `fejer_pair`, check the formula
  with `explicit_formula_sides`, compute `W(h)` from primes alone with `weil_functional`, and run
  `near_tightness_report` to watch `γ₁` control the margin. `tests/test_weil.py` pins every number
  quoted in Sections 2–3.
- **Primary sources**: Weil's 1952 explicit-formulas paper and his 1972 refinement (commonly cited;
  verify exact references before formal use); Selberg's 1956 trace-formula paper (commonly cited
  from the Journal of the Indian Mathematical Society); Connes, *Selecta Mathematica* 1999.
