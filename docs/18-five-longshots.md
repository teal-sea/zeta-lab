# 18 — Five longshots, run to their walls

A session's worth of deliberately improbable attacks on RH, each pushed until
it either produced something measurable or hit a named obstruction. None of
them advance RH. Four of them fail in *interesting* ways, and one of them
turns out to be the sharpest gate in the repository.

The house rule that governs this whole document: a structural property that
"explains" RH must survive `zeta.epstein.battery` — the Davenport–Heilbronn
function satisfies a functional equation, has real coefficients and a real
Hardy-style Z, and **violates RH**. A property `f_DH` also has distinguishes
nothing (`docs/09` gate #3).

| # | probe | module | verdict |
| --- | --- | --- | --- |
| 1 | Wu–Sprung inverse potential | `zeta/inverse.py` | passes for DH too — distinguishes nothing |
| 2 | Lee–Yang / GHS inequality | `zeta/leeyang.py` | passes for DH too — distinguishes nothing |
| 3 | PSLQ ℚ-independence | `zeta/relations.py` | bounded exclusion; instrument nearly lied |
| 4 | zero measure as a quasicrystal | `zeta/quasicrystal.py` | **separates ζ from DH** — reads the Euler product |
| 5 | additive synthesis / mean power | `zeta/synthesis.py` | exact equivalence, known wall |

---

## 1. Hilbert–Pólya as an experiment

If the ordinates γₙ are a Schrödinger spectrum, semiclassical quantization
inverts the counting function into a potential (Wu & Sprung 1993). The Abel
integral equation

    x(V) = ∫_{E₀}^{V} N̄′(E)/√(V−E) dE

is solved with the smooth density N̄′(E) = (1/2π)log(E/2π), then corrected by
a mollified sum over actual ordinates, then handed to a finite-difference
eigensolver and refined by first-order inverse iteration.

Calibration first, per house rule: the same two directions are run on the
harmonic oscillator, where truth is exact. Abel inversion returns V = x² with
defect below 1e-10; the forward solve returns 1, 3, 5, … within 5e-4.

**Result.** The reconstruction hits the first 25 ordinates to an RMS of
1.2×10⁻⁴ mean gaps. The smooth well alone already gets to 0.22 gaps.

**Verdict.** Run the identical pipeline on the Davenport–Heilbronn *on-line*
ordinates and it hits them to 2.5×10⁻⁴ gaps. The Abel inversion consumes a
list of real numbers; it cannot see the off-line zeros at all. So "there
exists a Hamiltonian with this spectrum" is not a fact about ζ — it is a fact
about lists of real numbers. Hilbert–Pólya content, if any, must live in
*properties* of the operator (a natural derivation, arithmetic structure in
V, a trace formula), never in its existence.

A basin caveat worth keeping: the refinement is first-order perturbation
theory and needs the seed within about one mean gap. It is a manufacturing
procedure, which is exactly why its success proves nothing.

---

## 2. Newman's Lee–Yang program

Statistical mechanics has a theorem that puts zeros on a line, so the
temptation is old. Read Φ (the heat-kernel density of `zeta/heatflow.py`) as
a single-site spin measure; its free energy is f(h) = log ∫Φ(u)e^{hu}du.

That integral is not an analogy. Measured, not recalled:

    ∫ Φ(u) e^{hu} du = ¼ · ξ(½ + h/2)

with the ratio constant to machine zero across h. **The free energy of the Φ
spin model is log ξ on the real axis**, and "Φ belongs to the Lee–Yang class"
is precisely RH. That is a restatement; its value is that classical
sufficient conditions become measurable.

**GHS** (magnetization concave in the field) reads G‴(w) ≤ 0 for
G(w) = log ξ(½+w). Two independent routes agree to five digits: a stencil on
ξ itself, and the RH-assuming Hadamard form −4w Σ_γ (3γ²−w²)/(γ²+w²)³. GHS
holds at every probe point from w = 0.5 to 40. Φ is also positive, even and
log-concave throughout ((log Φ)″ from −74.9 at u = 0 to −9.1×10³ at u = 1.3).

**Verdict.** The completed Davenport–Heilbronn function is real and symmetric
about ½, so the same free energy exists — and its G‴ is negative at every
probe point too. GHS distinguishes nothing. Whatever makes ζ's zeros real,
ferromagnetic inequalities do not see it.

---

## 3. PSLQ and the pigeonhole floor

It is conjectured (and used, under the name LI, throughout prime-race theory)
that the positive ordinates are linearly independent over ℚ. Not one instance
is proven: nobody can rule out γ₂/γ₁ ∈ ℚ.

**Result.** No integer relation with max|aᵢ| ≤ 10⁶ among the first 30
ordinates, at 280 digits. Bounded exclusion, not a proof — and finite
exclusions do not make the conjecture likelier.

**The part worth keeping is the near-miss.** The first n = 20 run, at the
textbook precision n·log₁₀B + 20, *returned a relation*: coefficients around
7×10⁵, residual 4.4×10⁻¹⁰⁴, stable when the ordinates were recomputed at 300
digits. It was junk — the pigeonhole floor. Over a coefficient box of size B
with n values, accidental combinations reach roughly scale·B^{−(n−1)}, and
when PSLQ's tolerance is looser than that floor it terminates on an accident.
The module now carries a 40-digit guard, a residual gate, and a third status
`inconclusive_floor_noise` that is neither an exclusion nor a candidate. A
"discovery" that does not shrink under added precision is an artifact of the
search, and the safe failure mode has to be built in.

---

## 4. The zero measure is a Fourier quasicrystal — and this one bites

Guinand's summation formula says zeros and prime powers are a Fourier pair.
As a statement about *measures*: the counting measure of the ordinates has an
atomic Fourier transform, atoms at u = log n with weights ∝ Λ(n)/√n. That is
the defining shape of a Fourier quasicrystal.

With a Gaussian taper of width A, Z(u) = Σ_{γ>0} e^{−γ²/2A²} cos(γu):

* **The atom law is derived, then checked.** c = −A/(2√(2π)) comes from the
  explicit formula applied to h(r) = e^{−r²/2A²}cos(ru). Measured/predicted
  runs 0.94–0.98 across taper widths spanning 2.5×; atom heights track
  Λ(n)/√n with ~3% spread.
* **The Euler-product signature.** ζ's Euler product forces Λ to vanish off
  the prime powers, so the transform must be *silent* at log 6, log 10,
  log 12. With 1000 zeros: prime-power atoms have median |Z| = 60.1,
  composite locations 2.2, ambient background 0.90 — a **26.8× separation**.

**Verdict — the interesting one.** `f_DH` is a *sum* of two Dirichlet
L-functions, not an Euler product, so −f′/f has coefficients spread over all
integers: b₆ = +1.936, b₁₄ = −2.852, b₂₁ = +3.290, b₂₆ = +3.521, all sitting
where ζ is exactly silent. DH's zero measure is still crystalline; it
crystallises on a *different, non-multiplicative* atom set. **This is the
only probe in this document that the counterexample fails.**

Read it honestly. The gate detects the **Euler product**, not RH, and DH was
already known to lack one. What the measurement adds is that the atomic
structure of the zero measure is a strictly sharper invariant than the
functional equation — it separates ζ from the standard counterexample where
positivity-flavoured probes do not. That is a computational instance of the
strengthened gate in `docs/09` §5.1: *factorization*, not positivity, is what
carries the arithmetic. It is not evidence for RH; possessing an Euler
product is not known to imply RH — that implication is substantially the
content of GRH itself.

---

## 5. Additive synthesis: does the prime patch clip?

In log-time u = log x, the normalized prime signal

    S(u) = (ψ(e^u) − e^u) / e^{u/2}

is by the explicit formula a synthesizer patch: one partial per zero. On RH
every partial is a pure tone with a *constant* envelope; a zero at Re ρ = β >
½ is a partial swelling like e^{(β−½)u}. So:

**RH ⟺ the prime patch has finite average power.**

Under RH the power is a closed form, Σ_ρ 1/(ρ(1−ρ)) = 2 + γ_Euler − log 4π =
0.0461914179…, so the primes play at a constant RMS of 0.2149. Measured three
ways: closed form 0.04619142; zero side (1000 ordinates + density tail)
0.04619200; prime side (Λ-sieve to 10⁶, window u ≥ 6) 0.04693046, approaching
from above as the window start rises.

**The wall, named.** Proving finiteness from the prime side means expanding S²
into ΣΛ(n)Λ(m) correlations — the variance of primes in short intervals — and
by Goldston–Montgomery that control is *equivalent* to pair correlation of the
zeros. The audio framing reaches Montgomery's program in three steps and then
stops exactly where everything else stops. Agreement among the three routes
checks the implementations and nothing else (Littlewood; `docs/08`).

---

## Two instrument traps, found the hard way

Both are recorded because the next agent will otherwise re-find them.

**`mp.diff` silently returns zero on this repo's rounded functions.** Both
`zeta.epstein.dh_f` and `zeta.core.xi` round to a fixed working precision
internally, so across `mp.diff`'s automatic step they are bit-for-bit
constant and the derivative vanishes — no warning, no exception. In
`quasicrystal` this produced a flat "defect" of 1.4e-3 at every truncation
length; in `leeyang` it produced ~1e-47 where the true value is 1.65e-3. The
diagnostic is the same in both cases: **a defect that does not change when
you improve the approximation is measuring a broken reference, not a real
error.** Hand-rolled stencils with explicit calibrated steps are required.

**A cross-check is the only thing that catches a sign.** The 5-point stencil
for a third derivative was first written negated. Every value had the right
magnitude and the wrong sign, and GHS would have been reported as violated
everywhere. The independent Hadamard zero-sum caught it. This is the
argument for the repo's habit of computing both sides of everything
independently, in one concrete instance.

---

## 6. Follow-up: Gate 4 as a decision statistic

Probe #4 above measures a distinction that `docs/09` **already asserts** —
Gate 3 names DH's properties as "satisfy functional equations, have no Euler
product, and have zeros off the critical line", and Gate 4 demands the Euler
product be structural. So the quasicrystal separation is not a discovery; it
is an instrument for a claim the document already makes qualitatively. The
useful follow-up is therefore to make the gate *quantitative*, which
`zeta/factorization.py` does.

For f(s) = Σ aₙn^{−s} with a₁ = 1 and −f′/f = Σ bₙn^{−s}, define

    D(f) = Σ_{n composite, not a prime power} bₙ²/n  ÷  Σ_{n a prime power} bₙ²/n

**D = 0 if and only if f has an Euler product.** Both directions are exact:
a product makes log f a sum of local terms, so b is supported on prime
powers; conversely, b supported on prime powers makes log f split as
Σ_p (local series), and exponentiating rebuilds the product. So this is a
decision procedure, not a heuristic — and it is computed from coefficients
alone, with no zeros, no ξ-phases and no counting functions, which is
precisely §5.1's Requirement A on provenance.

| function | D | status |
| --- | --- | --- |
| ζ | 1.2e-32 | Euler product |
| L(χ) quadratic mod 3, 4, 5 | ~1e-32 | Euler product |
| DH real-part combination (c = ½) | 0.825 | none |
| Davenport–Heilbronn | 0.979 | none |

The Euler-product rows are the real test: a statistic that failed to zero
out on the quadratic characters would be measuring something other than
factorization.

**The null is the point.** A nonzero D means nothing until you know what a
generic non-factoring sequence scores. Against random real sequences with
DH's shape (period 5, a₁ = 1, a₅ = 0), the null median is 1.329 with a
5–95% band of 0.534–4.313, and **DH sits at the 27th percentile — squarely
typical**. Davenport–Heilbronn is not an exotic near-miss to factorization;
it is an unremarkable member of the class of things that do not factor. A
candidate ontology claiming to "almost" produce an Euler product would need
to score orders of magnitude below this null, not merely nonzero.

**A blindness this exposes, bounding §4 above.** The zeros of ζ(s−δ) are the
points δ+½+iγ — *the same ordinates*. Any statistic computed from ordinates
alone is therefore identical for ζ and for a shifted function whose zeros lie
nowhere near Re s = ½. Ordinate probes read arithmetic; they cannot read the
position of the critical line. That is why the coefficient-side statistic
carries the Gate 4 content and the zero-side transform, however pretty,
cannot.

Still not about RH: an Euler product is not known to imply RH, and that
implication is substantially GRH itself.

### 6.1 Does the functional equation know about factorization? No.

The statistic makes one more question answerable, and it is the sharpest one
available here. Davenport–Heilbronn's κ is not a free parameter — it is
*forced* by demanding F(s) = F(1−s), and `zeta.epstein.kappa` re-derives it
by linear solve on every call. D is a completely separate functional of the
same coefficients. If symmetry and factorization were secretly linked, κ
would sit somewhere distinguished on the D landscape.

Scan the family aₙ = [1, t, −t, −1, 0] that contains DH at t = κ
(`kappa_landscape`):

| quantity | value |
| --- | --- |
| D at κ = 0.284079 | 0.979 |
| dD/dt at κ | **+1.154** — not a critical point |
| family minimum | t = 0, D = 0.825 |
| any t with D = 0 | **none** |
| symmetry of D | exactly even in t |

κ sits on a plain upslope. No member of the family factors at all, and the
minimum is at t = 0 — the real-part combination, which is not DH and not an
Euler product either. The evenness is structural rather than lucky: t ↦ −t
conjugates the underlying character, and conjugation cannot change whether
something factors.

So the functional equation pins κ to twelve digits and says **nothing
whatever** about the Euler product. One can slide t anywhere along this
family — destroying the functional equation at every point except κ —
without ever gaining or losing factorization. The two constraints are
independent.

That is `docs/09` Gate 2 turned from an assertion into a measurement:
*symmetry alone is provably insufficient*. The document argues it from the
existence of DH; this measures the local independence of the two conditions
in a neighbourhood of DH itself, which is a strictly finer statement. It
also explains, in one number, why Gate 4 has to be posed separately from
Gates 2 and 3 rather than following from them.

---

## 7. The hole, closed: a statistic that reads zero *positions*

§6.1 left an explicit gap. Probes 1 and 2 failed because they consume only
ordinates, and §6 showed why that is fatal: ζ(s−δ) has the *same ordinates*
as ζ while its zeros sit on a different vertical line, so no ordinate
statistic can locate the critical line. The coefficient-side statistic of §6
reads arithmetic instead — but arithmetic is not position either. The open
question was whether anything computable reads **position**.

There is, and the repository already had half of it. In `zeta/weil.py`'s
convention the Weil explicit formula reads

    Σ_ρ h(γ_ρ) = arch(h) + pole(h) − 2 Σ_n bₙ n^{−1/2} g(log n),   γ_ρ = (ρ−½)/i

and that γ_ρ is the whole story: on the line it is real, and for ρ = β+iγ off
the line it is γ − i(β−½), **complex**. The right-hand side is assembled from
Dirichlet coefficients and the gamma factor alone, so it accounts for every
zero. Therefore

    residue(c) := [arithmetic side] − [sum over ON-LINE zeros only]

is exactly what the on-line zeros fail to explain — and neither ingredient
knows an off-line zero exists. `zeta/detector.py`.

| | measurement |
| --- | --- |
| ζ, max abs residue at c = 20, 45, 60, 100 | **1.6e-15** (float noise) |
| DH, max abs residue at c = 40, 60, 100 | 8.0e-15 (quiet) |
| DH, residue at c = γ₀ = 85.6993484853776 | **+4.096324360133627** |
| predicted contribution of the known quadruple | **+4.096324360133638** |
| agreement | 1.1e-14 |
| \|β−½\| recovered from the peak height | 0.30851718245662 |
| true \|β−½\| | 0.30851718245664 |

So the detector does not merely notice the RH violation — scanning c
localizes the offending ordinate, and the peak height inverts through
≈ 4·exp(a(β−½)²) to recover *how far off the line the zero sits*, to
fourteen digits. Off-line zeros found without ever solving for them.

The ζ row is the real test. Its vanishing is a three-way agreement between a
digamma integral, a prime sum and a zero list that share no code, so it
validates the archimedean convention, the sign of the prime term and the
Fourier pair simultaneously. During development a sign-flipped prime term
produced ζ residues of order 1 — a signal-shaped artifact that only the
calibration caught. Same lesson as §3 and the trap notes: the control is
what makes the measurement mean anything.

**Limits, stated plainly.** This is not a proof of RH for ζ over any range,
and it is not *certified* — float/mpmath without enclosures, so `rigor.py`
keeps that word. And the residue measures "zeros unaccounted for by the
supplied on-line list": a *missing* on-line zero is indistinguishable from
an off-line one, so the statistic is only meaningful paired with an
independent count (`online_list_is_complete`, checked against
`zeta.epstein.zeros_on_line`).

What it settles for this document is narrow but real. Of the probes tried
here, ordinate statistics see nothing, coefficient statistics see
factorization, and exactly one — the Weil residue — sees where the zeros
actually are. That is the sense in which Gate 2 wants a positivity slot
rather than a symmetry: positivity is a statement about ρ, and ρ is the only
thing that knows about RH.
