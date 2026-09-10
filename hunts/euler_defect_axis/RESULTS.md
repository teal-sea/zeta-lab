# Results: one form per discriminant, not forty-one

**2026-09-10. Grade: measured. The load-bearing quantity is `a(1)`, an exact
integer count of representations of 1, and everything else here is downstream
of it.** Nothing bears on RH (`docs/08`) and nothing here is a new theorem:
the facts used are classical, and what the hunt adds is a measurement of which
rows of a published table those facts entitle.

**This page was rewritten after an independent adversarial audit.** The audit
is in `AUDIT.md` with its attacks and its verdict, *survives with corrections*.
It found the claim standing after eight attacks and the write-up wrong in
eleven places, including two counts and one sentence that presented an
algebraic identity as a coincidence. Every correction is applied below and the
three carrying numbers were recomputed here before being accepted.

## 1. The verdict

    forms in the published table                    41
    forms whose a(1) equals 1 (the principal ones)  14, one per discriminant
    forms whose a(1) equals 0                       27
    non-principal forms repairable by rescaling      0 of 27
    published axis                                   0 .. 36.0644
    axis over the entitled rows, cutoff n < 61       0, then 2.9608 .. 5.0847
    the same axis at cutoff n < 401                  0, then 5.0196 .. 10.5748

The composite-defect discriminator is defined for a Dirichlet series with
`a(1) = 1`. A binary quadratic form represents 1 exactly when it is the
principal form of its class group, so the recursion is entitled to run on one
form per discriminant and on the class-group sum, and on nothing else.

The qualitative reading of `docs/34` section 6 survives on the rows entitled to
it: class number one gives an Euler product and a composite defect at machine
zero, class number above one gives a *principal* form that is loud, and the
class-group sum returns to machine zero every time. What does not survive is
the sentence "every individual form is loud", the numerical axis, and the
experimental design issue #93 builds on top of that axis.

## 2. What `a(1) = 0` does to the recursion

The recursion solves

    a(n) log n = sum_{d | n} c(d) a(n/d)

by isolating the `d = n` term as `c(n) a(1)`. With `a(1) = 0` that term
vanishes and `c(n)` is not determined.

The residual of the identity at the returned `c` is **not** an independent
check on this, and the first version of this page said it was. Written out,

    R = max_{2 <= n < 61} | a(n) log n - sum_{d | n} c(d) a(n/d) |
      = |1 - a(1)| * max_{2 <= n < 61} |c(n)|,

identically, because the recursion's own sum omits exactly the `d = n` term.
Measured on all 41 forms, the difference between `R` and that product is `0.0`
exactly on 40 rows and `1.6e-30` on the remaining one. So `R` is a rescaling of
`max |c|` by `|1 - a(1)|` and it adds nothing to knowing `a(1)`.

`a(1)` is the whole of it, it is an integer, and it is `1` on exactly the
fourteen principal forms:

| d | h | forms with a(1) = 1 | forms with a(1) = 0 |
|---:|---:|---:|---:|
| -3, -4, -7, -8, -11 | 1 | 1 each | 0 |
| -15, -20, -24 | 2 | 1 each | 1 each |
| -23, -31 | 3 | 1 each | 2 each |
| -39 | 4 | 1 | 3 |
| -47 | 5 | 1 | 4 |
| -71 | 7 | 1 | 6 |
| -95 | 8 | 1 | 7 |

For the record, and because the first version leaned on it: the largest
published defect (`36.0644`, `d = -15`, form `(2,1,2)`) is also the largest `R`
(`189.6888`). That is not two measurements agreeing. They are two norms of the
same coefficient vector, correlated at `0.99` across the 27 rows with a shared
argmax by construction, and the sentence claiming otherwise is withdrawn.

## 3. What the published numbers actually are

They are not noise, and calling those rows empty was wrong.

Because the recursion never uses `a(1)` on its right-hand side (every divisor
`d < n` gives `n/d >= 2`), running it on `a` with `a(1) = 0` returns exactly the
coefficients of the series with `a(1)` replaced by `1`. That series is

    ftilde(s) = 1 + Z_Q(s),

and the published number for each non-principal form is precisely its composite
defect. Measured on all 27 rows against a Dirichlet-logarithm route: **worst
absolute disagreement `0.0`.**

So the correct statement is not that the rows carry no information. It is that
they describe `1 + Z_Q(s)`, a series with no functional equation, no Euler
product on either reading, and no connection to the zeros of `Z_Q`, rather than
the Epstein zeta function the table names.

**No rescaling reaches `Z_Q` itself.** Dividing through by the least represented
value `m` would restore `a(1) = 1` only if every represented value were a
multiple of `m`. Enumerated over `n < 61` for all 27 non-principal forms: none
is. `(2,1,2)` of `d = -15` represents 2 and 3; `(2,-1,3)` of `d = -23`
represents 2 and 3. The audit went further and asked whether *any*
integer-indexed `c` solves the identity for a non-principal form: least squares
over all `c(1..60)` with `c(1)` free leaves a residual of 2.18 to 5.79, so the
system is inconsistent and no such `c` exists.

## 4. The control that says the fault is not in the instrument

For class number one, `zeta_Q = w * zeta * L(chi_d)` exactly, which forces

    c(n) = Lambda(n) (1 + chi_d(n)).

That prediction uses no recursion. Computed with the Kronecker symbol from its
definition and von Mangoldt from trial division, it agrees with the recursion's
`c` on all five class-number-one discriminants to at worst `2.8e-30`. The audit
attacked the Kronecker implementation directly, against an independent one, and
did not break it.

## 5. The corrected axis, and what it costs issue #93

| d | h | defect, n < 61 | defect, n < 401 |
|---:|---:|---:|---:|
| -15 | 2 | 5.0847 | 10.5748 |
| -20 | 2 | 3.8823 | 8.6847 |
| -23 | 3 | 3.5569 | 7.8781 |
| -24 | 2 | 3.8530 | 6.9748 |
| -31 | 3 | 3.3991 | 6.8130 |
| -39 | 4 | 3.3959 | 6.4807 |
| -47 | 5 | 3.3630 | 6.1235 |
| -71 | 7 | 3.2614 | 5.4149 |
| -95 | 8 | 2.9608 | 5.0196 |

Issue #93 proposes the family as "a defect axis from 0 to 36 with class number
as the knob". Three things go wrong with that, and they are not the same thing.

**The range is not 0 to 36, and it is not any particular range.** The defect is
an unnormalised `L2` norm over composites below a cutoff, so it grows with the
cutoff: the band is `2.96 .. 5.08` at `n < 61`, `3.78 .. 6.17` at 121,
`4.18 .. 7.15` at 201 and `5.02 .. 10.57` at 401. Its width relative to its
mean moves too, `0.58, 0.52, 0.54, 0.78`. **The axis has no scale**, which is a
worse problem than having the wrong endpoints, and it is the first thing to fix
if the family is to be used as an axis at all.

**The ordering is nearly stable, and the "nearly" is the part worth stating.**
The first version of this section said the nine discriminants "rank in exactly
the same order at `n < 61` and at `n < 401`". They do not, and that sentence was
false when it was written. Six of the nine positions hold at every cutoff:
`-15` at the top, and `-31, -39, -47, -71, -95` in that order at the bottom. All
of the movement is inside the `-20, -23, -24` block, where `-23` climbs as the
cutoff grows. Against `n < 61` the rank correlation is `0.9500` at 121 and
`0.9833` at 201 and at 401, and the ordering then settles: `n < 201` and
`n < 401` agree exactly, `rho = 1.0000`. So the quantity does order these
subjects, and it needs a couple of hundred composites before it does.
`ordering.py` recomputes all of it from `artifacts/cutoff.json`, which is the
same artifact the false sentence was read off.

**Class number is not separable from the discriminant on nine points.** Over
the nine loud rows `corr(defect, h) = -0.69` and `corr(defect, log|d|) = -0.82`,
both negative, so the direction is opposite to the one the issue's framing
implies. But `corr(h, log|d|) = +0.97` on these nine points, tie-corrected
Spearman puts the two at `-0.979` and `-0.983` against the defect, and the
audit's permutation test for the gap between them gives `p = 0.113`. **So the
claim that the discriminant explains it better than the class number does is
withdrawn**: nine points cannot separate two predictors that correlate at 0.97.
What is supported is the sign and the ordering, not the attribution.

**The sparsity explanation is withdrawn too.** The first version said the
principal form of a large discriminant represents fewer integers below the
cutoff and so has a sparser coefficient sequence. Tested against that proxy:
`corr(defect, count of represented n < 61) = +0.47`, `R^2 = 0.22`, `t = 1.39`,
and the coefficient reverses sign once `log|d|` enters the model. The mechanism
may be true; this data does not show it.

**Disposition.** The compute job issue #93 prices, off-line zeros for every
discriminant against the defect, would be run against an axis whose scale is set
by an arbitrary cutoff and whose two candidate knobs cannot be told apart on
nine points. That is worth knowing before buying the compute rather than after.
Normalising the defect and building a family with a real knob comes first; the
door in section 7 says how.

One caveat this hunt inherits and did not state. `docs/34`'s gloss on `F4`, that
`c(n)/sqrt(n)` is the weight of frequency `log n` in the zero distribution,
reads the explicit formula on the critical line. The rows this hunt keeps are
exactly the `h > 1` principal forms, whose Epstein zeta functions classically
have zeros off it. The gloss therefore needs its own statement for these
subjects, and neither `docs/34` nor this page supplies one.

## 6. What is pinned, and what a repair would move

`tests/test_zeta_temperament.py` contains

    assert d15["max_form_defect"] > 30

which pins `36.0644`, a number belonging to `1 + Z_Q(s)` for the form `(2,1,2)`.
The same test's structural assertions all still hold on the entitled rows: class
number one below `1e-25`, loud above `1.0` (corrected rows run 2.96 to 5.08),
and every class-group sum below `1e-25`. So the guard that would change is the
one naming `30`, and the guards carrying the section's actual claim are
unaffected.

This hunt does not make that change. `tests/`, `zeta/` and `docs/` are outside
what a hunt may write. The proposed repair is in `PROPOSAL.md`.

## 7. The doors

1. **Active constraint.** The normalisation `a(1) = 1`. It binds on 27 of 41
   rows, and its shadow price is not that those rows are empty but that they
   describe a different function: `1 + Z_Q` instead of `Z_Q`. The distinction
   matters because the first is checkable and wrong, which is a cheaper defect
   to find than noise.
2. **Frozen-constant inventory.**
   - **The cutoff `NMAX = 61`.** The one frozen constant with real trade shape,
     and the measurement above prices it: the band roughly doubles from cutoff
     61 to 401 while the ordering moves by one adjacent transposition and is
     fixed from cutoff 201 upward. Anything using this quantity as
     an axis needs it normalised, by the number of composites in range or by the
     same norm of the prime-power part, so that two subjects can be compared
     without agreeing on a cutoff first. That is one line of code and it is the
     highest-value change available here.
   - **The unit count `w(d)`**, which is what makes `a(1) = 1` for the principal
     form. Not free: any other choice breaks the normalisation.
   - **The principal form as the family's representative.** The alternative
     inside the hypothesis is the class-group characters:
     `L(s, chi) = sum_Q chi(Q) zeta_Q(s)` has `a(1) = 1` for every `chi` and an
     Euler product for every `chi`, so it gives defect zero everywhere and no
     axis at all. That is *why* the family has no knob, and the audit checked
     it rather than taking it on the hunt's word.
3. **Information class.** A defect axis with a real knob needs a family whose
   members all satisfy `a(1) = 1`, share a functional equation, and vary
   continuously in multiplicativity. The Epstein family supplies the first two
   on one form per discriminant and does not supply the third. The route that
   does is a Davenport-Heilbronn-type construction at several moduli, where the
   mixing of two characters is the knob by construction and the functional
   equation is imposed by solving for the mixing constant, exactly as
   `zeta/epstein.py` already does at modulus 5. That reads no new information;
   it builds a family instead of borrowing one.
