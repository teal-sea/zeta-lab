# Results: one form per discriminant, not forty-four

**2026-09-09. Grade: measured, with the load-bearing step an exact residual
that is zero or is not.** Nothing here is evidence about RH (`docs/08`), and
nothing here is a new mathematical theorem: the facts used are classical, and
what the hunt adds is a measurement of which rows of a published table those
facts entitle.

## 1. The verdict

    forms in the published table                    44
    forms whose a(1) equals 1                        1 per discriminant, 14 total
    forms whose a(1) equals 0                       30
    non-principal forms repairable by rescaling      0 of 27 checked
    published axis                                   0 .. 36.0644
    axis over the entitled rows                      0, then 2.9608 .. 5.0847

The composite-defect discriminator is defined for a Dirichlet series with
`a(1) = 1`. A binary quadratic form represents 1 exactly when it is the
principal form of its class group, so the recursion is entitled to run on one
form per discriminant and on the class-group sum, and on nothing else.

The qualitative reading of `docs/34` section 6 survives intact on the rows
that are entitled to it: class number one gives an Euler product and a
composite defect at machine zero, class number above one gives a principal
form that is loud, and the class-group sum returns to machine zero every
time. What does not survive is the numerical axis, and with it the
experimental design issue #93 proposes on top of it.

## 2. The measurement

For each form, the recursion of `hunts/zeta_temperament/probe_euler_discriminator.py`
was run unchanged, and the residual of the identity it solves,

    R = max_{2 <= n < 61} | a(n) log n - sum_{d | n} c(d) a(n/d) |,

was computed by a separately written function that sums over all divisors
including `d = n`, so it does not share the recursion's isolation step.

| d | h | a(1), principal | R, principal | a(1), others | worst R, others |
|---:|---:|---:|---:|---:|---:|
| -3 | 1 | 1 | 7.9e-31 | -- | -- |
| -4 | 1 | 1 | 3.2e-30 | -- | -- |
| -7 | 1 | 1 | 3.2e-30 | -- | -- |
| -8 | 1 | 1 | 1.6e-30 | -- | -- |
| -11 | 1 | 1 | 3.2e-30 | -- | -- |
| -15 | 2 | 1 | 1.6e-30 | 0 | **189.6888** |
| -20 | 2 | 1 | 1.6e-30 | 0 | 71.8017 |
| -23 | 3 | 1 | 0 | 0 | 3.9890 |
| -24 | 2 | 1 | 1.6e-30 | 0 | 49.1321 |
| -31 | 3 | 1 | 0 | 0 | 4.0775 |
| -39 | 4 | 1 | 0 | 0 | 24.5661 |
| -47 | 5 | 1 | 0 | 0 | 12.0761 |
| -71 | 7 | 1 | 0 | 0 | 11.9670 |
| -95 | 8 | 1 | 0 | 0 | 15.4848 |

Raw values for every form, including the rows this table summarises, are in
`artifacts/axis.json`. The residual is zero to machine precision on exactly
the fourteen principal forms and on the fourteen class-group sums, and is
bounded away from zero on all thirty of the others.

**The largest published defect is the largest residual.** `d = -15`, the form
`(2,1,2)`, is reported at `36.0644` and carries residual `189.7`. The number
the table calls loudest is the number produced furthest outside the
recursion's hypothesis.

## 3. Why no rescaling repairs it

A form with `a(1) = 0` might be brought into range by dividing through by its
least represented value `m`, if every value it represents were a multiple of
`m`. Enumerated over `n < 61` for all 27 non-principal forms of the nine
discriminants with `h > 1`: **none of them has that property.** `(2,1,2)` of
`d = -15` represents 2 and 3; `(2,-1,3)` of `d = -23` represents 2 and 3. The
represented set is not contained in `m` times the integers, so `n -> n/m`
does not carry the series into a Dirichlet series over the integers, and the
composite-line reading, which is a statement about integer divisors, has no
object to attach to.

## 4. The control that says the fault is not in this hunt

For class number one, `zeta_Q = w * zeta * L(chi_d)` exactly, which forces

    c(n) = Lambda(n) (1 + chi_d(n)).

That prediction uses no recursion. Computed with the Kronecker symbol from
its definition and von Mangoldt from trial division, it agrees with the
recursion's `c` on all five class-number-one discriminants to at worst
`2.8e-30` over `n < 61`. So the recursion, run on inputs it is entitled to,
reproduces an independently derived answer, and the disagreement in section 2
is a property of the inputs rather than of the instrument.

## 5. The corrected axis, and what it costs issue #93

Over the rows the recursion is entitled to:

| d | h | principal-form defect |
|---:|---:|---:|
| -15 | 2 | 5.0847 |
| -20 | 2 | 3.8823 |
| -24 | 2 | 3.8530 |
| -23 | 3 | 3.5569 |
| -31 | 3 | 3.3991 |
| -39 | 4 | 3.3959 |
| -47 | 5 | 3.3630 |
| -71 | 7 | 3.2614 |
| -95 | 8 | 2.9608 |

Issue #93 proposes the family as "a defect axis from 0 to 36 with class
number as the knob". Both halves fail on the corrected rows.

- **The range is 0 or roughly 3 to 5**, not 0 to 36. Five discriminants sit at
  machine zero and nine sit inside a band of width 2.12.
- **Class number is not the knob, and what correlation there is runs
  backwards.** Over the nine loud rows, `corr(defect, h) = -0.69` and
  `corr(defect, log|d|) = -0.82`. Larger class number goes with a *smaller*
  defect, and the discriminant explains it better than the class number does.
  The mechanism is not mysterious: the principal form `(1, b, c)` of a large
  discriminant has `c` near `|d|/4`, so it represents fewer of the integers
  below 61 and its coefficient sequence is sparser.

The experiment the issue prices, off-line zeros for every discriminant
against the defect, would therefore have been run against a two-point
effective axis (zero, or about four) with the spread inside it explained by
sparsity. That is worth knowing before buying the compute rather than after.

## 6. What is pinned, and what a repair would move

`tests/test_zeta_temperament.py` contains

    assert d15["max_form_defect"] > 30

which pins the largest of the thirty ineligible rows. The same test's
structural assertions, class number one below `1e-25`, class number above one
above `1.0`, and every class-group sum below `1e-25`, all still hold on the
entitled rows: the loud principal forms run 2.96 to 5.08, comfortably above
1. So the guard that would have to change is the one naming `30`, and the
guards carrying the section's actual claim are unaffected.

This hunt does not make that change. `tests/`, `zeta/` and `docs/` are outside
what a hunt may write, and the disposition is a decision for the tree, not for
the hunt that found it. The proposed repair is recorded in `PROPOSAL.md`.

## 7. The doors

1. **Active constraint.** The normalisation `a(1) = 1`. Everything the
   discriminator says is downstream of it, and it binds on 30 of 44 rows. The
   shadow price is total: those rows carry no information at all, rather than
   biased information.
2. **Frozen-constant inventory.**
   - `NMAX = 61`, the truncation of the coefficient sequence. Relaxing it
     costs `O(NMAX log NMAX)` and would change every defect value, since the
     defect is an unnormalised `L2` norm over composites below the cutoff. The
     trade with shape: the defect is not scale-free, so comparing two
     subjects at one cutoff compares their coefficient sizes as much as their
     multiplicativity. A cutoff-normalised defect is the door.
   - The unit count `w = w(d)`, which sets `a(1) = 1` for the principal form.
     It is not free: any other choice breaks the normalisation the recursion
     needs.
   - The choice of the principal form as the family's representative. The
     alternative that stays inside the hypothesis is the class-group
     characters: `L(s, chi) = sum_Q chi(Q) zeta_Q(s)` has `a(1) = 1` for every
     `chi` and an Euler product for every `chi`, so it gives defect zero
     everywhere and no axis at all. That is the reason the family has no knob.
3. **Information class.** A defect axis with a real knob needs a family whose
   members all satisfy `a(1) = 1`, share a functional equation, and vary
   continuously in multiplicativity. The Epstein family supplies the first and
   second on one form per discriminant and does not supply the third. The
   route that does is a Davenport-Heilbronn-type construction at several
   moduli, where the mixing of two characters is the knob by construction and
   the functional equation is imposed by solving for the mixing constant, as
   `zeta/epstein.py` already does for modulus 5. That reads no new
   information; it builds a family instead of borrowing one.
