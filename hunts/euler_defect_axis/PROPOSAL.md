# Proposed repair, for the tree to accept or refuse

This hunt may not write `zeta/`, `tests/` or `docs/`. What follows is the
change it would make if it could, stated precisely enough to be argued with.

## 1. `hunts/zeta_temperament/probe_euler_discriminator.py`

Add the residual check to the probe itself and refuse a form it is not
entitled to, rather than returning a number for it:

```python
def spectrum(a, nmax=NMAX):
    if abs(a[1] - 1) > mp.mpf(10) ** -25:
        raise ValueError(
            "the recursion isolates c(n) a(1); a(1) = %s does not determine c"
            % mp.nstr(a[1], 6))
    ...
```

and report, per discriminant, `principal_form_defect` in place of
`max_form_defect`. The per-form loop then runs over the forms that represent
1, which is one form per discriminant.

A guard that cannot fire is worth nothing, so it ships with the planted fault
that fires it: the form `(2,1,2)` of discriminant `-15`.

## 2. `tests/test_zeta_temperament.py`

The line

```python
assert d15["max_form_defect"] > 30
```

pins `36.0644`, the value with residual `189.6888`. It has no replacement at
the same strength, because nothing in the corrected axis reaches 30. The
assertions that carry the section's claim need no change: class number one
below `1e-25`, loud above `1.0` (the corrected rows run 2.96 to 5.08), and
every class-group sum below `1e-25`.

The replacement worth having is not a looser threshold on the same quantity.
It is the check that would have caught this:

```python
def test_every_reported_defect_solves_the_identity_it_claims():
    """A composite defect is a statement about c; c is defined by
    a(n) log n = sum_{d|n} c(d) a(n/d). A row whose residual is nonzero is
    not a defect at all."""
```

## 3. `docs/34` section 6, table E7

The per-form column becomes the principal-form column, with a correction
notice in the section's own style recording what the earlier table reported
and why. The section's argument is unaffected: the discriminator separates
zeta from a rival sharing its functional equation, class number one supplies
an Euler product, the class-group sum restores one. Only the numbers attached
to non-principal forms go.

## 4. Issue #93

The open question stands, but its proposed design does not. The paragraph
"The Epstein family supplies a defect axis from 0 to 36 with class number as
the knob" wants replacing with the corrected axis and three narrower observations that
replace it: the band is `2.96 .. 5.08` at cutoff 61 and `5.02 .. 10.57` at
cutoff 401, so the axis has no scale; the ordering of the nine discriminants
holds in six of nine positions at every cutoff and is fixed from 201 upward, so
it does order them once there is enough of it; and the two candidate knobs
correlate with each other at `+0.97` over those nine points, so nine points
cannot say which one is doing the work.

## 5. Disposition of the compute job

The off-line-zero measurement issue #93 prices is not worth buying against
this axis, and normalising the defect comes before either. The band runs
`2.96 .. 5.08` at cutoff 61 and `5.02 .. 10.57` at cutoff 401 while the ordering
of the nine discriminants moves by a single adjacent transposition, so the
quantity orders subjects and does not scale them. Normalise it first, by the number of composites in range or
against the same norm of the prime-power part.

Then, if the question is worth pursuing, the family to build is a
Davenport-Heilbronn construction at several moduli, where the mixing constant
is a genuine knob and the functional equation is imposed by a linear solve, as
`zeta/epstein.py` already does at modulus 5. That is a construction, not a
borrowing, and it is the door section 7 of `RESULTS.md` names.

## Applied, 2026-10-10

*Added when the hunt was landed on main. The sections above are left as they
were written on 2026-09-10, when this was "the change it would make if it
could" and the hunt's issue #93 comment of that date called the repair
"deliberately not applied". Both were true then.*

The repair was applied by #296 (commit `da94b5a`) on 2026-10-10, before this
directory reached main. It changed `docs/34`,
`hunts/zeta_temperament/probe_euler_discriminator.py`,
`hunts/zeta_temperament/results_euler.json` and
`tests/test_zeta_temperament.py`. Sections 1 and 2 went in as written: the
same `a(1)` guard in `spectrum`, `principal_form_defect` in place of
`max_form_defect`, the per-form loop over the forms that represent 1, the
planted fault `(2,1,2)` of `d = -15`, the `> 30` line removed, and
`test_every_reported_defect_solves_the_identity_it_claims` added under that
name. Where it went beyond or against this page:

- **It followed `AUDIT.md` where section 3 and the audit conflict.** Section 3
  says the argument of `docs/34` section 6 is unaffected and only the
  non-principal numbers go. The audit's last correction says that is too
  broad, because the sentence "every individual form is loud" goes too. #296
  withdrew that sentence with a dated note, rewrote "the composite lines of the
  individual forms cancel" (only the principal form has composite lines of its
  own), and added the hedge to `F4` for zeros off the critical line that the
  audit asked for and `RESULTS.md` section 5 says was missing.
- **It kept the superseded numbers inline.** Table E7 prints each corrected
  row as, for example, `5.0847 (was 36.0644)`, beside a dated correction
  notice, rather than replacing the column and recording the old values only
  in the notice.
- **It added checks this page did not ask for**: the probe raises unless
  exactly one reduced form per discriminant represents 1, the planted fault is
  run on every probe run and recorded in `results_euler.json`, and the tests
  pin the corrected column, the six superseded numbers as composite defects of
  `1 + Z_Q(s)`, and the 14 / 27 split.
- **Section 4 was not carried out as an edit.** Issue #93's text was left as
  it is; `docs/34`'s Scope paragraph points at the issue comment of 2026-09-10
  instead.
- **Section 5 is untouched.** The defect is not normalised and the
  Davenport-Heilbronn family at several moduli has not been built.
