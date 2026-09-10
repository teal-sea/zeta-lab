# 38. One form per discriminant, and what an adversary did to the write-up

**Hunt #119, `hunts/euler_defect_axis/`.** The measurements and the doors are
in `hunts/euler_defect_axis/RESULTS.md`; the audit that rewrote it is in
`AUDIT.md`; the repair it proposes to files a hunt may not touch is in
`PROPOSAL.md`. This page is the front door.

Grade: **measured**. Nothing on this page bears on RH (`docs/08`), and no new
theorem is claimed: the mathematics used is classical, and what is new is a
measurement of which rows of a published table that mathematics entitles.

## 1. The discriminator, and its one hypothesis

`docs/34` section 6 records a genuinely good idea. For a Dirichlet series
`f = sum a(n) n^-s`, write `-f'/f = sum c(n) n^-s`. Then `f` has an Euler
product exactly when `c` is supported on prime powers, and Weil's explicit
formula makes `c(n)/sqrt(n)` the weight of frequency `log n` in the
distribution of `f`'s zeros. **So a nonzero `c` at a composite is a failure of
multiplicativity, read off the zeros.** For zeta the coefficients are von
Mangoldt's and the composite part vanishes; for the Davenport-Heilbronn
function, which shares zeta's functional equation and violates RH, it does not,
and its loudest single line is `n = 51 = 3 x 17`.

The idea needs one thing, and says so: `a(1) = 1`. The coefficients `c` are
recovered by a recursion that isolates the `d = n` term of

    a(n) log n = sum_{d | n} c(d) a(n/d)

as `c(n) a(1)`, and divides.

`docs/34` then reports the quantity for 41 reduced binary quadratic forms
across fourteen discriminants, with a headline of `36.0644` at `d = -15`, and
issue #93 reads the family as "a defect axis from 0 to 36 with class number as
the knob", proposes an experiment on top of it, and prices the compute.

## 2. A binary quadratic form represents 1 exactly when it is principal

That is classical, and it settles the table. The principal form of each
discriminant represents 1; the others do not. So `a(1) = 1` on fourteen rows and
`a(1) = 0` on twenty-seven, the `d = n` term vanishes on those twenty-seven, and
the recursion divides by zero in the only sense available to it: it never forms
the quotient at all, and returns a number anyway.

Measured, not read off the source: `a(1)` is exactly 1 on the fourteen
principal forms and exactly 0 on the other twenty-seven, and no rescaling
repairs any of them, because a rescaled series needs every represented value to
be a multiple of the least one and none of the twenty-seven has that property.
The form `(2,1,2)` of `d = -15`, whose row is the table's loudest, represents 2
and 3.

The qualitative reading of `docs/34` survives on the rows entitled to it: class
number one gives an Euler product and a defect at machine zero, class number
above one gives a *principal* form that is loud, and the class-group sum returns
to machine zero every time. What goes is the sentence "every individual form is
loud", the numerical axis, and the experiment issue #93 builds on it.

## 3. Then an adversary read the write-up

The first version of the hunt's result page was given to a separate agent with
no part in producing it, told to break the claim rather than review it. It ran
eight attacks. The claim survived all eight. The write-up did not.

**It found the counts wrong.** The page said 44 forms and 30 non-principal. The
class numbers sum to 41, of which 27 are non-principal. Two numbers, in the
verdict box, wrong.

**It found the load-bearing measurement was not one.** The page reported the
residual of the identity as an independent check that the recursion had no
right to run. Written out, `R = |1 - a(1)| * max_n |c(n)|` identically, because
the recursion's own sum omits exactly the term the residual is testing for.
Measured on all 41 forms: the difference between the two is `0.0` exactly on 40
rows. So the residual is a rescaling of a norm the recursion computed, it is
downstream of `a(1)`, and it adds nothing to knowing `a(1)`. The page had
presented an algebraic identity as two measurements agreeing.

**It found the strongest sentence was the emptiest.** "The largest published
defect is the largest residual" reads as a coincidence detected by a second
route. It is two norms of the same vector, correlated at 0.99 with a shared
argmax by construction.

**It found the withdrawn numbers were not empty.** The page said those rows
carry no information. They carry precise information about the wrong function.
Because the recursion never touches `a(1)` on its right-hand side, running it on
a series with `a(1) = 0` returns exactly the coefficients of the same series
with `a(1)` replaced by 1, which is `1 + Z_Q(s)`. The published number for each
non-principal form is that series' composite defect, exactly: measured on all 27
rows, worst disagreement `0.0`. A series with no functional equation and no
relation to the zeros of `Z_Q`.

**It found two explanations unsupported.** The page said the discriminant
explains the defect better than the class number does. On nine points the two
predictors correlate at `+0.97`, their rank correlations against the defect are
`-0.983` and `-0.979`, and a permutation test for the gap gives `p = 0.113`.
Nine points cannot separate them. The page also offered a sparsity mechanism;
against its own natural proxy that gives `R^2 = 0.22` and the coefficient
reverses sign once the discriminant is in the model.

**It found the axis has no scale.** The defect is an unnormalised sum over
composites below a cutoff, and the cutoff was frozen at 61. Move it to 401 and
the band runs `5.02` to `10.57` instead of `2.96` to `5.08`. The *ordering* of
the nine discriminants is identical at both cutoffs. So the family orders
subjects and does not scale them, which is a sharper statement than "the range
is 0 to 5" and a more useful one, since the page was using the range to cancel a
compute job.

Every correction is now in the result page, and the three carrying numbers were
recomputed here before being accepted rather than taken on the audit's word.

## 4. What is left standing

The claim: the composite-line discriminator is entitled to one form per
discriminant. Eight attacks, including an independent reimplementation of the
Kronecker symbol and a least-squares search for *any* integer-indexed `c` that
solves the identity for a non-principal form (residual 2.18 to 5.79, so none
exists). It did not move.

The disposition: the compute job issue #93 prices should not be bought against
this axis, and normalising the defect comes before either. A family with a real
knob is a Davenport-Heilbronn construction at several moduli, where the mixing
constant is the knob by construction, which `zeta/epstein.py` already does at
modulus 5.

The pinned number: `tests/test_zeta_temperament.py` asserts
`d15["max_form_defect"] > 30`, which pins `36.0644`, which belongs to
`1 + Z_Q(s)`. The test's structural assertions all still hold on the corrected
rows. That is one line, and changing it is the tree's decision, not the hunt's.

## 5. Why this page exists

Because the interesting part is not that a table had bad rows. It is that the
check which would have caught them is one line long, is implied by the method's
own stated hypothesis, and nobody ran it. And then, that a write-up of *that*
finding contained eleven overclaims of its own, including one that dressed an
identity up as a corroboration, until something with no stake in it went
looking.

Both halves are the same lesson and the second is the harder one to arrange.
