# LATTICE-EXTREMALITY-ROUTE

*A route to proving lattice extremality, worked out far enough to say exactly
what is proved, under which hypotheses, and what is missing. It is not a
completed proof, and section 6 is the honest part of this document.*

Companion to `lattice_extremality.py` (the computations) and
`K2-TWO-SPECIES.md` T1 (the obligation this would discharge). Written
2026-08-20, after the search in that module failed to find a counterexample.
A search that finds nothing bounds the search. This is the attempt to bound
the problem instead.

## 0. The statement

For a `P`-periodic centre configuration with offsets `a_1..a_m` and density
`rho = m/P`, the per-centre cost at `y = 1/2`, in the one-sided convention
`two_species.centre_gas_row` uses, is

    J(T) = (2/m) sum'_{p,q,n} f(a_p - a_q + nP),   f(s) = Dam(1,s) - Kpair(s),

the prime excluding only `(p = q, n = 0)`. The claim to prove:

> **Lattice extremality.** `J(T) <= -4 c2(0) + 2 kappa(0) = 0.11433003938654052...`
> for every configuration, with equality if and only if `T` is a translate of
> the `2*pi` lattice.

The right-hand side is `two_species.centre_gas_row_closed()`, landed in
084f326. What follows shows it is not merely the lattice's value but a
ceiling, subject to two hypotheses.

## 1. The identity

Everything rests on one exact rewriting. Poisson summation on the inner sum
gives, for any `h` for which it is valid,

    sum_{p,q} sum_n h(a_p - a_q + nP) = (1/P) sum_j hhat(2*pi*j/P) |A_j|^2,
    A_j = sum_p exp(2*pi*i*j*a_p/P),

so that

    J_h(T) = 2*rho*hhat(0) - 2*h(0)
             + (2/(mP)) sum_{j != 0} hhat(2*pi*j/P) |A_j|^2.       (*)

Two things make `(*)` worth having. The left side is an infinite sum over
space; the right side is a *finite* sum whenever `hhat` has compact support.
And `|A_j|^2 >= 0` always, so the sign of each term is decided entirely by
the sign of `hhat`.

`structure_factor_defect` measures `(*)` against direct summation rather than
trusting it. Residual below `4e-9` on five configurations, three of them not
lattices, at `h = -kappa`.

## 2. Three facts about `kappa_hat`

`mean_damage` records `-D(y,s) = int_{-1}^{1} c2(w) cosh(yw) cos(sw) dw`.
Summing at `y = 0` and `y = 1` gives `counting_lemma.kappa`, hence

    kappa_hat(xi) = 2*pi * c2(|xi|) * (1 + cosh|xi|)   on [-1,1], 0 outside.

**(a) Compact support**, on `[-1,1]`. This is what collapses `(*)` to finitely
many terms.

**(b) Non-negativity**, and this one is *proved* rather than measured.
`c2 = g star g` with `g(u) = cos(sqrt2 u)` on `|u| <= 1/2`. Since
`sqrt2/2 = 0.7071... < pi/2`, `g` is strictly positive on the whole of its
support, so `c2(w) = int g(u) g(u+w) du` is an integral of a product of
positive functions and is strictly positive wherever the two supports
overlap, that is on `(-1,1)`. `1 + cosh` is positive. So `kappa_hat > 0` on
`(-1,1)`.

**(c) Vanishing at the endpoints.** `c2(+-1) = 0`, because the supports of
`g(u)` and `g(u+1)` meet in a single point. This is the fact the whole
argument turns on, and it is also the fact `counting_lemma` already used to
get its Poisson limit.

## 3. The bound

Take `h = -kappa` in `(*)`. Every `j != 0` term is `(-kappa_hat) * |A_j|^2 <= 0`
by (b), so dropping them can only raise the value:

    J_kappa(T)  <=  2*rho*(-kappa_hat(0)) + 2*kappa(0)
                 =  -8*pi*rho*c2(0) + 2*kappa(0)  =:  LP(rho).

`LP` is strictly decreasing in `rho` because `c2(0) > 0`, and

    LP(1/(2*pi)) = -4*c2(0) + 2*kappa(0) = 0.11433003938654052...,

exactly the lattice value. The lattice attains it because at spacing `2*pi`
its only non-zero-frequency mass sits at `xi = +-1`, where `kappa_hat` vanishes
by (c). It is the one configuration that pays nothing.

Since `LP` decreases, `LP(rho) <= LP(1/(2*pi))` for every `rho >= 1/(2*pi)`.
The dense side is therefore closed by the bound alone.

## 4. Uniqueness, and why the threshold is sharp

Equality in section 3 forces `rho = 1/(2*pi)` (else `LP(rho) < LP(1/(2*pi))`
strictly) and `kappa_hat(2*pi*j/P) |A_j|^2 = 0` for every `j != 0`. At
`rho = 1/(2*pi)` we have `P = 2*pi*m`, so `kappa_hat(2*pi*j/P) > 0` exactly for
`0 < |j| < m`, and equality forces

    A_j = 0   for   j = 1, ..., m-1.

Write `z_p = exp(2*pi*i*a_p/P)`, so `A_j` is the power sum `p_j = sum_p z_p^j`.
Newton's identities turn `p_1 = ... = p_{m-1} = 0` into `e_1 = ... = e_{m-1} = 0`,
so the monic polynomial with roots `z_p` is `z^m - c`. Its roots are the `m`-th
roots of `c`, which are equally spaced on the circle. So `T` is a translate of
the `2*pi` lattice.

The threshold matches exactly: the band `[-1,1]` and the density `1/(2*pi)`
conspire so that the constrained modes are precisely `j = 1..m-1`, which is
precisely the Newton condition. One fewer and uniqueness would fail; one more
and the lattice would not attain the bound.

## 5. What this proves, and under what hypotheses

> **Under H1 alone.** Let `T` be a `P`-periodic configuration with
> `rho = m/P >= 1/(2*pi)`. Then `J(T) <= -4 c2(0) + 2 kappa(0)`, with equality
> if and only if `rho = 1/(2*pi)` and `T` is a translate of the `2*pi` lattice.

The first version of this section also assumed **H2**, that `K_1(d) <= 0` at
every non-zero difference, which is what makes `f = -kappa` where it matters.
Section 5a removes it. H2 is nonetheless true of the extremiser, and for a
reason worth recording: `clip_is_idle_on_lattice(5000)` is negative
throughout, and

    lim_n K_1(2*pi*n)*(2*pi*n)^2  =  2*cos^2(sqrt2/2)*(1 - cosh 1)
                                  =  -0.6277706...

`K_1` has a `1/x^2` asymptotic with two sources. The endpoints of `c2` at
`w = +-1` contribute `2*c2'(1-)*cosh(1)*cos(x)`, and the kink at `w = 0`
contributes `-2*c2'(0+)`, which does not oscillate. Both slopes equal
`-cos^2(sqrt2/2)`, so at `x = 2*pi*n`, where the cosine is `+1`, they combine
to the constant above. It is negative **precisely because `cosh 1 > 1`**, and
that single inequality is why the rectification never fires at a lattice
difference. Predicted `-0.6277706` against a measured `-0.6277713` at `n = 5000`.

## 5a. Gap B, closed: an explicit majorant

Gap B asked for `v >= K_1^+` vanishing on `2*pi*Z` minus the origin with
`vhat <= kappa_hat`. There is a fourth constraint the first draft of this
document missed. The bound from `g = -kappa + v` is
`LP(rho) + 2*rho*vhat(0) - 2*v(0)`, so tightness at `rho = 1/(2*pi)` needs

    int v = 2*pi*v(0).

That kills the obvious ansatz. `v = (1 - cos x)*psi(x)` has the right zeros
for free, but it also vanishes at the origin, forcing `int v = 0` against
`v >= K_1^+ >= 0`. What works instead is

    v(x) = c * s(x),    s(x) = (sin(x/2)/(x/2))^2,

because `s >= 0`, `s(2*pi*n) = 0` for `n != 0`, `shat(xi) = 2*pi*(1-|xi|)^+`
is supported exactly on `[-1,1]`, and `int s = 2*pi = 2*pi*s(0)`, so the
tightness condition holds for every multiple at once.

Feasibility is then two one-dimensional inequalities:

    c  >=  sup_x K_1(x)^+ / s(x)          =  K_1(0)  =  0.9115647...
    c  <=  inf_{|xi|<1} khat(xi)/shat(xi) =  cos^2(sqrt2/2)*(1 + cosh 1)
                                          =  1.4698290...

**Both hold at once, so the problem is feasible with margin `0.558`.** The
supremum is attained at `x = 0`; the tail of `K_1^+/s` settles at `0.734916`
by `x = 3000`, comfortably under. The infimum is the limit at `xi -> 1`, and
it is in closed form because `c2` vanishes linearly there with slope
`-cos^2(sqrt2/2)`.

Take `c = K_1(0)`. Then `g = -kappa + c*s` satisfies `g >= f` everywhere,
`ghat = -kappa_hat + c*shat <= 0` everywhere, and `g = f` at every lattice
difference. The bound becomes

    LP_v(rho) = LP(rho) + 2c(2*pi*rho - 1),

equal to the lattice value at `rho = 1/(2*pi)` for any admissible `c`, and
still strictly decreasing in `rho` because that needs only `c < 2*c2(0) =
1.6985...`, which the whole admissible interval satisfies. Uniqueness survives
too: `ghat < 0` strictly on `(0,1)` since `c` is strictly below the infimum, so
the Newton argument of section 4 runs unchanged.

Measured end to end: 300 random configurations at `rho >= 1/(2*pi)`, zero
violations of `J <= LP_v(rho)`.

## 6. What is missing

Four gaps as first written. Gap B is now closed; A remains the real one,
and C and D are routine but unwritten. None should be described as detail.

**Gap A, the sparse side.** For `rho < 1/(2*pi)`, `LP(rho) > LP(1/(2*pi))` and
the bound says nothing. It is not close: at `rho*2*pi = 0.4` the bound is
`+2.15` against a true value of `-0.043`, a margin of `2.2`. So sparse
configurations are far from threatening and completely unprotected by this
argument. Closing this needs either a second argument for low density or a
different auxiliary function. **This is where the work is.**

**Gap B, the rectification. CLOSED, see section 5a.** The concrete
majorant `v = K_1(0)*(sin(x/2)/(x/2))^2` satisfies every constraint with
margin `0.558`, so hypothesis H2 is gone and section 5 holds for every
configuration at `rho >= 1/(2*pi)`.

What is *not* closed about it: the two inequalities in 5a are verified
numerically on a finite range with a settled tail, not enclosed. `rigor.py`
is the natural next step and would turn this into an enclosure-carrying
statement. Both are one-dimensional and should be well within reach.

**Gap C, periodic to general.** `(*)` is stated for periodic configurations.
General locally finite sets need the autocorrelation-measure form. Standard,
and still a step.

**Gap D, Poisson.** `(*)` needs justification for the `h` used. With `kappa`
continuous and `L^1`, `kappa_hat` continuous and compactly supported, the sum
on the right is finite and the formula is a sampling theorem. Routine, and
not written out here.

## 7. Grade and scope

The numerics are **measured**: double precision, no enclosure anywhere. The
argument in sections 1 to 4 is a proof sketch and is not formalised; section 5
is what it yields, and section 6 is what it does not. Lattice extremality is
not established, T1 is not discharged, and `k >= 3` is untouched. Nothing here
is evidence about RH.
