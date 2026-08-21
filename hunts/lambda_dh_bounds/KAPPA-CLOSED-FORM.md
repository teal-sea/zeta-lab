# KAPPA-CLOSED-FORM: kappa = sqrt(1 + phi^2) - phi, decided on both backends

Written 2026-08-16. Vocabulary per `MISSION.md`: *measured* is one float
route, *decided* is an enclosure with exact endpoints settling a sign or a
containment, *cited* is somebody else's theorem. `kappa` is a coefficient of
the Dirichlet series, not a Lambda, so it is frame-free: nothing in this page
needs the narrow/wide tag of `FRAME.md`.

## 1. The identity and its owner

    kappa = -phi + sqrt(1 + phi^2),    phi = (1 + sqrt 5)/2  (the golden ratio)
          = 0.2840790438404122960282918323931261690911...

**The identity is Bombieri and Ghosh's** (*Around the Davenport-Heilbronn
function*, Russian Math. Surveys 66:2 (2011), 221-270, section 6), where the
constant is named `tau_+`. **The constant itself is Titchmarsh's** (Theory of
the Riemann Zeta-Function, Chap. X, 10.25, as Bombieri-Ghosh cite it), in the
radical form `(sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1)`. Nothing about the
closed form is original to this laboratory. The lab's contribution is three
small things: the enclosure-grade check connecting the hunt's own linear-solve
`kappa` to the closed form on both ball backends (section 4), the reduction of
the self-duality condition to the explicit real quadratic (section 3), and the
observation that this is the same conductor-5 golden arithmetic the lab
already carries in `hunts/golden_control` (section 5).

Equivalent forms, all decided equal at 500 bits on the flint leg (section 4):

    kappa = -phi + sqrt(1 + phi^2)                    (Bombieri-Ghosh, section 6)
          = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1)    (Titchmarsh, via B-G 5.1)
          = 5^{1/4} sqrt(phi) - phi                   (since 1 + phi^2 = phi + 2 = phi sqrt 5)
          = 2 sin(pi/5) / (sqrt 5 + 2 sin(2 pi/5))    (the trig form of the solve, section 3)

and `kappa` is a root of

    kappa^2 + 2 phi kappa - 1 = 0        over Q(sqrt 5),
    kappa^4 + 2 kappa^3 - 6 kappa^2 - 2 kappa + 1 = 0    over Q.

## 2. Bombieri-Ghosh's tau_+: definition and the equation it solves

Pinned from the hunt's reading record `BOMBIERI-GHOSH.md` (2026-08-16
retrieval, mathnet.ru `rm9410`, full English translation; the quotes below are
that record's verbatim transcriptions of the paper).

**Definition** (their section 5.1). They define the two-parameter series
`f(s, xi) = sum_{n>=1} a(n, xi)/n^s` with the period-5 pattern
`(1, xi, -xi, -1, 0)`, then:

> These series were introduced by Titchmarsh ([10], Chap. X, 10.25), who noted
> that for `xi = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1)` the function
> `f(s; xi)` satisfies the functional equation
> `(pi/5)^{-s/2} Gamma((1+s)/2) f(s; xi) = (pi/5)^{-(1-s)/2} Gamma((1+(1-s))/2) f(1-s; xi)`,
> which is analogous to the functional equation of Dirichlet series for an odd
> character mod 5, except for the fact that now the root number is 1. ...
> In what follows we will write `tau_+` for the above value of `xi`.

So **the equation `tau_+` solves is the self-duality functional equation of
`f(s, xi)` with root number 1**, displayed in their section 5.1. Their gamma
prefactor is `(pi/5)^{-s/2}` where the hunt's completed `F` uses
`(pi/5)^{-(s+1)/2}`; the two prefactors differ by `(pi/5)^{-1/2}` on both
sides at once, the ratio of left to right prefactor is `(pi/5)^{(1-2s)/2}` in
either convention, so the condition imposed on `xi` is identical.

**The closed form** appears in their section 6 (p. 246):

> For the Titchmarsh value `tau_+ = -phi + sqrt(1 + phi^2)` we find ...
> `sigma(tau_+, 1) = 1.120362`.

They also name the second root, `tau_- = -phi - sqrt(1 + phi^2)
= -3.520147021340...`, "the second Davenport-Heilbronn function", the one with
`sigma(tau_-, 1) = 2.3822861089...`. Both roots of the quadratic in section 3
are therefore theirs, with names.

One consequence of the quadratic worth pinning because their Theorem 7 uses
it: the constant term is `-1`, so the two roots satisfy `tau_- = -1/tau_+`,
hence `|arctan(tau_-)| = pi/2 - arctan(tau_+)`. Their Theorem 7 prime-sum
targets `pi/2 - |theta|` (with `xi = tan theta`) for the two functions,
`1.2940091` and `0.2767872`, are complementary in exactly this way:
`arctan(kappa) = 0.2767871794...` and `pi/2 - arctan(kappa) = 1.2940091473...`
(measured, mpmath dps 30). The complementarity is the quadratic's constant
term made visible.

## 3. The algebra: from the self-duality condition to the quadratic

The starting point is the condition `winding.py` derives (its docstring,
"Why G is even", step (i)): with `chi` the odd quartic character mod 5,
`chi(2) = i`, values `(1, i, -i, -1, 0)` on residues `1, 2, 3, 4, 0`, the real
period-5 pattern `a = (1, kappa, -kappa, -1, 0)` is
`a_n = alpha chi(n) + conj(alpha) conj(chi)(n)`, and matching the two theta
terms in Hecke's transformation makes `omega(1/x) = x^{3/2} omega(x)` hold if
and only if

    alpha = conj(alpha) * (-i tau(conj chi) 5^{-1/2}).            (S)

This is the same condition `instrument.kappa_ball` solves as a linear solve
`A + i kappa B = 0` on the completed L-functions at the single point
`s0 = 3/4 + 3i/2`; (S) is that condition at the theta level, which is where it
reduces to a quadratic in closed form.

**Step 1: alpha in terms of kappa.** Matching coefficients at `n = 1` and
`n = 2`: `alpha + conj(alpha) = 1` and `i(alpha - conj(alpha)) = kappa`, so

    alpha = (1 - i kappa)/2.

**Step 2: the Gauss sums, computed rather than remembered.** With
`e(x) = exp(2 pi i x)` and `sin(4 pi/5) = sin(pi/5)`:

    tau(chi)      = e(1/5) + i e(2/5) - i e(3/5) - e(4/5)
                  = 2 i sin(2 pi/5) - 2 sin(pi/5)
                  = -2 sin(pi/5) + 2 i sin(2 pi/5),
    tau(conj chi) =  2 sin(pi/5) + 2 i sin(2 pi/5).

Checks: `conj(tau(conj chi)) = -tau(chi)`, which is `chi(-1) tau(chi)` with
`chi(-1) = chi(4) = -1`, exactly the relation `winding.py` quotes; and
`|tau(chi)|^2 = 4 (sin^2(pi/5) + sin^2(2 pi/5)) = 4 (1 - (cos(2 pi/5) +
cos(4 pi/5))/2) = 4 (1 + 1/4) = 5`, the correct Gauss-sum modulus.

**Step 3: the condition is an angle equation.** Set

    w := -i tau(conj chi)/sqrt 5 = (2 sin(2 pi/5) - 2 i sin(pi/5))/sqrt 5.

By step 2, `|w| = 1`, so `w = e^{-i psi}` with `cos psi = 2 sin(2 pi/5)/sqrt 5
> 0` and `sin psi = 2 sin(pi/5)/sqrt 5 > 0`, hence `psi in (0, pi/2)`. On the
left of (S), `alpha = (1 - i kappa)/2 = |alpha| e^{-i theta}` with
`theta = arctan(kappa)`, so `alpha/conj(alpha) = e^{-2 i theta}`. Condition
(S) reads

    e^{-2 i theta} = e^{-i psi}.

The ball solve decides `0 < kappa < 1` (`kappa_ball` raises otherwise), so
`theta in (0, pi/4)` and `2 theta in (0, pi/2)`; both sides are principal, and

    2 arctan(kappa) = psi        exactly, not merely mod 2 pi.

**Step 4: tan(psi) is 1/phi.** Using `sin(2x) = 2 sin(x) cos(x)` and the
pentagon fact `cos(pi/5) = phi/2` (this is where the golden ratio enters, and
it enters through conductor 5):

    tan psi = sin(pi/5)/sin(2 pi/5) = 1/(2 cos(pi/5)) = 1/phi.

**Step 5: the quadratic.** The double-angle formula
`tan(2 theta) = 2 tan(theta)/(1 - tan^2(theta))` with `tan(theta) = kappa`
turns step 3 plus step 4 into `2 kappa/(1 - kappa^2) = 1/phi`, i.e.

    kappa^2 + 2 phi kappa - 1 = 0.                                (Q)

**So the quadratic the linear-solve kappa satisfies is exactly
`kappa^2 + 2 phi kappa - 1 = 0`**, equivalently
`kappa^2 + (1 + sqrt 5) kappa - 1 = 0`. It is what the task's candidate
guessed, and the discriminant delivers the claimed radical:

    disc = (2 phi)^2 + 4 = 4 (1 + phi^2),
    kappa = -phi +/- sqrt(1 + phi^2).

The decided constraint `0 < kappa < 1` selects the plus sign, giving
Bombieri-Ghosh's `tau_+`; the minus sign is their `tau_-`. Corollaries:
`tau_+ tau_- = -1` (constant term of (Q)); the half-angle form
`kappa = tan((1/2) arctan(1/phi))` (steps 3 and 4 read backwards); the
tidier radical `sqrt(1 + phi^2) = sqrt(phi + 2) = 5^{1/4} sqrt(phi)` (from
`phi^2 = phi + 1` and `phi + 2 = phi sqrt 5`); and, squaring
`sqrt 5 kappa = 1 - kappa - kappa^2`, the rational quartic
`kappa^4 + 2 kappa^3 - 6 kappa^2 - 2 kappa + 1 = 0`.

Also for the record, solving (S) componentwise instead of by angles gives the
trig form quoted in section 1: the imaginary part of
`sqrt 5 (1 - i kappa) = (1 + i kappa)(2 sin(2 pi/5) - 2 i sin(pi/5))` is
`kappa (sqrt 5 + 2 sin(2 pi/5)) = 2 sin(pi/5)`, hence
`kappa = 2 sin(pi/5)/(sqrt 5 + 2 sin(2 pi/5))`; the real part is the
consistent second equation of the same one-complex-equation pair.

## 4. The decided containments

All run 2026-08-16, script `kappa_closed_form_check.py` in this session's
scratchpad; the flint leg is pinned by `tests/test_lambda_dh_separation.py`
(that file is new: `tests/test_lambda_dh_bounds.py` did not exist when this
page was written, so the test lives in the new file and says so).

**flint leg (python-flint 0.9.0, Arb), 500 bits.** `instrument.kappa_ball(500)`
is the Hurwitz-zeta self-duality linear solve, never a remembered constant.
The closed form is built from exact input balls: `arb(5).sqrt()`,
`phi = (1 + sqrt 5)/2`, `target = (1 + phi^2).sqrt() - phi`, all at 500 bits.

| check | result | radius of the deciding ball |
|---|---|---|
| `kappa_ball(500)` contains the closed-form ball | **True** (strict one-sided containment) | kappa ball 1.52e-148, target ball 2.06e-150 |
| difference ball contains 0 (overlap) | True | midpoint gap 1.30e-149 |
| quadratic residual `kappa^2 + 2 phi kappa - 1` contains 0 | True | 5.80e-148 |
| tan identity `tan(2 arctan kappa) * phi - 1` contains 0 | True | 6.31e-148 |
| Titchmarsh form minus closed form contains 0 | True | 3.91e-150 |
| `5^{1/4} sqrt(phi) - phi` minus closed form contains 0 | True | 5.46e-150 |
| trig form minus closed form contains 0 | True | 2.87e-150 |
| quartic residual contains 0 | True | 9.10e-148 |

Shared midpoint, 60 digits, both balls:
`0.284079043840412296028291832393126169091088088445737582759163`.

**mpmath.iv leg, dps 40.** The iv context has no interval Hurwitz zeta, so
the linear solve itself cannot run on this backend (the same flint-only
boundary `instrument.py`'s docstring records for the quadrature). The iv leg
therefore encloses the *trig form* of the same condition, which is the linear
solve after the exact algebra of section 3 (that reduction step is itself
decided on the flint leg by the tan-identity row above):

    k_iv      = 2 iv.sin(iv.pi/5) / (iv.sqrt(5) + 2 iv.sin(2 iv.pi/5))
    target_iv = iv.sqrt(1 + phi_iv^2) - phi_iv,   phi_iv = (1 + iv.sqrt(5))/2

| check | result | width of the deciding interval |
|---|---|---|
| `k_iv - target_iv` contains 0 | True | 1.21e-40 |
| iv quadratic residual `k_iv^2 + 2 phi_iv k_iv - 1` contains 0 | True | 1.49e-40 |
| cross-backend midpoints (flint 500-bit vs iv dps-40) | agree | abs difference 5.31e-43 < 1e-40 |

Stated honestly: the flint row is the one that touches the hunt's actual
instrument; the iv row is an independent-backend enclosure of the reduced
form, not a second route to the Hurwitz-zeta solve. Together with the
tan-identity row the two legs close the loop
linear solve -> (S) -> trig form -> closed form at enclosure grade.

## 5. The golden_control connection

`hunts/golden_control/MISSION.md` (the Pisano paragraph) pins the lab's
standing conductor-5 fact: the Davenport-Heilbronn rival is built on the
quartic character mod 5, whose square is the quadratic character chi_5, the
character of Q(sqrt 5), the golden field, and Fibonacci arithmetic mod p is
governed by that same chi_5 through the Pisano period, pi(p) dividing
p - chi_5(p). That hunt pins the connection exactly and claims it does
nothing; this page keeps the same stance and adds one instance: the golden
ratio in the closed form is not decoration but the same conductor-5
arithmetic surfacing in the coefficient itself. It enters at exactly one
point of the algebra, `cos(pi/5) = phi/2` in step 4, which turns the
Gauss-sum angle into `arctan(1/phi)`, so

    kappa = tan((1/2) arctan(1/phi)),

and the quadratic (Q) lives in Q(sqrt 5) = Q(phi), the quadratic subfield of
the conductor-5 cyclotomic field. No claim is made that this connection does
anything; it is pinned because it is exact.

## 6. Grades, in one line

The identity is **cited** (Bombieri-Ghosh 2011 section 6; Titchmarsh for the
radical form). The reduction to (Q) is in-tree algebra whose every discharge
is **decided** on the flint leg at 500 bits (section 4 table). The two-backend
containment is **decided** (flint 500 bits; mpmath.iv dps 40). Nothing on this
page is claimed as novel and nothing here moves any Lambda number; `kappa`
enters the bracket's instruments as an input ball, and this page only says
what that ball's midpoint is in closed form, and whose closed form it is.
