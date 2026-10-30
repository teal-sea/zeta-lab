# RIVAL: a Davenport-Heilbronn function over F_7[T], and where the local identity refuses it

**Hunt #148, step 5. Status: exact algebra and ball-enclosed zeros at the stated
parameters; files produced on branch `hunt/ff-probe`, not landed.** Every number here is
read from `results_rival.json` and pinned by `test_ffprobe.py`. Grades as in `MISSION.md`.

## The rival

Let chi be a Dirichlet character modulo T^3 over F_7[T]. Writing a monic a prime to T as
a = a_0 (1 + x T + y T^2) mod T^3,

    chi(a) = eps(a_0)^e zeta_7^(alpha x + beta (y - x^2/2)),

which is primitive modulo T^3 when beta != 0 and odd (nontrivial on F_7^x) when e != 0 mod 6.
There are 5 x 7 x 6 = 210 such characters. For each, L(u, chi) = 1 + c_1 u + c_2 u^2 is
computed by summing chi over the monic polynomials of degree at most 4 (the coefficients of
u^3 and u^4 vanish), and the functional equation is checked exactly: c_2 = 7 eps(chi) with
|eps(chi)| = 1, and c_1 = eps(chi) conj(c_1). It holds for all 210 characters (derived and
checked, `results_rival.json`, `counts`).

The rival is

    D(u) = L(u, chi) + eps L(u, conj chi),

which is eps^(1/2) times the requested eps^(-1/2) L(u, chi) + eps^(1/2) L(u, conj chi), so it
has the same zeros and needs no square root of eps in the field. Exactly (checked):

    D(u) = (1 + eps)(1 + 7 u^2) + (c_1 + eps conj(c_1)) u,

so D(u)/(1 + eps) = 1 + beta u + 7 u^2 with beta = (c_1 + eps conj(c_1))/(1 + eps) real.
No character gives 1 + eps = 0. **The zeros are u = (-beta +- sqrt(beta^2 - 28))/14 exactly**:
a pair on the circle |u| = 7^(-1/2) when beta^2 <= 28, and two real zeros off it, with
product 1/7, when beta^2 > 28.

## Its zeros lie off the circle

For 66 of the 210 characters, beta^2 > 28 and both zeros lie off |u| = 7^(-1/2); in every one
of the 66, an Arb ball enclosure of |u| sqrt(7) (python-flint `acb_poly.roots` at 200 bits)
excludes 1, and the off-circle cases are exactly those with beta^2 > 28 (hardened: exact
discriminant and ball enclosure agree). In the language of real parts, |u| = 7^(-sigma),
the larger abscissa of the pair is distributed as follows (measured from the enclosures'
midpoints, four decimals):

| larger abscissa sigma | characters |
|---|---|
| 0.5668 | 4 |
| 0.6618 | 8 |
| 0.8695 | 4 |
| 1.0069 | 8 |
| 1.0134 | 4 |
| 1.0409 | 4 |
| 1.0866 | 2 |
| 1.1124 | 4 |
| 1.1542 | 2 |
| 1.1989 | 12 |
| 1.3763 | 8 |
| 1.9896 | 4 |
| 2.1781 | 2 |

So 50 of the 66 rivals vanish beyond sigma = 1, inside the half-plane where their Dirichlet
series converges absolutely, as the classical Davenport-Heilbronn function and hunt #120's
Epstein zeta do. None vanishes between 0.8695 and 1. **The named example** is
(e, alpha, beta) = (2, 2, 2): its zeros are at sigma = 1.00685535 and -0.00685535 (ball midpoints; the two sum to 1)
(|u| sqrt(7) = 0.37296 and 2.68128), both off the circle by enclosure. Since the template
asserts a zero-free half-plane Re > 7/8 for single L-functions with an Euler product, a rival
satisfying the template's hypotheses would contradict it; the point of this page is that it
does not satisfy them, and exactly where.

## Its local identity fails at the term X^2

The probe of `LOCAL_IDENTITY.md` is linear in the target's coefficients. Give it the rival's
normalized coefficients d(a) = (chi(a) + eps conj(chi)(a))/(1 + eps), so that d(1) = 1, and
compare two series for the principal row u = 1, in the variables X = 7^(-x) (degree of
A = c n^3) and W = 7^(-w) (degree of s), up to X^3 W^1:

- the **definition**: the sum of K(c, n, s, a; 1) over all indices, with eta replaced by d;
- the **local identity**: the product over primes of the closed-form local factors of
  Lemma 7.1, with eta(p) replaced by d(p), which is what the lemma would assert if d had an
  Euler product.

For chi itself the two series agree at every monomial up to X^3 W^1 (the control). For the
rival they first differ **at X^2 W^0**, the coefficient fed by A = P_1 P_2 for two distinct
linear primes, and also at X^2 W, X^3 and X^3 W. At X^2 the definition gives a coefficient of
modulus 3.7170 and the local identity a coefficient of modulus 20.5502 (exact cyclotomic
values in `results_rival.json`). The failing ingredient is multiplicativity: at
P_1 = T - 1, P_2 = T - 2, |d(P_1 P_2)| = 2.4661 while |d(P_1) d(P_2)| = 0.1702.

By linearity the rival's principal row is the combination, with weights 1/(1 + eps) and
eps/(1 + eps), of the principal rows for chi and conj chi; its poles in x are the zeros of
L(x, chi) and L(x, conj chi), which lie on Re x = 1/2, and the zeros of D never enter. The
probe therefore cannot be fooled by the rival, and the step that refuses it is the scalar
Euler identity: this is hunt #120's reading of the number-field argument, now checked in
exact arithmetic over F_7[T]. It is a statement about this rival and this probe, not about
the 7/8 paper's correctness elsewhere.

## Reproduce

```
.venv/bin/python hunts/ff_probe/ffprobe.py --part rival        # writes results_rival.json
.venv/bin/python -m pytest -q -n0 hunts/ff_probe/test_ffprobe.py -k rival
```
