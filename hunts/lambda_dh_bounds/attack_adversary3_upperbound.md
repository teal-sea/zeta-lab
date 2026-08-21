# Adversary 3: attack on the upper bound Lambda_DH <= 0.4006343708899557

Scratch analysis, 2026-08-16. Remit: break the upper side. Nothing in this
file is an enclosure; every number below is measured on one route unless it
says otherwise, and the routes are my own scratch code, not the hunt's
instruments.

**Verdict: the inequality survives. One major defect found, in the
normalization dictionary, which does not move the number but does move what
the number means.**

## 1. The defect: the hunt's Lambda is not Dobner's Lambda

`THEOREM13.md` section 6 says:

> Dobner's deformation xi_t^F((1+iz)/2) = int e^{tu^2} Phi_F(u) e^{izu} du is
> the hunt's H_t up to the constant factor 2 (Phi even turns the full-line
> integral into 2 int_0^inf ... cos(zu) du), so the two share zeros and share
> Lambda exactly.

That is false. Dobner's argument satisfies s = (1 + iz)/2 = 1/2 + iz/2; the
hunt's satisfies s = 1/2 + iz. The two differ by a dilation in z, not by a
constant. Measured (mpmath dps 30, my own quadrature):

| probe | Dobner | hunt |
|---|---|---|
| G_0(1) = F(1/2 + i/2) | 1.398404431 | H_0(1/2) = 1.398404431, H_0(1) = 1.298149697 |
| G_0(2 + 0.5i) | 1.304953764 - 0.06514358269i | H_0(1 + 0.25i) = same to 10 digits |
| Phi_F(0.2) | 1.81567948188 | Phi_DH(0.4) = 1.8156794817; Phi_DH(0.2)/2 = 1.09298627044 |
| G_t(3), t = 0.4 | 1.15903455711 | H_{0.1}(1.5) = 1.15903455711 |
| G_t(2), t = 1.6 | 1.39302526542 | H_{0.4}(1.0) = 1.39302526542 |

So Phi_F(u) = Phi_DH(2u), G_0(z) = H_0(z/2), and G_t(z) = H_{t/4}(z/2). Hence

    Lambda^Dobner = 4 * Lambda^hunt.

### Why the inequality still stands

de Bruijn's Theorem 13 is applied entirely inside the hunt's own
normalization, on the hunt's own Delta, so no factor of 4 enters the
derivation. Dobner is used only for the half-line structure and for
Lambda >= 0, and both properties are invariant under t -> t/4. The claim, as
stated with its own definitions of Phi_DH, H_t and Lambda_DH, is correct.

### Why it matters anyway

`NOVELTY.md` calibrates the result against "the zeta record 0 <= Lambda_zeta
<= 0.22 (Rodgers-Tao; Polymath 15), Lambda_zeta < 1/2 (Ki-Kim-Lee 2009)".
Those numbers live in the standard convention, the one Dobner uses, the one
Rodgers-Tao use, and the one `zeta/heatflow.py` uses: H_0(z) = (1/8) Xi(z/2),
kernel exp(-pi n^2 e^{4u}). The hunt's Phi_DH uses exp(-pi n^2 e^{2u}), which
is the a = 1 convention. Converting the hunt's headline into the convention
its own calibration is quoted in:

    0.2304 < Lambda_DH <= 1.6025374836        (standard convention)

and conversely zeta's classical 1/2 becomes 1/8 in the hunt's convention. A
reader who sets "Lambda_DH <= 0.4006" beside "Lambda_zeta < 1/2" concludes
the DH constant is comfortably below zeta's classical bound. In a common
normalization the DH upper bound is 3.2 times zeta's classical 1/2 and 7.3
times Polymath's 0.22.

Fix, either way round: state Phi_DH(u) = 8 e^{3u} sum_n n a_n
exp(-pi n^2 e^{4u} / 5), which puts H_0(z) = Xi_DH(z/2) and matches
`zeta/heatflow.py` exactly, or keep the present convention and print both
numbers side by side. In both cases delete the "share Lambda exactly"
sentence.

## 2. Attacks that failed

### 2.1 Theorem 13 read from the original scan

Fetched https://pure.tue.nl/ws/files/1769368/597490.pdf and read pages
203 to 205 as images. Theorems 10, 11, 12, 13 and 14 match `THEOREM13.md`
word for word. In particular Theorem 13 (p. 205) reads

> If F(t) satisfies the conditions of Theorem 10, and if all the roots of
> (3.6) lie in the strip |Im z| <= Delta, then all the roots of
> g(z) = int_{-inf}^{inf} F(t) e^{(1/2)lambda^2 t^2} e^{izt} dt lie in the
> strip (3.8) |Im z| <= {Max(Delta^2 - lambda^2, 0)}^{1/2}.

with no "(all but a finite number of the roots)" parenthetical in either
hypothesis or conclusion, unlike Theorems 11 and 12 on the same and facing
pages, which do carry it. Theorem 10 (p. 204) gives the class conditions as
exactly: b > 2, F integrable over the real line, (3.4) F(t) = (F(-t))*, and
(3.5) F(t) = O(e^{-|t|^b}). No positivity, no monotonicity, F may be complex.
The multiplier is e^{(1/2)lambda^2 t^2}, so t = lambda^2/2 and the all-real
threshold is t >= Delta^2/2. Kill condition 1 of `MISSION.md` is genuinely
not triggered.

### 2.2 The triangle equality case on Re s = sigma_0

Correct as written, and airtight. Every term a_n n^{-s} with n not divisible
by 5 is nonzero, so equality in the triangle inequality forces all of them
onto a common ray. a_3 = -kappa < 0 forces 3^{-it} = 1, a_4 = -1 < 0 forces
4^{-it} = 1, a_12 = kappa > 0 forces 12^{-it} = -1, and 12 = 3 * 4.

Note this step is not load-bearing: Theorem 13 wants a closed strip, and step
(b) evaluated at the decided rational sigma* = 1.3951361582351097210613589375
already delivers |Im z| <= sigma* - 1/2 without it.

### 2.3 The functional equation and the gamma factor

Rebuilt from scratch, sharing no code with the hunt. Linear solve for kappa
at s = 2.3 + 1.7i (mpmath dps 50) gives

    kappa = 0.2840790438404122960282918323931261690911
    imaginary residue 7.08e-51
    |kappa - KAPPA_REF| = 1.19e-41

and |F(s) - F(1-s)| <= 5.42e-51 at s = 1.1+0.3i, 0.2+5i, -1.5+2.2i. The
completing factor is (pi/5)^{-(s+1)/2} Gamma((s+1)/2), the odd-character
shape. Structurally kappa is forced: with F = c Lambda(s, chi) +
conj(c) Lambda(s, chibar) and c = (1 - i kappa)/2, the requirement
F(s) = F(1-s) is exactly eps(chi) = conj(c)/c, a unit modulus condition with
a unique real solution. So kappa is the constant making it hold, not a
constant chosen to nearly make it hold.

### 2.4 The trap: trivial zeros and the gamma poles

Worked out and it holds. Measured at dps 50:

| s | f(s) | F(s) | F(1-s) |
|---|---|---|---|
| -1 | 1.02e-51 | 1.77952795928 | 1.77952795928 |
| -3 | 3.92e-51 | 4.29503671195 | 4.29503671195 |
| -5 | 4.89e-50 | 16.9670072265 | 16.9670072265 |
| -7 | 1.22e-48 | | |

So f has simple zeros at s = -1, -3, -5, ..., each exactly cancelling a
simple pole of Gamma((s+1)/2), and F is finite and nonzero there. Xi_DH
inherits no zero from the gamma factor, because neither (pi/5)^{-(s+1)/2} nor
Gamma has any zero at all. The trivial zeros are zeros of f and not of F, and
`STRIP.md` section 3(e) states this correctly.

This is a check with teeth rather than a formality. If f had a double zero at
any s_m = -(2m+1), F would vanish at Re s = -(2m+1), which is outside the
strip, and the upper bound would collapse. It does not happen at the four
points tested, and it cannot happen anywhere, because F(s_m) = F(1 - s_m) and
1 - s_m = 2m + 2 lies in the half-plane Re s >= 2 where g(2) < 0 already puts
f away from zero.

### 2.5 Uniformity in the height

The domination |f(s)| >= 1 - sum_{n>=2} |a_n| n^{-Re s} depends on Re s only:
|n^{-s}| = n^{-Re s} exactly. There is no height-dependent term anywhere in
the argument, so no large |Im s| escape route exists. This is a property of
the construction, not a claim needing a check.

### 2.6 H_0 really is Xi_DH, with the stated Phi_DH

Derived independently. F(s) = int_0^inf Theta(x) x^{(s+1)/2} dx/x with
Theta(x) = sum_n n a_n exp(-pi n^2 x / 5); substituting x = e^{2u} gives
F(1/2 + iz) = int_{-inf}^{inf} 2 e^{3u/2} Theta(e^{2u}) e^{izu} du, and the
half-line cosine form doubles the prefactor to 4. So the constant 4 is
forced, not fitted. Measured agreement of H_0 against F(1/2 + iz):

| z | relative error |
|---|---|
| 0 | 0 |
| 1 | 8.9e-42 |
| 3 + 0.9i | 1.8e-41 |
| 0.5 + 0.895136i (on the strip edge) | 3.6e-41 |
| 10 - 0.8i | 8.7e-41 |
| 85 + 0.3i | 3.2e-18 (|Xi| there is 2.1e-28) |

Fitting H_0(z) = c Xi_DH(a z) gives c = 1 exactly and
a = 1 - 7.4e-42 i. Phi evenness measured at |u| = 0.1, 0.4, 0.9, 1.5:
relative differences 2.0e-41, 0, 5.0e-41, 2.9e-38.

### 2.7 The strip constant, recomputed

Independent route (mpmath dps 50, Hurwitz zeta, my own kappa):

    sigma_0 = 1.3951361582351097210613588973265388
    Delta   = 0.895136158235109721061358897327
    Delta^2/2 = 0.400634370889955694446954776081

inside the hunt's flint bracket [1.3951361582351097210613588712,
1.3951361582351097210613589375]. A brute-force check that does not use the
residue-class identity at all (direct float64 sum of |a_n| n^{-sigma} over
n <= 2e6 plus an integral-test tail) brackets g(sigma_0) in
[-4.21e-3, +3.99e-3], consistent with 0.

The headline decimal is a rounding in the safe direction: the exact
Delta*^2/2 at the decided rational sigma* is 0.4006343708899556944469548120
(outward), and the claimed 0.4006343708899557 exceeds it by 5.553e-18.

### 2.8 The strip-to-time dictionary, recalibrated

The operator was derived rather than recalled: multiplying by u^2 under
int Phi e^{izu} du is -d^2/dz^2 on the transform, so H_t = exp(-t d^2/dz^2)
H_0. Verified on the actual DH object by central differences at
(t, z) = (0.4, 2.3), dps 30: dH/dt = 1.95104693155701e-4 versus
-d^2H/dz^2 = 1.95104693155765e-4, residual 6.43e-17.

Bare conjugate pair p(z) = z^2 + D^2 flows to z^2 + D^2 - 2t, so it lands at
exactly D^2/2. Measured by 200-step bisection on the exact finite series:

| D | t* | D^2/2 | D^2/8 | 2D^2 | 2t*/D^2 |
|---|---|---|---|---|---|
| 0.300000 | 0.045000000000 | 0.045000000000 | 0.011250 | 0.180000 | 1.0000000000 |
| 0.600000 | 0.180000000000 | 0.180000000000 | 0.045000 | 0.720000 | 1.0000000000 |
| 0.895136 | 0.400634370890 | 0.400634370890 | 0.100159 | 1.602537 | 1.0000000000 |
| 1.000000 | 0.500000000000 | 0.500000000000 | 0.125000 | 2.000000 | 1.0000000000 |
| 2.000000 | 2.000000000000 | 2.000000000000 | 0.500000 | 8.000000 | 1.0000000000 |

D^2/8 and 2D^2 are both refuted by a factor of 4. Distant real spectators
only accelerate the landing, approaching the bound from below:
(z^2 + D^2)(z^2 - A^2) at D = 0.895136158235 gives 2t*/D^2 = 0.8738, 0.9846,
0.99936, 0.99998 for A = 3, 10, 50, 300. Two pairs at unequal heights land
strictly early, so the bound reads off the deepest pair, as it should.

### 2.9 The same machinery on zeta reproduces the literature

In `zeta/heatflow.py`'s convention H_0(z) = (1/8) Xi(z/2), the classical
zero-free half-planes give zeros of Xi in |Im| <= 1/2, hence Delta = 1 after
the z/2, hence Delta^2/2 = 1/2. That is de Bruijn's published bound exactly.

The same run also prices the elementary route. Feed zeta through the DH
argument's own domination (root of zeta(sigma) = 2):

    sigma_0(zeta) = 1.7286472389981836181
    Delta in the standard convention = 2 * 1.228647239 = 2.457294478
    Delta^2/2 = 3.0191480758

which is 6.04 times worse than the true 1/2. The Euler product is what buys
zeta that factor. DH has none, so a comparable slack should be assumed here
and is not visible from inside the argument.

## 3. Sharpness

0.4006 is not close to tight, and all the slack is in the strip constant, not
in de Bruijn's 1/2, which section 2.8 shows is attained on the extremal
family.

**Where the zeros actually are.** The repo's pinned off-line zero has
Re rho = 0.808517, so |Im z| = 0.3085. The census's deepest new pair at
gamma = 531.2797 has beta = 0.846954, so |Im z| = 0.3470. Against
Delta = 0.8951 that is a factor of 2.6 in the strip and about 6.7 in the
bound. DH is known to have zeros with Re s > 1, so the true supremum is at
least 0.5, but that only lifts the honest range: if the supremum were 0.5 the
de Bruijn bound would be 0.125, and at 0.6 it would be 0.18. With the
measured floor at 0.0577, the truth sits somewhere in (0.0577, 0.4006] and
nothing on disk narrows that.

**The strip constant is improvable now, with an argument the hunt already
has.** `STRIP.md` step 3(c) proves the triangle bound is never attained, via
12 = 3 * 4, and then discards the quantity. Keep it. On Re s = sigma the
values n^{-it} are, by Kronecker and the Q-independence of the log p, exactly
free independent phases on the primes, so the closure of the head's value set
is the set of sums with arbitrary prime phases. Define

    B_M(sigma) = min over prime phases of |sum_{n<=M} a_n n^{-sigma}
                 e^{i <v(n), theta>}|  -  sum_{n>M} |a_n| n^{-sigma}

Any sigma with B_M(sigma) > 0 is a valid strip constant, and M = 1 is the
hunt's present bound. Measured (float grade, L-BFGS with 25 restarts, tail
by the Hurwitz identity):

| M | sigma_0^(M) | Delta | Delta^2/2 |
|---|---|---|---|
| 1 | 1.39513616 | 0.89513616 | 0.40063437 |
| 4 | 1.39513616 | 0.89513616 | 0.40063437 |
| 12 | 1.37988698 | 0.87988698 | 0.38710055 |

M = 4 buying nothing and M = 12 buying the first gain is exactly the hunt's
own n = 12 witness: on n <= 4 the choice 2^{-it} = -1, 3^{-it} = 1 attains
the triangle bound, and 12 is the first n that cannot be aligned with it.
That is a 3.4 percent improvement in the bound for eleven extra terms, and
the sequence is monotone non-increasing in M by construction.

This is not a float-only route. The head is a trigonometric polynomial in
finitely many phases with an explicit gradient bound, so its minimum over the
torus can be enclosed by a Lipschitz grid using the same interval machinery
`strip.py` already carries, and the tail is the same Hurwitz expression.
The improvement is available at the grade the hunt already works at.

**The literature offers no better lever that I can find.** Ki-Kim-Lee 2009's
Lambda_zeta < 1/2 is a zeta-specific strictness result, and the
all-but-finitely-many statements (de Bruijn Theorems 11 and 12, Ki-Kim 2003
Theorem 2.2) have weaker conclusions at the same constant. Theorem 13's 1/2
is sharp. The strip is the only place to push.

## 4. Minor items

- `THEOREM13.md` section 5.3 asserts that g(u) = (pi/5) e^{2u} - (3/2)u - u^3
  is increasing on [2, 30] from a 201-point grid. A grid does not show
  monotonicity. One line does: g'(u) = (2 pi/5) e^{2u} - 3/2 - 3u^2, and at
  u = 2 that is 68.6 against 13.5, with the exponential dominating 3u^2
  thereafter. Replace the grid claim with the derivative.
- The headline 0.4006343708899557 is a rounded-up form of Delta*^2/2 and
  reads as if exact. Say so, or quote the outward endpoint.

## 5. Scratch code

`/tmp/claude-0/-home-user-zeta-lab/ea2c50e5-c6c1-5be9-ac30-eda79b8fac85/scratchpad/`:
`a3_strip.py` (kappa, sigma_0, trivial zeros), `a3_transform.py`
(H_0 versus Xi_DH, scale fit), `a3_dict.py` (polynomial flow calibration),
`a3_zeta.py` (backward heat on the DH object, zeta convention),
`a3_dobner.py` (the normalization defect), `a3_sharp.py` and `a3_sharp2.py`
(Bohr value set and the improved strip constant), plus the de Bruijn scan
`debruijn1950.pdf`. No hunt artifact was modified.
