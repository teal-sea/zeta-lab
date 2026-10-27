# Guo's Hypothesis 11.1: which mean value it is, what implies it, and 328/375

**Hunt #136, lane b78-amplification, 2026-10-21. Lane output, unreviewed by any person.
Nothing here is a result until the case log in `hunts/README.md` says how the hunt ended.**
Every fraction and decimal on this page is recomputed by `price.py` and pinned by
`test_price.py`; integers are line numbers or the integer coefficients of a quoted
identity, which the tests check against the source.

Grades as in `MISSION.md`: *cited* (a line of a source file, quoted, with the file's
SHA-256 checked by `price.verify_citations`), *derived* (exact arithmetic here, pinned by a
test), *inferred* (a reading or a standard step that no computation here checks),
*measured* (float). Nothing on this page bears on real part 1/2, and no abscissa below is
claimed as established: every one is conditional on an unproved hypothesis or on inputs
this lane does not check.

Sources (read as data, outside the tree):

| key | file | SHA-256 |
|---|---|---|
| guo11 | `followups/run-2026-10-21T1440Z/guo_zf/source/sections/11_limits.tex` (github.com/aster2024/openai-math-followups) | `59442f55...2017` |
| guo06, guo05 | sections `06_geometry.tex`, `05_count.tex` of the same source | `e81e698d...b8a`, `579f88ec...a8` |
| paper | `openai-math-adc7f124/paper.tex` (OpenAI, 2026-09-30) | `42a5ee0f...a6a3` |
| by | `baier-young-0804.2233v3/cubicmeanvalues2008-09-01.tex` (arXiv:0804.2233v3, downloaded here 2026-10-21) | `0d36f78f...aaa` |

## 1. The inequality, exactly

Guo, section 11, lines 33 to 46 (cited). Fix a finite-order ray character `nu` with its
zero-extended presentation, a finite set `S` of primes containing its modulus support and
the primes over 6, a compact interval `I = [a, b]` in `(0, infinity)`, and a nonnegative
radial Schwartz majorant `Phi` with `Phi >= 1` on `[0, 1]` and compactly supported Fourier
transform. Put

    A_u(D) = sum over (n, S) = 1 of mu(n) nu(n) chi_n(u) W(q_n / D),
    M(D, H) = (1/D) sum over u in O of Phi(q_u / H) |A_u(D)|^2.

**Hypothesis 11.1.** For every such datum and every `eps > 0` there are `J` and `C` with
`M(D, H) <= C H D^eps ||W||^2_{C^J(I)}` for all `D >= 2`, all `D^(99/100) <= H <= D^(101/100)`
and all `W` in `C_c^infinity(I)` (line 43 and line 45, cited).

In the paper's notation, `M_u(D; W) = D^(-1/2) sum mu(n) nu(n) chi_n(u) W(q_n/D)` (line 5225,
cited), so the hypothesis is the bound `sum_u Phi(q_u/H) |M_u(D; W)|^2 << H D^eps`. **It is the
paper's equation `raw-moment` (lines 12353 to 12357) with its range `H >= D^(1+c)` extended down
to `H >= D^(99/100)`** (derived from the two cited displays): a Moebius-weighted mean square of
sextic-character polynomials of length `D`, over every row `u` of norm at most about `H`, at
diagonal size, with slightly fewer rows than columns. The paper obtains `raw-moment` from
Lemma 17.1 at `Z = H`, `m = 1`, no prime slots (lines 12345 to 12350, cited); Lemma 17.1's first
width condition `r + 2z <= m - c_1` (line 9254, cited) is then `r = log_H D <= 1 - c_1`, and the
hypothesis asks for `r <= 100/99`. Guo states that the 11/12 companion paper's Proposition 3.1
proves the case `H = D^(1 + theta)`, `0 < theta <= 1/10` (line 33, cited; the companion was not
read in this lane). Two further differences are cosmetic: the smooth majorant `Phi` in place of
the sharp ball, and the explicit `C^J` norm of `W`.

Its use (line 61 to 63, cited) is Lemma 17.6's proof with `H' = max(2U, D^(99/100))` in place of
`H = max(2U, D^(1+c))`: then `H'/P = U^(1/6) H'^(5/6)` and the amplified exponent becomes
`e_99(r) = max{1, 1/6 + 33r/40}` (derived: `(5/6)(99/100) = 33/40`). In `price.py` this is the law
`Law.threshold(99/100)`, slope 33/40 and intercept 1/6.

## 2. Does a published theorem imply it?

**No, in the searched set, and for two reasons that are checkable here.**

**(a) No mean value for arbitrary coefficients can give it** (derived, one line). For any row
family containing `u = 1`, where `chi_n(1) = 1` for every column `n`, an inequality
`sum_u |sum_n c_n chi_n(u)|^2 <= Delta sum_n |c_n|^2` valid for all `c` forces `Delta >= N`, the
number of columns: take `c_n = 1` and keep only the row `u = 1`, which contributes `N^2`.
Applied to the Moebius coefficients, such an inequality therefore bounds `M(D, H)` by a
constant times `D` at best, never by `H D^eps` when `H = D^(99/100)`. The two named results are of
this kind:

- **Heath-Brown's cubic large sieve** (Israel J. Math. 120 (2000), Theorem 2; quoted by Baier
  and Young at line 195 of their source, and in its sextic primary-convention form as the
  paper's own Lemma sextic-large-sieve, line 4717, both cited; Heath-Brown's paper itself was
  not read): arbitrary coefficients on squarefree elements, constant `M + N + (MN)^(2/3)`. At
  `H` rows and `D` columns with `H = D^(99/100)` this is at least `(HD)^(2/3)`, which exceeds `H`.
- **Baier and Young, "Mean values with cubic characters"** (arXiv:0804.2233v3, whose source was
  read; published in J. Number Theory 130 (2010) per a web search), Theorem 1.3 (line 171) and its
  sextic extension Theorem 1.4 (line 205), cited: primitive cubic, and sextic, Dirichlet characters to moduli `q` in
  `(Q, 2Q]`, rational squarefree `m` in `(M, 2M]`, arbitrary coefficients, constant
  `min{Q^(5/3) + M, Q^(4/3) + Q^(1/2) M, Q^(11/9) + Q^(2/3) M, Q + Q^(1/3) M^(5/3) + M^(12/5)}`.
  Every branch is at least `M`, as (a) says it must be; the family is also a different one
  (rational columns, Dirichlet characters), so it does not even address the rows `u in Z[w]`.

**(b) The hypothesis alone already implies a zero-free half-plane** (derived from its own
statement; the passage from smoothed partial sums to the Dirichlet series is the standard
Mellin step, inferred). Keep only the row `u = 1` in `M(D, H)` and take `H = D^(99/100)`:
`|A_1(D)|^2 <= C D^(199/100 + eps)`, so `sum mu(n) nu(n) W(q_n/D) << D^(199/200 + eps)` for every
`W`, and `1/L^S(s, nu)` is holomorphic in `Re s > 199/200`. Using the rows `u = a^6` as well,
which is Lemma 17.6's argument at `U = 1` with the hypothesis in place of `raw-moment`, gives
`|M_1(D)|^2 << H^(5/6)` and the abscissa `1/2 + (5/12)(99/100) = 73/80`. Every finite-order Hecke
character of `Q(sqrt(-3))` is such a `nu`, so Hypothesis 11.1 by itself gives every finite-order
Hecke L-function of that field, and through the paper's transfer (lines 310 to 318) every
Dirichlet L-function, no zeros in `Re s > 73/80`. A zero-free half-plane of any width was open
before the 2026 preprints (the 7/8 preprint presents its theorem as resolving that question,
lines 113 to 116, cited), so no earlier theorem can imply the hypothesis without having implied
that. Of the 2026 results read by this hunt (the 7/8 preprint, Liu, Xu and Sang, Guo,
the tracker records; `FOLLOWUPS.md`), none states a mean value of this shape with fewer rows
than columns; the 7/8 theorem itself only bounds each row pointwise, giving `H D^(3/4)`
(inferred from the reading; this is not a search of the whole literature).

The same test applied to the paper's own input is a consistency check, not a new claim:
Lemma 17.6 at `U = 1` reads `|M_1(D)|^2 << D^(5(1+c)/6)`, which is a zero-free half-plane
`Re s > 11/12` for every `L(s, nu)`, the abscissa of the paper's Part I. A raw moment valid for
`H >= D^theta` gives `1/2 + 5 theta/12` this way (`price.trivial_route_abscissa`): 11/12 at
`theta = 1`, 73/80 at `theta = 99/100`, 7/8 at `theta = 9/10`, 7/9 at `theta = 2/3` (derived).
Conversely GRH for the family implies the hypothesis (shift to `Re s = 1/2 + eps`; inferred). So it
sits between GRH and a zero-free half-plane, and is at least as deep as the latter.

## 3. The claimed consequence 328/375, recomputed

Guo's proposition `prop:conditional` (lines 50 to 99, cited), checked step by step in exact arithmetic:

- **Geometry** (lines 81 to 83): `ell = 21/125`, `b = 11/100` give `l_x = 361/1000`, `l_y = 471/1000`,
  `h = 807/1000` and `sigma = 11/12 - ell/4 = 328/375` (derived).
- **Counts** (lines 73 to 75): with `e_99`, the crossing of the short count with the long
  branch `1/6 + (33/40 - delta) t` is `t_99 = 1 + (D_x/120 + delta P_x/2)/J_99` and the excess over
  `1 - delta` is `T_99 = (97/120 - delta) delta P_x / (2 J_99)`, `J_99 = (33/40 - delta) D_x + delta P_x`
  (derived: `price.excess` with `Law.threshold(99/100)` equals `T_99`, and the minimisation over
  `t` done directly lands on `t_99`).
- **Endpoint** (Guo `06_geometry.tex` line 15): `E_99 = -1/4 + b/6 + 5 ell/4 - b delta/2 -
  ell (1/2 - x) delta + h T_99`, which is hunt #134's `E_*` on the face `M + ell = 1`.
- **The polynomial identity** of lines 86 to 89, `20000(-108 J_99 E_99) = 526080 delta^2 - 406288 delta
  + 79365 + y(1292640 delta^2 - 603308 delta + 72930) + y^2 (920640 delta^2 - 19144 delta) + 322560 y^3
  delta^2` with `y = 1/2 - x`, holds exactly: both sides have degree at most 2 in `delta` and 3 in `y`,
  and they agree on a 13 by 5 rational grid (derived).
- **The three completed-square remainders** of lines 92 to 94 are exactly 45529856, 13108397936
  and 1763264 (derived).
- **The bound** `E_99 <= -7/42768` on `0 <= delta <= 3/4`, `0 <= x <= 1/2` (line 98) is decided true by
  this lane's own exact rectangle procedure, which does not use Guo's squares (derived).

So, given Hypothesis 11.1 and the rest of Guo's envelope (whose other inputs are the paper's
lemmas, not checked here), the endpoint inequality at 328/375 holds. **328/375 is a rational
point, not the envelope's infimum.** Under `e_99` the exact optimum of the same endpoint system
(hunt #134's frame with `delta <= 3/4`, which is Guo's criterion of `06_geometry.tex` line 22) is

    2305/2529 - 8 sqrt(22906)/32877 = 0.8745999251,

at `ell = 0.1682669662`, `b = 0.1093307117`, inside Guo's geometry box `1/6 <= ell <= 17/100`,
`1/10 <= b <= 13/100` (derived; the sandwich of `LOSS_MAP.md` section 4 agrees). Inside Liu's
refined comparison system the same hypothesis gives the fixed point 0.8744476409, at
`kappa = 0.7488952817`, which lies below the `kappa` range `7497/10000 <= kappa <= 3/4` in which
Liu's tangent family is stated (derived; Liu's admissibility would have to be re-checked
there). Both are conditional numbers about comparison systems, not claims.

For scale: the tracker's record is `8748087/10^7 = 0.8748087` (`FOLLOWUPS.md`, cited there). The
raw-moment threshold that would reach it is `theta = 0.9958275690` in hunt #134's system and
`0.9982147398` in Liu's (derived, `LOSS_MAP.md` section 4): Guo's `99/100` is well past both.

## 4. The rival gate

What the hypothesis and its use rely on, explicitly: the sixth-power identity
`psi_{u a^6}(m) = psi_u(m) 1_{(m,a)=1}` (paper line 12420), which is the multiplicativity of the
residue symbol in its upper argument together with `chi^6 = 1`; the Moebius function's
multiplicativity and squarefree support (the exact column identity, line 12428); and
`|chi| <= 1` (the coefficient mass `d(a)`, line 12430).

- **`W_a = zeta(s + a) zeta(s - a)`, `a > 3/8`.** Over `F` the rival is `zeta_F(s + a) zeta_F(s - a)`;
  its inverse coefficients `mu_a`, of `1/(zeta_F(s + a) zeta_F(s - a))`, are multiplicative but not
  bounded: `mu_a(p) = -(q_p^a + q_p^(-a))`. For `a > 33/80` the hypothesis fails for this rival by
  the argument of section 2(b): the column identity still holds for a multiplicative sequence
  supported on cube-free ideals, with coefficient mass `<< P^eps` when `a < 1/2`, so the hypothesis
  would make `zeta_F(s - a)` zero-free in `Re s > 73/80`, that is `zeta_F = zeta L(s, chi_-3)`
  zero-free in `Re w > 73/80 - a < 1/2`, against Hardy's theorem for `zeta` (the argument of
  section 2(b), its Mellin step inferred; Hardy cited from the literature). For `3/8 < a <= 33/80` failure is
  **not shown** here. Its diagonal alone, `(1/D) sum_{n <= D} mu_a(n)^2`, grows like `D^(2a)`
  against the `D^eps` per row that the hypothesis allows (measured over the rational integers: the
  ratio to `D^(2a)` is 0.87 at `a = 0.4` and 0.73 at `a = 0.45`, `D = 20000`), but in the range
  `D <= H <= D^(101/100)` the off-diagonal is not controlled by anything checked here.
- **Epstein zeta of discriminant -15.** The coefficients `r_Q(n)/2` of `Q = x^2 + xy + 4y^2` are
  not multiplicative: `a(6) = 2` while `a(2) a(3) = 0` (derived, `zeta.epstein`), so the column
  identity has no analogue. Applied to the inverse coefficients of `Z_Q`, the row `u = 1` of the
  hypothesis would make `1/Z_Q(s)` holomorphic in `Re s > 199/200`, against the zeros of `Z_Q` in
  `Re s > 1` (Davenport and Heilbronn 1936, cited from the literature as `zeta/epstein.py` does,
  not recomputed here).

So the hypothesis is not a generic inequality: it fails for the Epstein rival and for `W_a` at
least when `a > 33/80`. That is the gate it must pass to be worth proving; it says nothing about
whether it is true.

## 5. Limitations

- Guo's other inputs (Lemma 17.1, Lemma 18.1 at `kappa = 3/4`, the detector, the uniform side
  conditions on his geometry box) are taken as stated; nothing here checks them.
- Heath-Brown 2000 was read only through two quotations; the companion paper's Proposition 3.1
  was not read.
- Section 2(b) uses the standard step from bounds on smoothed partial sums to holomorphy of the
  Dirichlet series; it is inferred, not formalized.
- "No published theorem implies it" is a statement about the results named here and the
  structural reasons (a) and (b), not a search of the literature.
