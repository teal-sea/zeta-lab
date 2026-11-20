# RESULTS: the interface inequality of a posted RH claim, measured (hunt #161)

Status: **measured, with Arb enclosures at the extremal points and at spot
checks; one derivation calibrated numerically; no claim promoted.** Nothing here evaluates the posted
proof. Nothing here is evidence for RH. A finite computation is never a uniform
RH result.

Reading guide to the rungs used below. *Text*: read off the archive, no kernel.
*Derivation*: ordinary pencil derivation, assumptions stated, not independently
reviewed. *Measured*: one route, float grade. *Hardened*: independent routes
agree and Arb enclosures carry every step of the number in question.

## 0. What was found

1. **Transcription (text).** The definitions of `Gz`, `gChi`, `Level.Gm`,
   `Level.cyc` and the windowed statement are as the two readers reported.
   Quotes with path, line and file hash are in `transcription.json`; the joined
   tarball has sha256
   `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
   The archive states the windowed statement; whether its proof text is sound
   was not examined.
2. **The explicit formula survives calibration (derivation, hardened at spot
   points).** For `y >= 1`,
   `G(y) = sum_rho y^rho/(rho(1-rho)) + log(2 pi) + T(y)`. With 20000
   Arb-isolated zeros the prime side and the zero side differ by at most 0.082
   of the exact tail budget at 256 points up to 9.8 * 10^7.
3. **The RH envelope, measured.** `F(y) = (G(y) - log 2pi - T(y))/sqrt(y)`
   equals `c0 = 2 + gamma - log(4 pi) = 0.0461914179...` at `y = 1` (an
   identity). Over `2 <= y <= 10^9` its maximum is 0.0246942450780346
   (0.5346 of `c0`) at `y = 34186454.425380` and its minimum is
   -0.0226812404958921 (-0.4910 of `c0`) at the prime `y = 319439`. Scan:
   measured. The two values: hardened.
4. **Characters.** The character formulas (even and odd differ) calibrate for
   all 26 primitive characters of conductor at most 12. For all 35 levels
   `Level.cyc psi` with conductor at most 20, `Gm` stays within 0.7180 of the
   GRH envelope on `100 <= y <= 10^7`. A single character reaches 0.9463 of
   its envelope, and the reason is a zero of `L(s, chi_19(3, .))` at height
   -0.0190.
5. **The criterion has teeth only far out.** A planted quadruple
   `beta +- i gamma0`, `1 - beta +- i gamma0` first violates `G(y) <= y^theta`
   near `y = (|rho(1-rho)|/2)^(1/(beta-theta))`, and from that onset to the
   power 2/3 on, every window `[Y, Y^(3/2)]` in reach contains a violation. At
   the verified height `gamma0 = 3 * 10^12` the earliest such onset is near
   `10^49.3` (closed form, not a measurement).
6. **Rivals.** For Davenport-Heilbronn and for the Epstein zeta function of
   the form (1,1,6), the coefficients of `-f'/f` are not supported on prime
   powers, and the same smoothed sum grows with the exponent of the off-line
   zero this lab already has on record (measured 0.808 against 0.80852, and
   0.954 against 0.95326). Both fail hypotheses of the interface. That excludes
   nothing about the posted proof.
7. **Literature.** The identity for `G` is Lemma 2.2 of Ramare (2013) up to
   rearrangement. It is original here in the sense of provenance and it is not
   novel. The author's PDF, as fetched, prints the zero sum with the opposite
   sign and a different bounded term; the form above is the one that passes the
   measured defect.

## 1. Transcription

All paths are relative to `lean/src`. The archive states (Lean text, verbatim
in `transcription.json`):

| object | path:line | plain mathematics |
| --- | --- | --- |
| `Sz`, `Gz` | `Formalism/StatementOC.lean:11-13` | `G(y) = sum_{n<=y} Lambda(n)(y/n - 1) - y log y + (1 + gamma) y` |
| `gChi` | `.../TotientGaloisClasses/Analytic.lean:11-24` | `Gchi(y) = sum_{n<=y} Lambda(n) chi(n)(y/n - 1) + y L'/L(1, chi)` for `chi != 1` |
| `wt`, `Gm` | `.../TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:32-38` | `Gm = Gz + sum over nontrivial kept psi of wt(psi) Re gChi(psi)`, `wt = (3o+1)^-1` when `psK = none` |
| `Level.ofSub`, `Level.cyc` | same file, 105-121 | kept set: primitive inducers of the powers of `psi`; `psK = none`; `o` the order of `psi` |
| `CharFamily`, `Gm`, `ZeroFree` | `Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean:24-39` | finite family, positive weights, each member trivial of level 1 or nontrivial |
| `zeroFree_of_rpow_window` | `.../DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:11-14` | windows `[Y, Y^(1+delta)]` with `Gm <= C y^theta` for arbitrarily large `Y` give zero-freeness for `Re s > theta` |
| top call | `Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:10`, `.../PrimitiveCosets/Imports.lean:13` | `la = 3/2`, `delta = la - 1`, `C = 1` |
| bound asked for | `.../TotientGaloisClasses/TopWin.lean:26-28` | `Gm(x) <= x^(1/2 + (eD + eL + 7) eps)` on the family's windows |

Three points a reader might get wrong, checked against the text:

- `Formalism/StatementOC.lean:20-21` defines a real-valued `Gchi` (real parts
  taken inside); the live chain uses the complex `An.gChi` and takes the real
  part in `Gm`. For `Gm` these agree.
- `Level.ofSub` builds its kept set as a `Finset` image under `PChar.of`, so an
  imprimitive power of `psi` is replaced by the primitive character inducing it
  and counted once. For `psi` of conductor 16 and order 4 the level holds two
  characters of conductor 16 and one of conductor 8
  (`test_cyc_level_weights_are_three_or_four_over_3o_plus_1`).
- With these weights, `1 + (3o+1)^-1 sum_{k=1}^{o-1} psi^k(n)` equals
  `o (3 + [psi(n) = 1])/(3o + 1)` on integers prime to the conductor: classes
  in the kernel of `psi` weigh 4, the others 3. Exact, tested.

## 2. Instruments

`instrument.py` has two routes that share no arithmetic.

- **Float route.** With `E(n) = sum_{m<=n} Lambda(m)/m - log n + gamma` and
  `R(n) = psi(n) - n`, for `n <= y < n+1`:
  `G(y) = y E(n) - y log(y/n) + (y - n) - R(n)`, so `G(n) = n E(n) - R(n)`.
  The large cancelling terms never appear. Increments in float64, running sums
  in extended precision.
- **Arb route.** One pass over the primes with `psi` and
  `A = sum Lambda(m)/m` accumulated in 128-bit balls, snapshots at the
  requested points, higher prime powers added per point. A float `y` is read as
  the exact dyadic rational it is.

They agree to 4.0e-12 in `F` at every decade extreme up to 10^9, the gap
growing with `y` as float rounding does. Characters are stored as exact
exponents read from python-flint's Conrey labels; multiplicativity and
orthogonality are tested, not assumed.

`L'/L(1, chi)` for the 79 primitive characters of conductor at most 20
(`lseries.json`): route A is Arb's Taylor jet of `L(s, chi)` at `s = 1`, route
B is Arb's generalized Stieltjes constants of the Hurwitz zeta function, route
C is mpmath's Stieltjes constants at 30 digits. A and B overlap for every
character, worst distance 4.9e-36; A and C differ by at most 1.1e-38. Example:
`L'/L(1, chi_-3) = 0.368281615970148`. Grade: hardened.

## 3. The explicit formula for G

**Statement (derivation).** For `y >= 1`,

    G(y) = sum_rho y^rho / (rho (1 - rho)) + log(2 pi) + T(y),
    T(y) = (y/2) int_y^infty log(1 - t^-2) t^-2 dt
         = -sum_{k>=1} y^(-2k) / (2k (2k+1))
         = (1/2) log(1 - y^-2) + (y/2) log((y+1)/(y-1)) - 1      (y > 1),

with `T(1) = log 2 - 1`, the sum over nontrivial zeros with multiplicity.

**Derivation.** `sum_{n<=y} Lambda(n)(y/n - 1) = y int_1^y psi(t) t^-2 dt`, and
`int_1^infty (psi(t) - t) t^-2 dt = -1 - gamma`, so
`G(y) = -y int_y^infty (psi(t) - t) t^-2 dt`. Insert
`psi(t) - t = -sum_rho t^rho/rho - log(2 pi) - (1/2) log(1 - t^-2)` and
integrate term by term. Assumptions: the classical explicit formula for `psi`,
absolute convergence of `sum 1/|rho(1-rho)|`, and the interchange of sum and
integral (Ramare's Lemma 2.1 does this step). Review status: not independently
reviewed; calibrated numerically below. The same formula follows from the
Mellin identity the archive states at
`.../LandauTheorems/mellinGchiOfNeOne.lean:116-119` and its zeta analogue.

**Consequences (derivation).** At `y = 1` the formula reads
`sum_rho 1/(rho(1-rho)) = 2 + gamma - log(4 pi) = c0`. Under RH each term is
`1/|rho|^2 > 0`, so for every `y >= 1`

    |G(y) - log(2 pi) - T(y)| <= c0 sqrt(y),

with equality on the upper side at `y = 1`. Conversely, by Landau's theorem
(classical, quoted, and stated by the archive as `ZetaLandau` at
`Formalism/StatementU.lean:14-17`), `G(y) <= C y^(1/2)` for all large `y`
forces every zero onto the line. So RH is equivalent to the single inequality
`G(y) <= c0 sqrt(y) + log(2 pi) + T(y)` for all `y >= 1`. This is a
restatement of RH in the archive's units. It is not progress on RH.

**Calibration (`zeros.json`, `explicit_zeta.json`).**

- Zeros: the first 20000 ordinates from Arb (`acb.zeta_zeros`, 64 bits, largest
  ball radius 1.8e-15), up to height 18046.464. The first 1000 equal the lab's
  `data/zeros_1000.json` to float precision.
- The constant: `c0` minus the partial sum of `2/(1/4 + gamma^2)` is the total
  weight of the unlisted zeros. With 20000 zeros it is 1.580858e-04. The
  density of zeros predicts `(log(T/2pi) + 1)/(pi T) = 1.580895e-04`. The two
  agree to 2.3e-5 relative, at every rung of the ladder to better than 0.2
  percent. That is the calibration of `c0`: measured.
- The identity: prime side by the Arb route at 256 points, `1 <= y < 10^8`
  (17 fixed, the rest log-uniform dyadics, seed 161). The budget is
  `(c0 - partial sum) sqrt(y)`: exact if the unlisted zeros are on the line.

| zeros used | tail budget / sqrt(y) | max over y > 1 of abs(defect) / budget | max over y > 1 of abs(defect) / sqrt(y) |
| --- | --- | --- | --- |
| 100 | 6.22e-03 | 0.160 | 9.95e-04 |
| 1000 | 1.44e-03 | 0.114 | 1.64e-04 |
| 5000 | 4.54e-04 | 0.095 | 4.31e-05 |
| 20000 | 1.58e-04 | 0.082 | 1.30e-05 |

  At `y = 1` the ratio is 1 to 12 digits, as it must be: every phase is
  aligned there.
- Hardened spot checks: at `y = 2.5, 100.5, 10007.25, 1000003.5`, with 2000
  zeros, the prime side, the truncated zero side and the budget are all Arb
  balls at 128 bits and Arb decides `|defect| <= budget`. At `y = 1` the two
  balls overlap (equality).

The budget assumes the unlisted zeros are on the line. That is known up to
height 3 * 10^12 (Platt and Trudgian 2021, quoted, not recomputed); above that
height the total weight is about 3e-12 and is irrelevant at these `y`.

**Planted faults (`test_planted_faults_in_the_explicit_formula_go_red`).** The
defect test fails on each of: the zero sum with the opposite sign, `T`
dropped, `gamma` off by 1e-3, one zero removed from the list while the budget
is computed from the full list, and `c0` off by 1e-4.

## 4. The RH envelope, measured

`scan_1e9.json` holds `F(n)` extremes for every integer `2 <= n <= 10^9` in ten
bins per decade (float route, 130.1 s on one core).
`scan_1e9_enclosed.json` holds the Arb values at the per-decade extremes (128
bits, repeated at 192 bits with identical digits).

How the integer scan controls real `y` (derivation). Between consecutive prime
powers `G'' = -1/y`, so `F` is concave there once `y` is past the first few
integers: a minimum over real `y` sits at a prime power, and a maximum sits at
an interior critical point whose value exceeds the larger neighbouring
integer value by at most about `1/(8 n^(3/2))`. The critical point is solved in closed form and polished; Arb
evaluates `F` and `F'` there.

| decade | min at n | F min | F min / c0 | max at y | F max | F max / c0 |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 3 | -0.0209708631 | -0.4540 | 5.9344 | 0.0135767618 | 0.2939 |
| 1 | 17 | -0.0173979402 | -0.3766 | 34.4893 | 0.0164080988 | 0.3552 |
| 2 | 103 | -0.0193452531 | -0.4188 | 208.1148 | 0.0181721197 | 0.3934 |
| 3 | 9413 | -0.0158822397 | -0.3438 | 3099.7135 | 0.0186745678 | 0.4043 |
| 4 | 56519 | -0.0174332116 | -0.3774 | 11016.0087 | 0.0165428516 | 0.3581 |
| 5 | 319439 | -0.0226812405 | -0.4910 | 164922.3234 | 0.0181348957 | 0.3926 |
| 6 | 6862369 | -0.0175305938 | -0.3795 | 5604380.3014 | 0.0183689995 | 0.3977 |
| 7 | 39226493 | -0.0185062428 | -0.4006 | 34186454.4254 | 0.0246942451 | 0.5346 |
| 8 | 169371133 | -0.0170570072 | -0.3693 | 502867944.9468 | 0.0217427010 | 0.4707 |

Decade `k` is `[10^k, 10^(k+1))`, decade 0 starting at 2. The extremes:

- maximum over `2 <= y <= 10^9`:
  `F = [0.02469424507803455263976536 +/- 1.31e-27]` at
  `y = 34186454.425380` (float `0x1.04d26b3672d7dp+25`), where Arb gives
  `F' = [-4.97e-21 +/- 1.3e-29]`. The integer next to it is 34186454.
- minimum: `F = [-0.02268124049589207899539318 +/- 1.72e-27]` at the prime
  319439.
- `c0 = 0.0461914179322420676...`. Arb decides `-c0 < F < c0` at both points.

So in the scanned range the normalised quantity uses 53 percent of the room RH
allows above and 49 percent below. That the scan stays inside the envelope is
what RH below known verified heights requires; a value outside would have been
a bug. The scan itself is float grade and is not a finite-range theorem: the
signs at the integers are float signs.

The archive's own form, `G(y) <= y^theta` with `C = 1`: the last integer with
`G(n) > sqrt(n)` is `n = 3`. From `n = 4` to `10^9` the scan has
`G(n) < sqrt(n)`, and the supremum of `G(n)/sqrt(n)` over `n >= 100` is 0.18022
at `n = 118`. Under RH this is automatic for `y >= 4`, because `c0 < 1`.

## 5. Characters

**Formulas (derivation, same assumptions as section 3, for a primitive `chi`
mod `q > 1`).** The Mellin transform of `Gchi` is
`(-L'/L(s) + s L'/L(1)) / (s(s-1))`. It is regular at `s = 1`, has residue
`y^rho/(rho(1-rho))` at each nontrivial zero, and at `s = 0` and the trivial
zeros it depends on the parity:

    odd:   Gchi(y) = sum_rho y^rho/(rho(1-rho)) + L'/L(0, chi) + T_odd(y)
    even:  Gchi(y) = sum_rho y^rho/(rho(1-rho)) + log y + 1 + b(chi) + T(y)

with `T_odd(y) = -sum_{k>=1} y^-(2k-1)/((2k-1) 2k)`, `T_odd(1) = -log 2`, and
`b(chi) = lim_{s->0} (L'/L(s, chi) - 1/s)`. The even case carries a `log y`
because `s = 0` is then a double pole. From the functional equation, with
`a = 0` for even and `a = 1` for odd,

    c_chi = sum_rho 1/(rho(1-rho)) = 2 Re L'/L(1, chi) + log(q/pi) + digamma((1+a)/2),
    L'/L(0, chi) = -conj(L'/L(1, chi)) - log(q/pi) + gamma + log 2        (odd),
    b(chi)       = -conj(L'/L(1, chi)) - log(q/pi) + gamma + log 2        (even).

Under GRH, `|Gchi(y) - (non-oscillating part)| <= c_chi sqrt(y)` for `y >= 1`.

**Calibration.**

- The `s = 0` constants were also computed directly at `s = 0` from Arb's
  Taylor jet, without the functional equation. Direct and derived overlap for
  all 79 characters (worst distance 2.7e-37). Hardened.
- `explicit_chi.json`: for each of the 26 primitive characters of conductor at
  most 12, zeros with `|gamma| <= 80` from sign changes of the Hardy Z function
  (2396 zeros in all), prime side in float64 at 60 points up to 10^6. The
  defect is at most 0.132 of the budget `(c_chi - partial sum) sqrt(y)`. Every
  budget is positive and within 0.7 percent of the density prediction, which
  is the check that no zero was missed and that `c_chi` is right. Measured.
- Planted faults: the formula of the other parity fails for both test
  characters, and so does `L'/L(1)` off by 1e-3.

**Levels (`levels_q20_y7.json`, `levels_q30_y6.json`).** For `Level.cyc psi`
with `psi` of order `o`, the envelope is `|Gm(y) - M(y)| <= C sqrt(y)` with
`C = c0 + (3o+1)^-1 sum_k c_k` and `M` assembled from the constants above. The
identity `Gm(1) - M(1) = C` holds in Arb for every level.

- Conductor at most 20, `2 <= n <= 10^7`: 79 primitive characters generate 35
  distinct levels. The worst ratio `|Gm - M| / (C sqrt(n))` is 0.7180, for
  the quadratic character mod 19, at `n = 1855747`; Arb gives -0.718010359487
  there and decides it is below 1 in absolute value. The largest `C` is 0.3756
  (the full group mod 19). The supremum of `Gm(n)/sqrt(n)` over `n >= 100`,
  across levels, is 0.4074, and no level has `Gm(n) > sqrt(n)` beyond `n = 6`.
- Conductor at most 30, `n <= 10^6`: 167 characters, 56 levels, worst level
  ratio 0.6983.
- Character by character (no dilution by the weights): worst ratio 0.9463
  over `n >= 2`, 0.9423 over `n >= 100`, both for `chi_19(3, .)` and its
  conjugate. The instrument was not wrong: that L-function has a zero at
  `1/2 - 0.0190 i`, which alone contributes 0.917 of `c_chi = 4.3578`, so
  `Re Gchi` rides near the top of its envelope for seven decades. The same
  happens more mildly for `chi_17(5, .)` (zero at height -0.391).

Measured throughout; the three worst level points are hardened.

## 6. Lesion

`lesion.json`. A quadruple `beta +- i gamma0`, `1 - beta +- i gamma0` is added
to `G` through the formula of section 3. This is a model computation on the
zero side. It is not a proof of the windowed lemma, and it says nothing about
whether the archive's proof of that lemma is sound.

Grid: `beta` in {0.6, 0.75, 0.9, 1}, `gamma0` in {10, 30, 100, 1000}, three
`theta` per `beta` (48 cases). Base `G`: the prime side on the integers up to
10^7, and the truncated zero side (2000 zeros) on a log grid up to 10^30.

- Control: with no lesion neither detector fires, on the prime side or on the
  model.
- The detector sees the plant. Example `beta = 1`, `gamma0 = 30`: the envelope
  `|F| <= c0` is first broken at `n = 388`, and `G(n) > sqrt(n)` first at
  `n = 229536`. In the 6 cases where the prime side reaches the first
  violation of `G <= y^theta`, the model puts it at the same place to within
  0.02 percent.
- Onset law: in 25 of the 48 cases the first violation lies below 10^30. In
  all of them it is between 0.98 and 1.61 times
  `(|rho(1-rho)|/2)^(1/(beta-theta))`.
- Windows: in every one of those 25 cases, each window `[Y, Y^(3/2)]` with
  `Y >= onset^(2/3)` in reach contains a violation, and no window that ends
  before the onset does. After the onset the gaps between violations are
  at most two periods `2 pi/gamma0` in `log y`.

What this says about teeth. The criterion does respond to an off-line zero, in
every window, but only from `Y` near `onset^(2/3)`. By the closed form (not a
measurement), a quadruple at the verified height `gamma0 = 3 * 10^12` with
`beta = 1` first breaks `G <= sqrt(y)` at `y` near `10^49.3`, and first breaks
the envelope at `10^46.6`; with `beta` closer to 1/2 the onset is later
without bound. Conversely the scan of section 4 could only have seen a
quadruple with `gamma0` below about 1170 (`beta = 1`) or about 18.5
(`beta = 0.6`), all long excluded. The scan tests the transcription and the
instrument. It does not test RH beyond what is known.

## 7. Rivals

`rivals.json`, `n <= 10^7`, float grade. `Lambda_f` is defined by
`a_n log n = sum_{d|n} Lambda_f(d) a_{n/d}`. The recursion returns the von
Mangoldt function for zeta to 1.2e-14 and agrees with the lab's mpmath recursion
for Davenport-Heilbronn to 1.1e-15 on `n <= 240`.

| | zeta (control) | Davenport-Heilbronn | Epstein (1,1,6), D = -23, h = 3 |
| --- | --- | --- | --- |
| nonzero `Lambda_f(n)`, `n <= 10^7` | 665134 | 2843565 | 998154 |
| of those, off the prime powers | 0 | 2178445 | 887075 |
| negative | 0 | 1421777 | 271001 |
| first off a prime power | none | `Lambda_f(6) = (1 + kappa^2) log 6` | `Lambda_f(6) = 2 log 6` |
| slope of `log sum_{n<=x} abs(Lambda_f)`, last decade | 1.0001 | 1.1195 | 1.1436 |
| off-line zero on record | none | 0.80852 + 85.69935 i | 0.95326 + 16.29022 i |
| exponent at that ordinate, per decade step | 0.485, 0.505, 0.491, 0.510 (at gamma_1) | 0.806, 0.808, 0.808 | 0.943, 0.955, 0.954 |

The smoothed sums are `G_f(y) = sum Lambda_f(n)(y/n - 1) + y f'/f(1)` for
Davenport-Heilbronn (`f'/f(1) = 0.153889965968`, mpmath and python-flint
agree) and `sum Lambda_f(n)(y/n - 1) - y log y + (1 + g0) y` for the Epstein
function (`g0 = 0.530027482627`, finite differences on the lab's `epstein_zeta`
against the Kronecker limit formula, agreeing to 2e-25).

The exponent row is a demodulation: `G_f(n) n^(-i gamma)` averaged over each
decade with a Hann window in `log n`, whose size scales by exactly `10^beta`
per decade if `G_f` contains `c n^(beta + i gamma)`. For
Davenport-Heilbronn the 64 on-line zeros below height 120 were subtracted
first. The recovered amplitude matches the residue `1/|rho(1-rho)|` to 0.01
percent (Davenport-Heilbronn) and 0.2 percent (Epstein). Eight units away in
`gamma` the amplitude is 69 and 34 times smaller, so the measurement is of
that zero and not of the window.

The Davenport-Heilbronn slope 1.1195 sits next to the abscissa 1.12036 this
lab records for its rightmost zeros (`docs/29`). A finite-range slope is not an
abscissa; it is recorded as consistent.

**The interface inequality on the rivals.** For the Epstein function,
`G_f(n) > n^0.55` first at `n = 22132` and `G_f(n) > n^0.6` first at
`n = 1025840`, where the onset law of section 6 predicts 1026448. The last
window `[Y, Y^(3/2)]` without a violation of the 0.6 bound starts at
`Y = 10171`, which is `1025840^(2/3)`. For `theta = 0.75` nothing happens
below 10^7 (predicted onset 2.8 * 10^10). For Davenport-Heilbronn nothing
happens below 10^7 for any `theta >= 1/2`: the predicted onset at
`theta = 0.6` is 1.2e+17. Zeta through the same code path: no violation.

**Which hypothesis each rival fails.**

- *Type and arithmetic.* The windowed statement is typed to finite families of
  Dirichlet characters, and its Mellin step uses
  `-L'/L = sum Lambda(n) chi(n) n^-s`. For both rivals `Lambda_f` is not of
  the form `Lambda(n) chi(n)`: it is nonzero at 6, takes both signs, and is not
  bounded by a multiple of `Lambda`.
- *Positive combination.* `Gm` is a positive combination of the `G` of
  L-functions, which is the `G` of a product of positive powers of
  L-functions. Both rivals are linear combinations of L-functions with Euler
  products, not factors of such a product.
- *Nonvanishing on `Re s >= 1`.* Both have zeros with `Re s > 1` (Davenport
  and Heilbronn 1936, quoted, not recomputed), so `sum Lambda_f(n) n^-s`
  cannot represent `-f'/f` on all of `Re s > 1`. The measured slopes above 1
  are the visible trace.
- *The bound itself.* The Epstein function violates `G_f <= y^theta` inside
  the range computed; Davenport-Heilbronn is predicted to, far outside it.

Reading. The window criterion is a shared lemma: applied to a rival it reports
the rival's off-line zero, as it should. A rival that fails a hypothesis
excludes nothing about the posted proof. The step that would distinguish, the
upper bound for `Gm` produced from Frobenius classes of an abelian CM field,
cannot be formulated for either rival and was not examined here. The third
battery rival, the shifted product `zeta(s+a) zeta(s-a)`, was not computed: its
log-derivative coefficients are `Lambda(n)(n^a + n^-a)`, a twist that is not a
Dirichlet character, and its pole is at `1 + a`, so it fails the type and the
normalization (derivation only).

## 8. Decoy

`decoy.json`. Each integer `n >= 3` is kept independently with probability
`1/log n` and weighted `log n` (eight seeds, `n <= 10^6`). Over `n >= 100`
the smallest value of `sup |F|` across seeds is 208, and after refitting the
best linear term it is 40.8, against 0.0227 for the primes and
`c0 = 0.0462`. At most 0.19 of the integers stay inside the envelope after the
refit. A density-matched set with no arithmetic misses the envelope by a factor
near 900. Measured.

## Literature

Searches run on 2026-11-20, generic mathematical queries only (web search):
(1) the kernel `x^rho/(rho(1-rho))` with the weight `Lambda(n)(x/n - 1)`;
(2) the constant `2 + gamma - log 4 pi` with `sum 1/|rho|^2`; (3) the sum
`sum Lambda(n)(1/n - 1/x)`; (4) explicit estimates for `sum Lambda(n)/n`;
(5) the tail integral of `(psi(t) - t)/t^2` as an RH equivalent; (6) localized
oscillation theorems of Pintz type.

Found:

- **The identity.** O. Ramare, "Explicit estimates for the summatory function
  of Lambda(n)/n from the one of Lambda(n)", Acta Arith. 159 (2013), 113-122,
  Lemma 2.2: `sum_{n<=x} Lambda(n)/n = log x - gamma + (psi(x) - x)/x` plus a
  sum over zeros of `x^(rho-1)/(rho(rho-1))` plus `B(x)/x`, proved by the same
  integration of the explicit formula. Multiplying by `x` gives the identity
  of section 3. In the author's PDF as fetched (the journal version was not
  consulted) the zero sum carries a plus sign and
  `B(x) = 1/2 + log 2pi - ((x-1)/2) log(1 - 1/x)`. The calibrated form has
  `sum x^(rho-1)/(rho(1-rho))` and `B(x) = log 2pi + T(x)`,
  `T(x) = ((x+1)/2) log(1 + 1/x) - ((x-1)/2) log(1 - 1/x) - 1`. At `x = 1` the
  printed form gives `B(1) = 2.338` where the identity needs `log 4pi - 1 =
  1.531`; the planted-fault test with the printed sign goes red. This does not
  touch Ramare's theorems, which bound these terms in absolute value.
- **The constant.** `sum 1/(rho(1-rho)) = 2 + gamma - log 4 pi` is classical;
  search summaries report it in arXiv 2311.09464, the value 0.0461914 in
  arXiv 1410.7036, and the statement that RH holds exactly when
  `sum 1/|rho|^2` equals it. Not read in full.
- **Neighbours.** The bound `|psi_1(x) - x^2/2| <= x^(3/2) sum 1/|rho(rho+1)|`
  under RH (Ingham; used in arXiv 2311.09464), and a bound by
  `sum |rho|^-2` for a related integral in arXiv 2411.07436.
- **Localized oscillation.** Pintz's theorems (a zero `rho0` forces a large
  value of the remainder in every `[X^(1/4), X]`), and arXiv 1912.00853.
  These are two-sided or for `psi` itself.

Not found in these searches: the inequality `|G(y) - log 2pi - T(y)| <= c0
sqrt(y)` stated as such, the one-inequality equivalence with the sharp
constant attained at `y = 1`, or a one-sided windowed Landau statement for
this smoothed sum. Claim made: the formula and the bound are original to this
lab in the sense of provenance, they are a one-line consequence of a published
lemma, and no novelty is claimed. Six searches are not a literature review.

## Standing checklist

1. **Rival.** Section 7. The claim "the interface inequality holds" is not
   shared by the rivals: the Epstein function violates it in reach, and
   Davenport-Heilbronn fails its hypotheses. The test set is not the rival
   set: the envelope was measured on zeta and 167 Dirichlet characters, the
   rivals are the standing battery, and the rival zeros used are ones this lab
   recorded before this hunt. What the rivals share with zeta is the window
   criterion as a function-agnostic lemma, and that was said, not hidden.
2. **Decoy.** Section 8. A Cramer set of the same density misses the envelope
   by a factor near 900 after the best linear refit. The effect is not a
   consequence of density.
3. **Lesion.** Section 6 and the planted-fault tests. A planted quadruple is
   flagged where the closed form says, and it is told apart from the true
   signal: with no plant nothing fires in the same range. The detector cannot
   see a plant above height about 1170 in the scanned range, and that limit is
   reported as the scope of the measurement. One hazard this file names
   itself: a missing on-line zero in the list looks like a defect of the
   formula, and the test plants exactly that. The exact tail budget is the
   completeness check on the list.
4. **Precision response.** The identity's defect falls from 9.95e-04 to
   1.30e-05 (relative to `sqrt(y)`) as the zero list grows from 100 to 20000,
   tracking the budget. The extremal values are identical at 128 and 192 bits
   and agree with float64 to 4.0e-12. The envelope ratio does not move with
   precision, as a real quantity should not.

## Caveats

- The scan is float grade. Its signs are not rigorous and the range
  `2 <= y <= 10^9` is not covered by a theorem. Arb was used at 18 extremal
  points and at spot checks, not at every integer.
- The passage from integers to real `y` rests on the concavity argument of
  section 4, a derivation.
- The tail budgets assume the unlisted zeros are on the line. For the Dirichlet
  characters the zero lists come from sign changes, which is a lower bound on
  the count; the budgets match the density to 0.7 percent, which is a check and
  not a proof of completeness.
- The transcription is of text. Machine-generated names were not trusted;
  Mathlib's meaning of each symbol was assumed standard. No kernel was run.
- Whether the windowed statement is true as stated, whether its proof text is
  complete, and whether the upper bound for `Gm` is established anywhere in the
  archive, are outside this hunt.
- The Epstein off-line zero is this lab's 20-digit measurement.
- The first lesion run let the BLAS library use more than one core for about
  half a minute; later runs were pinned to one thread (`RUNS.md`).
- `tests/test_hunt_probe_discipline.py::test_every_hunt_directory_is_covered_by_the_case_log`
  fails until the case-log entry returned with this hunt is placed in
  `hunts/README.md`, which this hunt may not edit.

## The doors

This hunt measures a supremum, so it owes the three lists.

1. **Active constraints at the optimum.** Under RH the supremum of `F` over
   `y >= 1` is `c0` exactly and is attained at `y = 1`, where every phase
   `gamma log y` vanishes. Away from 1 what binds is simultaneous alignment of
   the low zeros: the first zero alone carries 21.6 percent of `c0`. The
   per-decade maxima (0.29, 0.36, 0.39, 0.40, 0.36, 0.39, 0.40, 0.53, 0.47 of
   `c0`) show no trend over nine decades, so the saturation curve is flat in
   the range and the measured 0.5346 is a property of the range, not a limit.
   For the reach of the criterion the binding constraint is the height of the
   lowest unverified zero: the onset `(|rho(1-rho)|/2)^(1/(beta-theta))`
   grows like the square of that height or faster.
2. **The frozen-constant inventory.**
   - Window exponent 3/2 and `C = 1`: the archive's. *Genuine trade shape*: a
     window `[Y, Y^la]` sees a violation from `Y = onset^(1/la)`, so a larger
     `la` asks more of the upper bound and gives teeth earlier.
   - Weights `(3o+1)^-1`: the archive's. They dilute the characters, which is
     why level ratios (0.7180) sit below character ratios (0.9463).
   - 20000 zeros, 64-bit: tail budget 1.58e-4. *Trade*: cost is linear in the
     count, budget falls like `log T / T`.
   - `y <= 10^9` for zeta, `10^7` for conductor at most 20, `10^6` up to 30:
     chosen by the one-core budget. *Trade*: about 130 s per factor 10 for
     zeta, about 95 s per 10^7 for 114 character combinations.
   - L-function zeros to height 80 on a 0.04 grid; 2000 zeros in the lesion
     base; lesion grid of 16 points; 8 decoy seeds; Hann decade windows;
     128-bit Arb. None of these was optimized.
3. **The information class.** Everything here reads primes below 10^9 and
   zeros below height 18046 (zeta) or 80 (characters): the same data every
   existing verification reads. No door inside this class leads to the
   question that matters, which is whether the archive's upper bound for `Gm`
   holds for the reasons it states. That door reads different information: the
   kernel replay, and the arithmetic side (prime-power sums by Frobenius class
   bounded through a slope inequality), which this hunt did not open.

Proof status of the optimum: the value `c0` at `y = 1` is a derivation
calibrated to 30 digits by Arb; the range maximum 0.5346 of `c0` is a float
scan with Arb values at the located points; neither is a proved ceiling, and
the first is conditional on RH for `y > 1`.
