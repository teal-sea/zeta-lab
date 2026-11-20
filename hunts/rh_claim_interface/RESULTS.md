# RESULTS: the interface inequality of a posted RH claim, measured (hunt #161)

Status: **measured, with Arb enclosures at the extremal points and at spot
checks; the identity for `G` is a published lemma (corrected in print in 2023),
recalibrated here at float grade; no claim promoted.** Nothing here evaluates
the posted proof. Nothing here is evidence for RH. A finite computation is
never a uniform RH result.

**Revised on 2026-11-20 after two independent reviews.** Both returned "holds"
for the headline, with twelve findings: one major, eleven minor. All twelve
were reproduced and none was rejected. What changed, heaviest first:

1. *Literature (major).* The identity for `G` is, sign for sign, Lemma 2.1 of
   Ramare's 2023 corrigendum. The first version missed the corrigendum, cited
   the misprinted 2013 lemma "up to rearrangement" and presented the sign as
   something its own defect test had found. Corrected: zero delta, and the
   2013 Theorem 1.1 is now stated as the unconditional frontier.
2. *Teeth, downgraded.* The onsets `10^49.3` and `10^46.6` are a model of one
   planted quadruple. What is known without RH guarantees `G(y) <= sqrt(y)`
   only up to about `10^23`.
3. *Grades, downgraded.* The sharp calibration of the identity is float grade;
   Arb decides only a coarse inequality at 4 points. Three statements at
   `y = 1` were arithmetic of constants, not calibration, and are now labelled
   so. "Calibrated to 30 digits by Arb" is withdrawn.
4. *Enclosures, repaired.* The maxima had been enclosed at 128 bits only while
   the text said 128 and 192. The stage was rerun: every extreme at both.
5. *Rivals, completed.* The battery has four rivals, not three. Epstein
   (2,1,3) is recorded as undefined for this claim, all three Epstein onsets
   are printed with their predictions, and the inequality is said not to
   separate zeta from Davenport-Heilbronn in reach.
6. *Transcription, corrected.* One gloss confused the exponent of the supplied
   bound with the `theta` of the windowed statement. Seven quotes were added.
7. *Tests, repaired.* The pins were substring checks that ten wrong numbers
   passed, and no test ran the Arb zero side. Both are fixed and shown red.

The record of each finding, with evidence, is the section "Review findings and
dispositions". Wrong statements of the first version are quoted there and at
the point of correction, not erased.

Reading guide to the rungs used below. *Text*: read off the archive, no kernel.
*Published*: read in a cited source, not re-proved here. *Derivation*: ordinary
pencil derivation, assumptions stated, not independently reviewed. *Measured*:
one route, float grade. *Hardened*: independent routes agree and Arb enclosures
carry every step of the number in question.

## 0. What was found

1. **Transcription (text).** The definitions of `Gz`, `gChi`, `Level.Gm`,
   `Level.cyc` and the windowed statement are as the two readers reported.
   Quotes with path, line and file hash are in `transcription.json`; the joined
   tarball has sha256
   `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
   The archive states the windowed statement; whether its proof text is sound
   was not examined.
2. **The explicit formula is a published lemma, recalibrated here (measured).**
   For `y >= 1`, `G(y) = sum_rho y^rho/(rho(1-rho)) + log(2 pi) + T(y)`. This is
   Ramare's corrected Lemma 2.1 (2023) multiplied by `y`. With 20000
   Arb-isolated zeros the prime side and the zero side differ by at most 0.082
   of the exact tail budget at the 255 grid points with
   `1 < y <= 9.8 * 10^7`. Arb decides only the coarser inequality
   `|defect| <= budget` with 2000 zeros at 4 points.
3. **The RH envelope, measured.** `F(y) = (G(y) - log 2pi - T(y))/sqrt(y)`
   equals `c0 = 2 + gamma - log(4 pi) = 0.0461914179...` at `y = 1`, which is
   arithmetic of constants (`G(1) = 1 + gamma` by an empty sum) and involves no
   zero. Over `2 <= y <= 10^9` its maximum is 0.0246942450780346
   (0.5346 of `c0`) at `y = 34186454.425380` and its minimum is
   -0.0226812404958921 (-0.4910 of `c0`) at the prime `y = 319439`. Scan:
   measured. The two values at those two points: hardened (Arb at 128 and at
   192 bits). Without RH, known facts already force `|F(y)| <= c0 + 4.7e-08`
   on this range (section 6), so the scan could not have come out otherwise.
4. **Characters.** The character formulas (even and odd differ) calibrate for
   all 26 primitive characters of conductor at most 12. For all 35 levels
   `Level.cyc psi` with conductor at most 20, `Gm` stays within 0.7180 of the
   GRH envelope at the integers `2 <= n <= 10^7`. A single character reaches
   0.9463 of its envelope, and the reason is a zero of `L(s, chi_19(3, .))` at
   height -0.0190.
5. **Where the criterion can have teeth.** A single planted quadruple
   `beta +- i gamma0`, `1 - beta +- i gamma0` first violates `G(y) <= y^theta`
   near `y = (|rho(1-rho)|/2)^(1/(beta-theta))`, and from that onset to the
   power 2/3 on, every window `[Y, Y^(3/2)]` in reach contains a violation. At
   the verified height `gamma0 = 3 * 10^12` a single quadruple with `beta = 1`
   has its onset near `10^49.3` (closed form for one quadruple, not a
   measurement and not the frontier of what is known). Known facts guarantee
   `G(y) <= sqrt(y)` only up to about `10^23`: 8.2 * 10^22 from a published
   theorem, 4.2 * 10^23 from the bound of section 6. Between about `10^23` and
   `10^49` nothing here excludes a violation made by many zeros together.
6. **Rivals.** For Davenport-Heilbronn and for the Epstein zeta function of
   the form (1,1,6), the coefficients of `-f'/f` are not supported on prime
   powers, and the same smoothed sum grows with the exponent of the off-line
   zero this lab already has on record (measured 0.808 against 0.80852, and
   0.954 against 0.95326). Both fail the type of the interface, and so does
   the shifted product. The Epstein form (2,1,3) is undefined for this claim
   and was not tested. Within reach the inequality itself does not separate
   zeta from Davenport-Heilbronn. None of this excludes anything about the
   posted proof.
7. **Literature.** The identity for `G` is Lemma 2.1 of O. Ramare's
   corrigendum (Acta Arith. 211 (2023), 93-96) multiplied by `y`: zero delta.
   It was rederived here before that source was found, so it is original in
   the sense of provenance only, and it is not novel. Theorem 1.1 of the 2013
   paper already gives `|G(x)| <= sqrt(x)/2 + 1.75e-12 x` for `x >= 8950`
   without RH.

## 1. Transcription

All paths are relative to `lean/src`. The archive states (Lean text, verbatim
in `transcription.json`):

| object | path:line | plain mathematics |
| --- | --- | --- |
| `Sz`, `Gz` | `Formalism/StatementOC.lean:11-13` | `G(y) = sum_{n<=y} Lambda(n)(y/n - 1) - y log y + (1 + gamma) y` |
| `gChi` | `.../TotientGaloisClasses/Analytic.lean:11-24` | `Gchi(y) = sum_{n<=y} Lambda(n) chi(n)(y/n - 1) + y L'/L(1, chi)` for `chi != 1` |
| `wt`, `Gm` | `.../TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:32-38` | `Gm = Gz + sum over nontrivial kept psi of wt(psi) Re gChi(psi)`, `wt = (3o+1)^-1` when `psK = none` |
| `Level.ofSub`, `Level.cyc` | same file, 105-121 | kept set: primitive inducers of the powers of `psi`; `psK = none`; `o` the order of `psi` |
| `ramp`, `Deduction.Gchi` | `Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean:10-19` | the same sums over `n = 0..floor(y)` (`Lambda(0) = 0`), with the branch `chi = 1` giving `G` |
| `CharFamily`, `Gm`, `ZeroFree` | same file, 24-39 | finite family, positive weights, each member trivial of level 1 or nontrivial |
| `zeroFree_of_rpow_window` | `.../DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:11-14` | windows `[Y, Y^(1+delta)]` with `Gm <= C y^theta` for arbitrarily large `Y` give zero-freeness for `Re s > theta` (any real `C`, `0 < theta < 1`) |
| `Gz_eq`, `gChi_eq`, `level_family` | `Development/AutomorphicArithmetic/PrimitiveCosets/GzEq.lean:6-7`, `GChiEq.lean:16-17`, `LevelFamily.lean:41-42` | the archive states `Level.Gm = Deduction.Gm` of a family built from the level; statements quoted, proofs not examined |
| top call | `Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:10`, `.../PrimitiveCosets/Imports.lean:13` | `la = 3/2`, `delta = la - 1`, `C = 1` |
| `theta` at the top | `.../TotientGaloisClasses/TopWin.lean:68-81` | `theta = 1/2 + min(Re s - 1/2, 1/2)/2` for the point `s` to be excluded |
| bound supplied | `.../TotientGaloisClasses/TopWin.lean:26-28` | `Gm(x) <= x^(1/2 + (eD + eL + 7) eps)` on the family's windows, for real `eD`, `eL` with no sign condition |

Points a reader might get wrong, checked against the text:

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
- **Corrected in the review round.** The first version said the top uses
  "`theta = 1/2 + (eD + eL + 7) eps`". That expression is the exponent of the
  bound that is supplied. The `theta` handed to the windowed statement is
  `1/2 + min(Re s - 1/2, 1/2)/2`, after `eps` is chosen with
  `(eD + eL + 7) eps` at most half of that minimum (`level_of_tiedWin`).
- `eD` and `eL` are universally quantified reals in
  `ChebyshevInequalityOnWindows` and existentially quantified in
  `ChebyshevInequalityAtWindowScale`, with no sign condition in either, so the
  text does not force the supplied exponent to be at least 1/2.
- The windowed statement is about `Deduction.Gm`. The quantity scanned here is
  `Level.Gm`. The identification goes through three archive lemmas whose
  statements are quoted and whose proofs are unverified archive text. This
  hunt checked it by reading the definitions; a reviewer also evaluated
  `Level.Gm` from the Lean text at 6 points with mixed conductors and found
  agreement with `Gm_arb` to 1e-18 (reported, not rerun here).

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

**Statement (published; rederived here).** For `y >= 1`,

    G(y) = sum_rho y^rho / (rho (1 - rho)) + log(2 pi) + T(y),
    T(y) = (y/2) int_y^infty log(1 - t^-2) t^-2 dt
         = -sum_{k>=1} y^(-2k) / (2k (2k+1))
         = (1/2) log(1 - y^-2) + (y/2) log((y+1)/(y-1)) - 1      (y > 1),

with `T(1) = log 2 - 1`, the sum over nontrivial zeros with multiplicity. This
is Lemma 2.1 of Ramare's 2023 corrigendum multiplied by `y` (Literature).

**Derivation.** `sum_{n<=y} Lambda(n)(y/n - 1) = y int_1^y psi(t) t^-2 dt`, and
`int_1^infty (psi(t) - t) t^-2 dt = -1 - gamma`, so
`G(y) = -y int_y^infty (psi(t) - t) t^-2 dt`. Insert
`psi(t) - t = -sum_rho t^rho/rho - log(2 pi) - (1/2) log(1 - t^-2)` and
integrate term by term. Assumptions: the classical explicit formula for `psi`,
absolute convergence of `sum 1/|rho(1-rho)|`, and the interchange of sum and
integral. The interchange is the corrected explicit-formula lemma (Lemma 1.1
of the corrigendum, stated there for `2 <= a <= b`). The first version cited
Lemma 2.1 of the 2013 paper for this step; that printing has the sign of
`log 2pi` wrong. Review status: the statement is published; this derivation of
it was not independently reviewed; it is recalibrated numerically below. The
same formula follows from the Mellin identity the archive states at
`.../LandauTheorems/mellinGchiOfNeOne.lean:116-119` and its zeta analogue.

**Consequences (derivation).** At `y = 1` the formula reads
`sum_rho 1/(rho(1-rho)) = 2 + gamma - log(4 pi) = c0`, which is classical.
Under RH each term is `1/|rho|^2 > 0`, so for every `y >= 1`

    |G(y) - log(2 pi) - T(y)| <= c0 sqrt(y),

with equality on the upper side at `y = 1`. Conversely, by Landau's theorem
(classical, quoted, and stated by the archive as `ZetaLandau` at
`Formalism/StatementU.lean:14-17`), `G(y) <= C y^(1/2)` for all large `y`
forces every zero onto the line. So RH is equivalent to the single inequality
`G(y) <= c0 sqrt(y) + log(2 pi) + T(y)` for all `y >= 1`. This is a
restatement of RH in the archive's units. It is not progress on RH. Without RH
the same argument gives the bound of section 6, and the proof of Ramare's
Theorem 1.1 already contains it with 0.047 in place of `c0`.

**Calibration (`zeros.json`, `explicit_zeta.json`).**

- Zeros: the first 20000 ordinates from Arb (`acb.zeta_zeros`, 64 bits, largest
  ball radius 1.8e-15), up to height 18046.464. The first 1000 equal the lab's
  `data/zeros_1000.json` to float precision.
- The constant: `c0` minus the partial sum of `2/(1/4 + gamma^2)` is the total
  weight of the unlisted zeros. With 20000 zeros it is 1.580858e-04. The
  density of zeros predicts `(log(T/2pi) + 1)/(pi T) = 1.580895e-04`. The two
  agree to 2.3e-05 relative, which is 3.7e-09 absolute, and at every rung of
  the ladder to better than 0.2 percent. That comparison is the only evidence
  in this hunt that `c0` is the sum over the zeros. It is float grade and it
  leans on the leading term of the zero density. Measured.
- The identity: prime side by the Arb route at 256 points, `1 <= y < 10^8`
  (17 fixed, the rest log-uniform dyadics, seed 161; 10 of them in
  `1 < y < 2`). The budget is `(c0 - partial sum) sqrt(y)`: exact if the
  unlisted zeros are on the line.

| zeros used | tail budget / sqrt(y) | max over y > 1 of abs(defect) / budget | max over y > 1 of abs(defect) / sqrt(y) |
| --- | --- | --- | --- |
| 100 | 6.22e-03 | 0.160 | 9.95e-04 |
| 1000 | 1.44e-03 | 0.114 | 1.64e-04 |
| 5000 | 4.54e-04 | 0.095 | 4.31e-05 |
| 20000 | 1.58e-04 | 0.082 | 1.30e-05 |

  At `y = 1` the ratio is 1 for any zero list whatever:
  `defect(1) = (1 + gamma - log 2pi - T(1)) - partial sum = c0 - partial sum`,
  which is the budget. The first version reported this as "1 to 12 digits, as
  it must be" next to the calibration. It cannot fail and is evidence of
  nothing; the table excludes it. Away from 1 the sharpest point is
  `y = 1.25`, where the defect is 1.74e-08 in absolute value.
- Arb spot checks, and what they resolve: at
  `y = 2.5, 100.5, 10007.25, 1000003.5`, with 2000 zeros, the prime side, the
  truncated zero side and the budget are all Arb balls at 128 bits and Arb
  decides `|defect| <= budget`. The budgets there are 1.40e-03, 8.87e-03,
  8.85e-02 and 8.85e-01, which is 2510, 822, 97 and 205 times the defect. So
  this check resolves an error of the size of the budget and nothing smaller:
  a constant wrong by 1e-3 would pass at the last two points. What is
  enclosure-carrying is that coarse inequality. The sharp agreement in the
  table is float grade.

The budget assumes the unlisted zeros are on the line. That is known up to
height 3 * 10^12 (Platt and Trudgian 2021, quoted, not recomputed); above that
height the total weight is about 3e-12 and is irrelevant at these `y`.

**Planted faults.** `test_planted_faults_in_the_explicit_formula_go_red`: the
float defect test fails on each of the zero sum with the opposite sign, `T`
dropped, `gamma` off by 1e-3, and one zero removed from the list while the
budget is computed from the full list. The fifth fault of the first version,
`c0` off by 1e-4 read at `y = 1`, was the tautology above and is replaced:
`c0` off by 1e-6 is now read against the zero density, where the 20000-zero
budget would miss the prediction by 0.63 percent against a tolerance of 0.2.
`test_the_arb_zero_side_runs_and_its_planted_faults_go_red` calls the Arb
route itself with 300 zeros. At `y = 2.5` Arb decides the inequality for the
true formula and decides its failure for the opposite sign, for `T` dropped
and for a constant off by two budgets; a constant off by 1e-4, below the
budget, passes. At `y = 100.5` dropping `T` passes too, because `T` there is
far below the budget. Before the review no test executed this route: flipping
the sign inside it left all 25 tests green.

## 4. The RH envelope, measured

`scan_1e9.json` holds `F(n)` extremes for every integer `2 <= n <= 10^9` in ten
bins per decade (float route, 130.1 s on one core).
`scan_1e9_enclosed.json` holds Arb values at the per-decade extremes: four per
decade (the minimum, the integer maximum, the interior maximum, and the
maximum of `G(n)/sqrt(n)`), each at 128 and at 192 bits. The two enclosures
overlap at all 36 values and agree to every digit the 128-bit ball prints, 24
or more. The first version of this stage repeated only the 9 minima at 192
bits while this paragraph said "repeated at 192 bits with identical digits"
of all of them; the stage was rerun in the review round and reproduced every
earlier field exactly.

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
  `F' = [-4.9723679e-21 +/- 1.28e-29]`. The integer next to it is 34186454.
- minimum: `F = [-0.02268124049589207899539318 +/- 1.72e-27]` at the prime
  319439.
- `c0 = 0.0461914179322420676...`. Arb decides `-c0 < F < c0` at these two
  points and at the other 25 values of `F` in the file, at both precisions.

So in the scanned range the normalised quantity uses 53 percent of the room RH
allows above and 49 percent below. That the scan stays inside the envelope is
not news about zeta: without RH, the bound of section 6 already gives
`|F(y)| <= c0 + 4.7e-08` for `y <= 10^9`. A value outside would have been a
bug. The scan itself is float grade and is not a finite-range theorem: the
signs at the integers are float signs.

The archive's own form, `G(y) <= y^theta` with `C = 1`: the last integer with
`G(n) > sqrt(n)` is `n = 3`. From `n = 4` to `10^9` the scan has
`G(n) < sqrt(n)`, and the supremum of `G(n)/sqrt(n)` over `n >= 100` is 0.18022
at `n = 118`. Under RH this is automatic for `y >= 4`, because `c0 < 1`.
Without RH it is a published theorem on `8950 <= y <= 8.2 * 10^22` (Ramare
2013, Theorem 1.1, read, not re-proved). The scan adds finer constants inside
that range. It adds no range.

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
  As for zeta, the ratio at `y = 1` is 1 for any zero list and is not counted.
- Planted faults: the formula of the other parity fails for both test
  characters, and so does `L'/L(1)` off by 1e-3.

**Levels (`levels_q20_y7.json`, `levels_q30_y6.json`).** For `Level.cyc psi`
with `psi` of order `o`, the envelope is `|Gm(y) - M(y)| <= C sqrt(y)` with
`C = c0 + (3o+1)^-1 sum_k c_k` and `M` assembled from the constants above. The
identity `Gm(1) - M(1) = C` holds in Arb for every level; like its zeta
analogue it is arithmetic of the constants, and what it checks is that the
weights and constants were assembled consistently (a wrong weight breaks it:
`test_level_arb_route_against_float_route_and_a_planted_weight_fault`).

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

## 6. Lesion, and what is known without RH

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

**What this says about teeth.** The criterion does respond to an off-line
zero, in every window, but only from `Y` near `onset^(2/3)`. Two different
numbers bound where that can first happen. The first version of this file
gave only the first of them and let it read as the frontier.

- *One planted quadruple (closed form, not a measurement).* At the verified
  height `gamma0 = 3 * 10^12` with `beta = 1`, a single quadruple first breaks
  `G <= sqrt(y)` at `y` near `10^49.3` and first breaks the envelope at
  `10^46.6`; with `beta` closer to 1/2 the onset is later without bound. This
  is a model of one quadruple acting alone.
- *What is known without RH (derivation; the weight is float grade).* Let `H`
  be a height below which every zero is on the line and
  `w1 = sum_{gamma > H} 1/gamma^2`. Pair `rho` with `1 - conj(rho)` and use
  `|rho(1-rho)| >= gamma^2`: the zeros above `H` contribute at most
  `w1 (y + sqrt(y))` to the zero sum at `y` and at most `2 w1` at 1, so for
  `y >= 1`

      |G(y) - log(2 pi) - T(y)| <= c0 sqrt(y) + w1 (y + 3 sqrt(y)).

  With `H = 3 * 10^12` the zero density gives `w1 = 1.48e-12` (leading term,
  not enclosed; `frontier.json`). The excess over the RH envelope is 4.7e-08
  at `y = 10^9` and reaches `c0` itself at `y = 9.7 * 10^20`, and
  `G(y) <= sqrt(y)` is guaranteed for `4 <= y <= 4.2 * 10^23`. Bounding every
  zero above `H` by `y`, as the reviewer did, gives 2.4 * 10^20 and
  1.1 * 10^23. The published form is Ramare's Theorem 1.1:
  `|G(x)| <= sqrt(x)/2 + 1.75e-12 x` for `x >= 8950`, hence `G(x) <= sqrt(x)`
  up to 8.2 * 10^22.

So known facts guarantee the interface inequality with `theta = 1/2` and
`C = 1` up to about `10^23` and no further. Between about `10^23` and the
single-quadruple onset near `10^49`, nothing in this hunt excludes a violation
made by many zeros above `H` acting together; whether zero-density theorems
narrow that gap was not examined. The scan to `10^9` sits fourteen orders of
magnitude inside the guaranteed range.

Conversely, in the scanned range a single quadruple is visible only when its
height is of order 10^3 or less (`beta = 1`) or a few tens or less
(`beta = 0.6`), all long excluded. The closed form puts those limits at 1170
and 18.5, and it is an order of magnitude, not a threshold: it sets the plant
against the whole envelope, while `F` itself already uses up to 0.53 of it.
On the prime side to `10^7`, where the closed form gives 370, a plant at
`gamma0 = 407` is still flagged (first at `n = 5553908`) and one at 444 is
not. For `beta = 0.6` the looseness is larger: with `gamma0 = 10` the
envelope breaks at `y = 16.5` where the closed form says 4432, and with
`gamma0 = 30` the model puts the break at 3.2 * 10^11, beyond the scan. The
scan tests the transcription and the instrument. It does not test RH beyond
what is known.

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

**The standing battery, all four rivals (`rivals.json`, key
`battery_type_claim`).** `zeta.epstein.battery` was run on a necessary
condition of the type: for `n <= 60`, `Lambda_f(n)` vanishes off the prime
powers and `|Lambda_f(p^k)| <= log p`. Zeta passes. Davenport-Heilbronn,
Epstein (1,1,6) and the shifted product `zeta(s + 1/4) zeta(s - 1/4)` fail;
for the shifted product `Lambda_f(2)/log 2 = 2.0301`, which is
`2^(1/4) + 2^(-1/4)`. The Epstein form (2,1,3) is **undefined for this
claim**: it does not represent 1, so `a_1 = 0` and it has no log-derivative
Dirichlet series in the normalisation `a_1 = 1`. It was therefore not tested,
and the battery returns `distinguishes: False`, as its rule requires when a
rival could not be evaluated. The first version of this file never mentioned
(2,1,3) and called the shifted product "the third battery rival".

**The interface inequality on the rivals.** Epstein (1,1,6), first `n` with
`G_f(n) > n^theta`, against the onset law of section 6 for its recorded zero:

| theta | first violation | onset law | observed / predicted | first violation with the recorded quadruple subtracted |
| --- | --- | --- | --- | --- |
| 0.5 | 72 | 48428 | 0.0015 | 89 |
| 0.55 | 22132 | 184500 | 0.1200 | none to 10^7 |
| 0.6 | 1025840 | 1026448 | 0.9994 | none to 10^7 |

The law fits at 0.6 and only there. The first version quoted the prediction
at 0.6, gave 22132 without its prediction and left out 72. What the data say:

- At 0.5 the violations are not the off-line zero's doing. With its quadruple
  subtracted through the residue formula, the rest of `G_f` still exceeds
  `sqrt(n)`, first at `n = 89` and at 678135 integers up to 10^7 (4169350
  with the zero), and reaches 1.54 `sqrt(n)` at `n = 1888692`. With `C = 1` this function
  fails the bound at `theta = 1/2` even without that zero. The rest holds its
  on-line zeros, any other off-line zeros and its non-oscillating part, which
  were not separated.
- At 0.55 the violation needs the zero and arrives a factor 8.3 early: at
  `n = 22132` the quadruple contributes 98.8 and the rest 146.6 of the
  threshold 245.3. The law ignores the rest.
- At 0.6 the quadruple contributes 3178.3 of 4042.5 and the law holds to 0.06
  percent. The last window `[Y, Y^(3/2)]` without a violation of the 0.6
  bound starts at `Y = 10171`, which is `1025840^(2/3)`.

For `theta = 0.75` nothing happens below 10^7 (predicted onset 2.8 * 10^10).
For Davenport-Heilbronn nothing happens below 10^7 at any tested
`theta >= 1/2` (0.5, 0.6, 0.75): the predicted onset at `theta = 0.6` is
1.2e+17. Zeta through the same code path: no violation. So on the whole
computed range the inequality does not separate zeta from Davenport-Heilbronn.

**Which hypothesis each rival fails.** `zeroFree_of_rpow_window` has two
hypotheses besides `0 < theta < 1` and `delta > 0`: its argument is a
`CharFamily`, and the window bound holds.

- *The type.* A `CharFamily` is a finite family of Dirichlet characters with
  positive weights, and the statement's Mellin step uses
  `-L'/L = sum Lambda(n) chi(n) n^-s`. No rival is of this type. Three ways to
  see it:
  - *Arithmetic.* For Davenport-Heilbronn and Epstein (1,1,6), `Lambda_f` is
    not of the form `Lambda(n) chi(n)`: it is nonzero at 6, takes both signs,
    and is not bounded by a multiple of `Lambda`. For the shifted product the
    coefficients are `Lambda(n)(n^a + n^-a)`, a twist that is not a Dirichlet
    character, and the pole is at `1 + a`, so the normalization fails as well
    (derivation; the battery run above checks the coefficients only).
  - *Positive combination.* `Gm` is a positive combination of the `G` of
    L-functions, which is the `G` of a product of positive powers of
    L-functions. Davenport-Heilbronn and the Epstein functions are linear
    combinations of L-functions with Euler products, not factors of such a
    product.
  - *Nonvanishing on `Re s >= 1`.* This is not a hypothesis of the statement.
    It is a property of the members of the type that the archive's proof text
    calls (`.../LandauTheorems/lemmaL.lean:18-19`). Davenport-Heilbronn and
    the Epstein functions lack it: both have zeros with `Re s > 1` (Davenport
    and Heilbronn 1936, quoted, not recomputed), so `sum Lambda_f(n) n^-s`
    cannot represent `-f'/f` on all of `Re s > 1`, and the measured slopes
    above 1 are the visible trace. The first version listed this as a
    separate hypothesis.
- *The bound itself.* Epstein (1,1,6) violates `G_f <= y^theta` inside the
  range computed for `theta <= 0.6`. Davenport-Heilbronn does not, and is
  predicted to only far outside it.

Reading. The window criterion is a shared lemma: applied to a rival it reports
the rival's off-line zero, as it should. A rival that fails a hypothesis
excludes nothing about the posted proof. The step that would distinguish, the
upper bound for `Gm` produced from Frobenius classes of an abelian CM field,
cannot be formulated for any of the rivals and was not examined here. The
smoothed sum of the shifted product was not computed.

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
oscillation theorems of Pintz type. Review round, same day: (7) the title of
the 2013 paper below with the word corrigendum, after which both author copies
were fetched and read (sha256 in `frontier.json`).

Found:

- **The identity: zero delta.** O. Ramare, Corrigendum to "Explicit estimates
  for the summatory function of Lambda(n)/n from the one of Lambda(n)", Acta
  Arith. 211 (2023), 93-96, DOI 10.4064/aa220605-11-10 (journal reference from
  the publisher's listing; the author copy was read). Its Lemma 2.1 corrects
  Lemma 2.2 of the 2013 paper (Acta Arith. 159 (2013), 113-122) and states,
  for `x >= 1`:
  `sum_{n<=x} Lambda(n)/n = log x - gamma + (psi(x) - x)/x - sum_rho x^(rho-1)/(rho(rho-1)) + B(x)/x`,
  `B(x) = log 2pi + (1/2) log(1 - x^-2) + (1/2)(x log((x+1)/(x-1)) - 2)`,
  with `0 <= B(x) <= log 2pi`. Multiplying by `x` gives
  `G(x) = sum_rho x^rho/(rho(1-rho)) + B(x)` with `B(x) = log 2pi + T(x)`:
  the identity of section 3, sign for sign.
- **What the first version said about the source, and why it was wrong.** It
  cited Lemma 2.2 of the 2013 paper "up to rearrangement", wrote "the journal
  version was not consulted", and reported the sign as something the defect
  test had found. Its description of the 2013 printing was accurate: there the
  zero sum carries a plus sign and
  `B(x) = 1/2 + log 2pi - ((x-1)/2) log(1 - 1/x)`, so that `B(1) = 2.338`
  where the identity needs `log 4pi - 1 = 1.531`, and the planted-fault test
  with the printed sign goes red. But the author had corrected both points in
  2023 (the corrigendum's abstract says Lemmas 2.1 and 2.2 contain sign
  errors), and the first title search for the paper returns the corrigendum.
  The defect test agrees with the corrected lemma and rejects the misprinted
  one. It discovered nothing.
- **The explicit formula used in the derivation.** Lemma 1.1 of the
  corrigendum, the corrected Lemma 2.1 of the 2013 paper and Lemma 4 of Ramare
  and Saouter (2003): for `g` continuously differentiable on `[a, b]` with
  `2 <= a <= b`, the integral of `psi(t) g(t)` is that of `t g(t)`, minus the
  sum over `rho` of the integrals of `t^rho g(t)/rho`, minus the integral of
  `(log 2pi + (1/2) log(1 - t^-2)) g(t)`. It is stated for `a >= 2`; the
  corrigendum states its Lemma 2.1 for `x >= 1`; this hunt's grid has 10
  points in `1 < y < 2`.
- **The unconditional frontier.** Theorem 1.1 of the 2013 paper, which the
  corrigendum says needs no change: for `x >= 8950`,
  `sum_{n<=x} Lambda(n)/n = log x - gamma + (psi(x) - x)/x + O*(1/(2 sqrt(x))) + O*(1.75e-12)`.
  In this hunt's units, `|G(x)| <= sqrt(x)/2 + 1.75e-12 x` for `x >= 8950`. So
  the zeta-only interface inequality `G(y) <= sqrt(y)` with `C = 1` is a
  published two-sided theorem on `8950 <= y <= 8.2 * 10^22`. Its proof bounds
  the zero sum by `0.047 sqrt(x)` plus the tail, which is the envelope of
  section 3 with 0.047 for `c0`. Read, not re-proved.
- **One step of that proof, checked because its constant sets the reach
  (measured; `frontier.json`).** Lemma 4.2 of the 2013 paper, as the author
  copy prints it, bounds `sum_{gamma >= T} 1/gamma^2` by
  `log(T/2pi)/(2 pi T) + 0.67 (2 log(T/2pi) + 1/2)/T^2` for `T >= 1000`. At
  `T = 1000` the 19351 listed zeros with `1000 <= gamma <= 18046.464` alone sum
  to 8.866e-04, above the printed bound 8.140e-04. With the tail above the
  table read off `c0` the sum is 9.657e-04, and the density integral
  `(log(T/2pi) + 1)/(2 pi T)` gives 9.661e-04. The printed bound appears to
  drop the term `1/(2 pi T)`. At the paper's `T0 = 2.44 * 10^12` that turns
  1.74e-12 into 1.81e-12, above the theorem's 1.75e-12; at the height
  `3 * 10^12` verified since, the same integral gives 1.48e-12, below it. On
  this reading the constant of Theorem 1.1 stands with the later verification
  height. This is a float-grade observation about one printed lemma in an
  author copy. It is not a reviewed erratum and the journal version was not
  consulted.
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

Not found in these searches: the one-inequality equivalence with the sharp
constant attained at `y = 1` stated as such, or a one-sided windowed Landau
statement for this smoothed sum. The inequality
`|G(y) - log 2pi - T(y)| <= c0 sqrt(y)` under RH is not on that list any more:
with 0.047 for `c0` it is inside the proof of Ramare's Theorem 1.1. Claim
made: the formula and the bound were derived in this lab before the source was
found (original in the sense of provenance); the formula is a published lemma
with zero delta; the bound is a one-line consequence that the same paper
already uses with a rounded constant; no novelty is claimed. Seven searches
are not a literature review, and the first six missed a corrigendum that a
title search returns first.

## Standing checklist

1. **Rival.** Section 7. All four members of the standing battery are
   accounted for: Davenport-Heilbronn, Epstein (1,1,6) and the shifted product
   fail the type, and Epstein (2,1,3) is undefined for this claim and was not
   tested. On the inequality itself only the Epstein function (1,1,6) violates
   it in reach. Davenport-Heilbronn satisfies `G_f(n) <= n^theta` for every
   tested `theta >= 1/2` on the whole computed range, so within reach the
   inequality does not separate zeta from Davenport-Heilbronn. The first
   version said here that the claim "is not shared by the rivals", which holds
   for the Epstein function only. The test set is not the rival set: the
   envelope was measured on zeta and 167 Dirichlet characters, the rivals are
   the standing battery, and the rival zeros used are ones this lab recorded
   before this hunt. What the rivals share with zeta is the window criterion
   as a function-agnostic lemma, and that was said, not hidden.
2. **Decoy.** Section 8. A Cramer set of the same density misses the envelope
   by a factor near 900 after the best linear refit. The effect is not a
   consequence of density.
3. **Lesion.** Section 6 and the planted-fault tests. A planted quadruple is
   flagged where the closed form says, and it is told apart from the true
   signal: with no plant nothing fires in the same range. In the scanned range
   the detector cannot see a single plant above a height of order 10^3 (closed
   form 1170, loose by tens of percent), and that limit is reported as the
   scope of the measurement. One hazard this file names itself: a missing
   on-line zero in the list looks like a defect of the formula, and the test
   plants exactly that. The exact tail budget is the completeness check on the
   list.
4. **Precision response.** The identity's defect falls from 9.95e-04 to
   1.30e-05 (relative to `sqrt(y)`) as the zero list grows from 100 to 20000,
   tracking the budget. All 36 enclosed values overlap at 128 and 192 bits,
   and the 18 values of `F` at the decade extremes agree with float64 to
   4.0e-12. The envelope ratio does not move with precision, as a real
   quantity should not.

## Caveats

- The scan is float grade. Its signs are not rigorous and the range
  `2 <= y <= 10^9` is not covered by a theorem of this hunt. Arb was used at
  36 extremal values and at spot checks, not at every integer.
- The passage from integers to real `y` rests on the concavity argument of
  section 4, a derivation.
- The sharp calibration of the identity is float grade. Arb decides a coarse
  inequality at 4 points and nothing finer (section 3).
- That `c0` is the sum over the zeros is classical. Here it is checked only
  through the zero density, to 3.7e-09, at float grade.
- The tail budgets assume the unlisted zeros are on the line. For the Dirichlet
  characters the zero lists come from sign changes, which is a lower bound on
  the count; the budgets match the density to 0.7 percent, which is a check and
  not a proof of completeness.
- The weight `w1` in the bound of section 6 is the leading term of the zero
  density, not an enclosure, and the bound is a derivation. The published
  theorem next to it was read, not re-proved, and one lemma of its proof does
  not hold as printed in the copy read (Literature).
- The transcription is of text. Machine-generated names were not trusted;
  Mathlib's meaning of each symbol was assumed standard. No kernel was run.
  The identification of `Level.Gm` with the `Deduction.Gm` of the windowed
  statement rests on three archive lemmas whose proofs were not examined.
- Whether the windowed statement is true as stated, whether its proof text is
  complete, and whether the upper bound for `Gm` is established anywhere in the
  archive, are outside this hunt.
- The Epstein off-line zero is this lab's 20-digit measurement.
- What the tests pin. Every decimal number, every number in scientific
  notation and every integer of four or more digits in this file is inside a
  phrase that `test_rh_claim_interface.py` either builds from the committed
  data or holds as a frozen reference string (citations, archive locations,
  dates), with an exact occurrence count, and a mutation test changes each
  such number in turn and requires a failure. Integers below 1000 are pinned
  only where such a phrase carries them. A frozen string guards against
  drift, not against being wrong.
- The unit timings of the first round are evidenced by a log only for the
  scan (`RUNS.md`).
- The first lesion run let the BLAS library use more than one core for about
  half a minute; later runs were pinned to one thread (`RUNS.md`).
- `tests/test_hunt_probe_discipline.py::test_every_hunt_directory_is_covered_by_the_case_log`
  fails until the case-log entry returned with this hunt is placed in
  `hunts/README.md`, which this hunt may not edit.

## Review findings and dispositions

Two independent reviewers attacked the first version of this hunt on
2026-11-20, one on mathematics, transcription and literature (R1) and one on
numerics and tests (R2). Both verdicts: "holds". Every finding below was
reproduced by this hunt before anything was changed; none was found not real.
Where a reviewer's own detail did not reproduce exactly, that is said.

| id | severity | finding | reproduced by | disposition |
| --- | --- | --- | --- | --- |
| R1.1 | major | The identity is Ramare's corrected Lemma 2.1 (2023); "Lemma 2.2 of Ramare (2013) up to rearrangement" was false for the lemma as printed; the sign was not this hunt's finding; Theorem 1.1 makes `G(y) <= sqrt(y)` a published theorem far beyond the scan | fetching and reading both author copies; a search that returns the corrigendum | fixed: item 7, section 3, Literature, MISSION frontier line; item 2 regraded from "derivation, hardened at spot points" to "published, recalibrated at float grade" |
| R1.2 | minor | `10^49.3` and `10^46.6` are a one-quadruple model, not the frontier | recomputing the weight above height 3 * 10^12 and the two crossings (2.4 * 10^20, 1.1 * 10^23) | fixed: item 5, section 6, MISSION dead routes; the bound was also sharpened by pairing zeros (9.7 * 10^20, 4.2 * 10^23) |
| R1.3, R2.3 | minor | "hardened at 128 and 192 bits" was true only for the minima | reading `stage_enclose` and the JSON keys | fixed by a rerun: all 36 values at both precisions; the earlier fields reproduced exactly |
| R1.4 | minor | three statements at `y = 1` were algebraic tautologies presented as calibration | the algebra `defect(1) = c0 - partial sum` | fixed: relabelled in item 3, section 3, section 5 and the doors; "calibrated to 30 digits by Arb" withdrawn; the tautological planted fault replaced |
| R1.5 | minor | rivals: (2,1,3) missing; onset law quoted only where it fits; nonvanishing is not a hypothesis; the inequality is not "not shared by the rivals" | reading `zeta.epstein.battery`; `rivals.json`; `lemmaL.lean:18-19` | fixed: battery run on all four with (2,1,3) recorded as undefined; all three onsets printed with a measured attribution; hypothesis list restructured; checklist item 1 reworded |
| R1.6 | minor | transcription: the `theta` gloss; unsigned `eD`, `eL`; `ramp` and `Deduction.Gchi` not quoted; "y" for an integer scan | reading `TopWin.lean:26-28` and `68-81`, `CharFamily.lean:10-19` and the three bridging statements | fixed: seven quotes and three glosses added to `transcription.json`, section 1 corrected, item 4 says integers |
| R2.1 | minor | the pins were substring checks; ten altered numbers passed all 25 tests | altering the same kinds of number in a scratch copy of the first version: 25 passed | fixed: exact-count phrase pins and a mutation test over every pinned number; the test docstring now says what is and is not pinned |
| R2.2 | minor | no test executed the Arb zero side; the Arb spot check is coarse; the `y = 1` ratio cannot fail | flipping the sign and dropping `T` inside `zeta_zero_side_arb` in the scratch copy: 25 passed; budget over defect 2510, 822, 97, 205 | fixed: a test now runs the route and plants faults at the Arb level; the resolution is printed next to the claim |
| R2.4 | minor | the Epstein onset at 0.6 was quoted with its prediction, the one at 0.55 without | `rivals.json` | fixed with R1.5 |
| R2.5 | minor | "written before the scaled runs" is not evidenced; no unit for two stages | the logs and the file times | downgraded in `RUNS.md`; review-round estimates were logged with a time stamp before each run |
| R2.6 | minor | the closed-form reach (1170, 18.5) is loose by tens of percent | the prime side to `10^7`: a plant at 407 is flagged where the closed form gives 370 | fixed: section 6 and checklist item 3 reworded |

Details where this hunt's reproduction differs from a reviewer's report:

- R1.1 gives the reach of Theorem 1.1 as "about 8.1e22";
  `(0.5/1.75e-12)^2` is 8.2 * 10^22 to two digits.
- R1.2 bounds every zero above the verified height by `y`. Half of them have
  real part at most 1/2, which halves the weight on `y`; both versions are in
  `frontier.json`.
- R2.6 reports the first flagged integer for the plant at 407 as 5547578 on
  the reviewer's own prime side. This hunt's instrument gives 5553908. The
  difference was not chased; both are far above the closed form's reach.
- Reading the proof of Theorem 1.1 for R1.1 turned up the Lemma 4.2
  observation recorded under Literature. No reviewer asked for it.

What the reviewers checked and found sound, as reported by them and not rerun
here: all 13 file hashes and the tarball hash; 13 quotes character for
character; the explicit formulas for zeta and for odd and even characters
rederived by Mellin inversion; the nine decade minima and maxima by two
independent scans; the two extreme values in mpmath at 30 and 50 digits;
`L'/L(1, chi)` by three further routes; the lesion and Davenport-Heilbronn
responses to a moved zero.

A fault of this round, recorded: the first review-round run of the rival
stage had a wrong bound in the new battery claim (it compared with `p`, not
`log p`) and reported the shifted product as passing. The recorded
coefficient 2.0301 contradicted it, the bound was fixed and the stage rerun.

## The doors

This hunt measures a supremum, so it owes the three lists.

1. **Active constraints at the optimum.** Under RH the supremum of `F` over
   `y >= 1` is `c0` exactly and is attained at `y = 1`, where every phase
   `gamma log y` vanishes. Away from 1 what binds is simultaneous alignment of
   the low zeros: the first zero alone carries 21.6 percent of `c0`. The
   per-decade maxima (0.29, 0.36, 0.39, 0.40, 0.36, 0.39, 0.40, 0.53, 0.47 of
   `c0`) show no trend over nine decades, so the saturation curve is flat in
   the range and the measured 0.5346 is a property of the range, not a limit.
   For the reach of the criterion the binding constraint is the height `H`
   below which RH is verified. The guaranteed range of `G(y) <= sqrt(y)` ends
   near `((1 - c0)/w1)^2`, which grows like `(H/log H)^2`; the onset of a
   single quadruple, `(|rho(1-rho)|/2)^(1/(beta-theta))`, grows like the
   square of the height or faster.
2. **The frozen-constant inventory.**
   - Window exponent 3/2 and `C = 1`: the archive's. *Genuine trade shape*: a
     window `[Y, Y^la]` sees a violation from `Y = onset^(1/la)`, so a larger
     `la` asks more of the upper bound and gives teeth earlier.
   - Weights `(3o+1)^-1`: the archive's. They dilute the characters, which is
     why level ratios (0.7180) sit below character ratios (0.9463).
   - 20000 zeros, 64-bit: tail budget 1.58e-04. *Trade*: cost is linear in the
     count, budget falls like `log T / T`.
   - `y <= 10^9` for zeta, `10^7` for conductor at most 20, `10^6` up to 30:
     chosen by the one-core budget. *Trade*: about 130 s per factor 10 for
     zeta, about 95 s per 10^7 for 114 character combinations.
   - The verification height `3 * 10^12` in the bound of section 6: quoted.
     *Trade*: the guaranteed range grows with its square.
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

Proof status of the optimum: the value `c0` at `y = 1` is arithmetic of
constants and holds with or without RH; that `c0` bounds `F` for `y > 1` is
conditional on RH, and without RH the bound of section 6 replaces it; the
range maximum 0.5346 of `c0` is a float scan with Arb values at the located
points. None of these is a proved ceiling of this hunt.
