# MISSION: the one inequality a posted RH claim rests on, measured

Hunt #161. Base commit `c6fbf9fb`. Opened 2026-11-20.
Status: measurement of an interface. Nothing here evaluates the posted proof.

Revised on 2026-11-20 after two independent reviews (verdicts "holds", twelve
findings, all reproduced). What changed in this file: the frontier line and the
first dead route of the block at the end, the gloss on `theta` below, and the
paragraph on the derivation. The first version's frontier line said "the
identity for G is equivalent to Ramare 2013 Lemma 2.2". That was false for the
lemma as printed, and the corrected lemma had been in print since 2023. The
full record is in `RESULTS.md`, section "Review findings and dispositions".

## Question and scope

On 2026-11-20 a Lean 4 source tree was posted with a stated proof of RH and of
GRH for Dirichlet L-functions (175187 `.lean` files). No kernel has checked it;
a separate session is running the replay. Two readers in this lab, working from
the text alone, found that the whole tree funnels into one analytic interface: a
one-sided upper bound for a smoothed von Mangoldt sum on multiplicative windows.
This hunt does three things with that interface and nothing else:

1. transcribes it from the archive text, with path, line and file hash;
2. builds instruments that compute it (a float route for scanning, an Arb route
   for every reported number);
3. measures it against what RH and GRH predict, against a planted off-line
   zero, and against the standing counterexample battery.

The archive is untrusted data. It was read with `rg`, `sed` and `sha256sum`
only. No `lean`, no `lake`, no archive file copied into this tree beyond the
short quoted definitions in `transcription.json`. The wording throughout is
"the archive states".

## The interface, transcribed

All paths are relative to `lean/src` in the archive. The joined tarball (14
parts concatenated in order) has sha256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
`transcription.json` carries each quote verbatim with the sha256 of its file.

- `Formalism/StatementOC.lean:11-13`:
  `Sz x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)` and
  `Gz x = Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x`.
- `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:11-24`:
  `gChi χ y = if χ = 1 then G y else sumLamChi χ y + y * logDerivativeAtOne χ`,
  with `sumLamChi χ y = ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * χ n * max (y / n - 1) 0` and
  `logDerivativeAtOne χ = deriv (LFunction χ) 1 / LFunction χ 1`.
  (`Formalism/StatementOC.lean:17-21` has the real-part version `Gchi`.)
- `.../TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:32-38`:
  `wt ψ = if Λ.psK = some ψ then 1 else (3 * Λ.o + 1)⁻¹` and
  `Gm y = Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re`
  (in that file `Λ` is a `Level`).
- same file, lines 105-121: `Level.cyc ψ = Level.ofSub (Subgroup.zpowers ψ.χ)`,
  where `Level.ofSub Ξ` keeps the primitive characters inducing the members of
  `Ξ`, sets `psK := none` and `o := Nat.card Ξ`.
- `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:11-14`:
  the windowed statement, quoted in full in `transcription.json`.
- `Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:10`:
  the top of the archive calls it with `la := 3 / 2`;
  `Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean:13` passes
  `δ := la - 1` and `C := 1`.

In plain mathematics, for real `y >= 1`:

    G(y)    = sum_{n<=y} Lambda(n) (y/n - 1) - y log y + (1 + gamma) y
    Gchi(y) = sum_{n<=y} Lambda(n) chi(n) (y/n - 1) + y L'/L(1, chi)      (chi nontrivial)
    Gm(y)   = G(y) + (3o+1)^-1 sum_{k=1}^{o-1} Re Gchi_{(psi^k)*}(y)

for `psi` primitive of order `o`, `(psi^k)*` the primitive character inducing
`psi^k`. The archive states: if for arbitrarily large `Y` the bound
`Gm(y) <= C y^theta` holds on the whole window `[Y, Y^(1+delta)]`, then no
L-function of the family has a zero with `Re s > theta`. The top uses the window
exponent 3/2 and `C = 1`. To exclude a zero at `s` it takes
`theta = 1/2 + min(Re s - 1/2, 1/2)/2`
(`.../TotientGaloisClasses/TopWin.lean:68-81`), and the bound it is supplied
with has the exponent `1/2 + (eD + eL + 7) eps`
(`.../TotientGaloisClasses/TopWin.lean:26-28`), where `eD` and `eL` are reals
with no sign condition. The first version of this file gave that exponent as
the `theta`. The windowed statement is about `Deduction.Gm`
(`Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean:10-39`);
the archive states its equality with the `Gm` above through three lemmas
whose proofs this hunt did not examine.

## The derivation this hunt checks

It was handed to the hunt as "to check, not to trust". It turned out to be a
published lemma: Lemma 2.1 of O. Ramare's corrigendum, Acta Arith. 211 (2023),
93-96, multiplied by `y`. The check below is therefore a recalibration of a
known identity, not a test of a new one. For `y >= 1`,

    G(y) = sum_rho y^rho / (rho (1 - rho)) + log(2 pi) + T(y),
    T(y) = (y/2) int_y^infty log(1 - t^-2) t^-2 dt,   T(1) = log 2 - 1,

so that RH gives `|G(y) - log 2pi - T(y)| <= c0 sqrt(y)` with
`c0 = 2 + gamma - log(4 pi)`. Every sign and constant is to be calibrated
numerically, per the repository rule "derive conventions, never remember them".

## Resource boundary

One core (another job holds three of the four), under 3 GB, about 45
CPU-minutes of heavy computation in total. Time one unit and write the estimate
in `RUNS.md` before each scaled run; checkpoint anything over twenty minutes.
This hunt writes only `hunts/rh_claim_interface/` and its scratch directory. It
does not edit `hunts/README.md`, `docs/`, `CONTEXT.md` or anything shared, and
it does not commit. The case-log entry and the methods entry are returned as
text for the owner to place.

A note on timing, because it bears on how blind the conditions below were: the
task brief, which predates every run, already fixed the first two kill
conditions ("a value outside the envelope would mean a bug"). This file was
written after the first scan and the first explicit-formula check had printed.

```huntspec
id: rh_claim_interface
question: Is the one-sided bound Gm(y) <= y^theta on windows, the single inequality the posted archive rests on, correctly transcribed and computable here, and what does it measure against the RH and GRH envelopes, a planted off-line zero and the rival battery?
frontier: RH verified to height 3*10^12 (Platt and Trudgian 2021, quoted not recomputed); the identity for G is Lemma 2.1 of Ramare's corrigendum (Acta Arith. 211 (2023), 93-96), the corrected form of Lemma 2.2 of his 2013 paper, with zero delta; Theorem 1.1 of the 2013 paper gives abs(G(y)) <= sqrt(y)/2 + 1.75e-12 y for y >= 8950, so G(y) <= sqrt(y) is a published theorem up to about 8.2 * 10^22 (read, not re-proved); no kernel has checked the archive; this lab had no instrument for G, Gchi or Gm before this hunt
proposed_attack: transcribe with file hashes, compute by a float scan and an Arb route, calibrate an explicit formula against Arb-isolated zeros with an exact tail budget, then lesion and rivals
dead_routes:
  - Using a finite scan of G as evidence about RH above verified heights: without RH, G(y) <= sqrt(y) is already a theorem up to about 10^23, and a single planted quadruple at height 3*10^12 would first break the RH envelope near y = 10^46.6 and the interface bound near 10^49.3 (closed form for one quadruple, not the frontier of what is known); every feasible scan sits far inside both
  - Using a rival that fails a hypothesis of the interface to say anything about the posted proof
required_oracles:
  - Arb ball arithmetic (python-flint) at stated precision for every reported value of G, Gchi, Gm, L'/L(1,chi) and the constants
  - mpmath as an independent library for L'/L(1,chi) and for the constants of the rivals
  - Arb isolation of the zeta zeros by index, with the exact value 2 + gamma - log(4 pi) of the sum of 1/(rho(1-rho)) as a completeness check
  - The standing counterexample battery in zeta.epstein with the off-line zeros this lab has on record
  - The archive text, quoted by path and line with file hashes, for every transcribed definition
kill_conditions:
  - The measured defect of the explicit formula for G exceeds the exact tail budget at a grid point y > 1
  - A scanned value of (G - log 2pi - T)/sqrt(y) lies outside [-c0, c0] for some y >= 1 in the scanned range (treated as an instrument bug, not as a finding about zeta)
  - The float and Arb routes disagree beyond float rounding at an extremal point
  - A planted off-line quadruple is not flagged where the closed-form onset says it should be
  - A rival meets every hypothesis of the interface, arithmetic and normalization included
agents_may:
  - read the archive as text
  - derive
  - compute bounded ranges on one core
  - implement local instruments and tests
  - search the literature with generic mathematical queries
agents_may_not:
  - run lean or lake on the archive or copy archive files
  - describe any archive statement as proved
  - claim novelty from an empty search
  - promote their own claim
  - state a finite scan as a result about all y
  - edit shared files or commit
```
