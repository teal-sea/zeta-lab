# Hunt R-4218D4: results

**Settled.** The variance constant moved from `5855` to `275`, a factor of
21.3, with every statement's shape preserved, no hypothesis added, no sorry,
and a green `lake build`. The three constants below are kernel-checked by
Lean 4 + Mathlib v4.33.0-rc2 against the standard axioms.

Reproduce the arithmetic with `python3 hunts/r_4218d4/probe.py`; reproduce
the mathematics with `cd lean && lake build` and the axiom audit in
`PrintMertensAxioms.lean`.

## Before and after

| quantity | before | after | reference |
|---|---|---|---|
| Chebyshev remainder constant, `psi x <= x log 4 + c x` | `4` | `3/2` | sharp value `4/e = 1.4715` |
| `sum_{n <= N} (log n)/n^2` (`sum_log_div_sq_le`) | `6` | `3/2` | sharp `4/e = 1.4715`; limit `-zeta'(2) = 0.9375` |
| prime-power tail in Mertens I | `12` | `3` | sharp `8/e = 2.9430`; limit `0.7554` |
| **`mertens_first_theorem`** band | `log 4 + 16 = 17.3863` | **`log 4 + 3 = 4.3863`** | classical `2` |
| **`mertens_second_theorem`** band | `76` | **`16`** | assembly needs `15.698`; classical `4` |
| **`sum_sq_dev_le`** variance constant | `5855` | **`275`** | `m^2 + m + 3` in the Mertens band `m` |

Nothing else changed. `mertens_first_theorem`, `mertens_second_theorem`,
`sum_sq_dev_le`, `turan_variance` and `hardy_ramanujan` keep their names,
their arguments, their hypotheses and their shape; the only edits inside a
statement are numerals, and each moved down.

## What was chosen, and why

Three independent slack steps fed the chain. All three are local, which is
what the discovering runs predicted; none needed new mathematics.

### 1. The Chebyshev remainder: `4` -> `3/2`

Mathlib proves `Chebyshev.psi_le : psi x <= x log 4 + 2 sqrt(x) log x`, then
packages `psi_le_const_mul_self : psi x <= (log 4 + 4) x` by bounding
`2 sqrt(x) log x <= 4 x`, that is, by using `log t / sqrt t <= 2`. The
supremum of `log t / sqrt t` is `2/e = 0.7358`, attained at `t = e^2`, so
that step throws away a factor of `e/1` and a bit more.

The sharp majorant is one line: `log t <= t/e` for `t > 0`, which is
`log x <= x - 1` applied at `x = t/e` together with `log e = 1`. It is added
as `ZetaLean.Mertens.log_le_div_exp_one`. Composing it with
`log x = 2 log sqrt x` gives `2 sqrt(x) log x <= (4/e) x`, and `4/e < 3/2`
because `3e > 8`. The result is `psi_le_const_mul_self'`, stated for
`x >= 1` and used only at natural arguments.

Mathlib's own constant was left alone; this is a local corollary in this
repository's file, not a change to Mathlib.

### 2. `sum_log_div_sq_le`: `6` -> `3/2`

Two tightenings of one telescope, both cheap:

- the same `log t <= t/e` majorant gives `log n <= (2/e) sqrt n`, against the
  `log n <= 2 sqrt n` the file used (that came from `log t <= t - 1` applied
  to `sqrt n` directly, which is the same inequality used less sharply);
- the `n = 1` term of `sum (log n)/n^2` is zero, so the telescope may start
  at `n = 2`, where `sum_{2 <= n <= N} n^{-3/2} <= 2 - 2/sqrt N` rather than
  the `3 - 2/sqrt N` that starting at `1` forces. The existing lemma
  `sum_inv_mul_sqrt_le` is reused unchanged and the `n = 1` term subtracted.

`(2/e) * 2 = 4/e = 1.4715`, stated as `3/2`. The limit is
`-zeta'(2) = 0.9375`, so about 60 percent of what remains is the telescope
against the true sum, not the majorant.

The prime-power tail is `2 B` by the existing geometric layer bound, so it
falls from `12` to `3` with no other change.

### 3. Mertens I: keeping the two halves apart

This is the step neither discovering run named, and it is worth about `1.5`.

The von Mangoldt form is asymmetric. Its **lower** half loses only `1`
(from `N log N - N + 1 <= sum_{n<=N} log n <= N log N`), while its **upper**
half loses the whole Chebyshev constant. The prime form then loses the
tail on the lower side only, since the prime sum is at most the von Mangoldt
sum. So the honest band is

    max(c_psi, 1 + tail) = max(log 4 + 3/2, 4) = 4,

whereas routing through the *symmetric* von Mangoldt band, which is what the
original proof did, pays `c_psi + tail = log 4 + 4.5 = 5.886`.

A new one-sided lemma `log_sub_one_le_sum_vonMangoldt_div` extracts the
lower half; `abs_sum_vonMangoldt_div_sub_log_le` now uses it too, so nothing
is proved twice. `mertens_first_theorem` is stated as `log 4 + 3 = 4.3863`,
which covers `4` because `1 <= log 4`, and keeps the `log 4 + c` shape the
file has carried since it landed.

### 4. Propagation

`mertens_second_theorem` needed no structural change: the band `c` enters
its assembly as

    upper <=  c*r + 1 + |log log 2| + c*r
    lower >= -c*r + 1 - g            - c*r

with `r` an upper bound for `1/log 2` and `g = 4` the `sum 1/n^2` gap term.
Two numerals moved: `c` from `17.4` to `4.4` (the rounding of `log 4 + 3`),
and `r` from `2` to `1.443` (the true value is `1.442695`, and the sharper
bound is no harder to prove from Mathlib's `log_two_gt_d9`). The assembly
then needs `15.698`, and `16` is stated.

`sum_sq_dev_le` needed only its numerals: the variance decomposition is
`m^2 + m + 3` in the Mertens band `m`, unchanged, so `76 -> 16` gives
`5855 -> 275`.

## What could not be settled

**The classical constants are still out of reach, and deliberately so.**
Mertens I's classical band is `2` and we land `4.3863`; Mertens II's is `4`
and we land `16`. Closing either needs mathematics the brief explicitly
declined to fund, and the brief's kill condition ("do not chase the
classical constant at the cost of a green build") applies.

Three named steps resisted, with what each would need:

1. **The `4` in Mertens II from `sum 1/n^2` against the logarithm bracket.**
   `log_sub_log_le_mul_add` bounds `1/(xy)` by `4` from the hypothesis
   `1/2 < x`. In use, `x = log n` with `n >= 2`, so `1/(xy) <= 1/(log 2)^2 =
   2.081` and the term would fall from `4` to about `2.1`, taking the
   Mertens II band from `16` to about `14`. Getting it requires replacing
   the hypothesis `1/2 < x` by something like `0.69 < x`, which is a
   *stronger* hypothesis and therefore a weaker lemma. The addendum forbids
   that, so it was not done. The clean version instead threads the actual
   `log n >= log 2` through as a bound on the conclusion rather than a
   hypothesis, which is a small restructuring, not a numeral change.

2. **The telescope `sum_{2<=n<=N} n^{-3/2} <= 2`.** The true value is
   `zeta(3/2) - 1 = 1.6124`. The bound is the integral comparison
   `int_1^N x^{-3/2} dx`, which is already the natural one; improving it
   means an Euler-Maclaurin correction term, i.e. new mathematics for about
   `0.2` in `sum_log_div_sq_le` and about `0.4` in the tail. Not worth it at
   this budget.

3. **The main term `log 4` in the Chebyshev bound.** `psi x / x -> 1`, so
   `log 4 = 1.3863` is itself 39 percent slack, and it propagates to
   everything. Removing it is the prime number theorem, not a constant
   tightening, and Mathlib v4.33.0-rc2 does not carry PNT.

The residual budget after this run, in order of size: `log 4` (1.386, needs
PNT), the `4`-vs-`2.1` bracket factor in Mertens II (needs the
restructuring in point 1), the `1 + tail = 4` lower half of Mertens I (needs
a better tail than `2B`), and the roundings `3/2` for `4/e` and `1.443` for
`1/log 2` (worth about `0.03` each, not worth a rebuild).

## Verification

- `cd lean && PATH="$HOME/.elan/bin:$PATH" lake build ZetaLean.Mertensstheorems`,
  `... ZetaLean.MertensSecond` and `... ZetaLean.HardyRamanujantheorem` are each
  green with zero sorrys, on `leanprover/lean4:v4.33.0-rc2` with Mathlib
  `v4.33.0-rc2`, as is every other module that imports them.
- A full `lake build ZetaLean` in this container also killed two modules,
  `ZetaLean.Pub1.UpolyD2` and `ZetaLean.Pub1.CertAtoms`, with exit code 137.
  That is the OOM killer, not a proof failure: four `lean` processes were
  resident at about 6.5 GB each under the default parallelism. Neither module
  imports anything this hunt touched (both import only `Mathlib` and other
  `ZetaLean.Pub1.*` files, and nothing outside `MertensSecond`,
  `HardyRamanujantheorem` and `ZetaLean.lean` imports the edited files at all),
  so the failure is a property of this container's memory, not of the diff.
  Stated rather than smoothed over: this run did not observe a single green
  whole-library build, only a green build of the affected subtree.
- `lake env lean ../hunts/r_4218d4/PrintMertensAxioms.lean` reports
  `[propext, Classical.choice, Quot.sound]` for every theorem in the chain,
  unchanged from before this hunt.
- `python3 hunts/r_4218d4/probe.py` reproduces every number in the table
  above, and checks each majorant numerically against the quantity it
  majorises (`sum (log n)/n^2` and both telescopes to `N = 200000`, the
  prime-power tail to `p = 200000`).

Nothing here is evidence for or against the Riemann hypothesis
(`docs/08-why-it-is-hard.md`). Mertens's theorems and Hardy-Ramanujan are
unconditional classical results; only their explicit constants moved.

## Loose threads

1. **The bracket factor `4` in `MertensSecond.log_sub_log_le_mul_add`.**
   *What*: the lemma's `4 * c` comes from `1/(xy) < 4` under `1/2 < x`, but
   every call site has `x = log n` with `n >= 2`, where `1/(xy) <= 2.081`.
   *Why it might matter*: it is the largest remaining term in the Mertens II
   assembly that is not the Mertens band itself; fixing it would take `16` to
   roughly `14` and the variance constant from `275` to about `213`, still
   with no new mathematics.
   *First step*: add a second lemma taking `hx : c0 <= x` and concluding
   `log y - log x <= x(1/x - 1/y) + c/c0^2`, leave the existing lemma
   untouched, and call the new one with `c0 = log 2` in `hterm_lb`.

2. **`abs_psi_sub_theta_le_sqrt_mul_log` has the same `2/e` slack, upstream
   in Mathlib.** *What*: Mathlib's `psi_le_const_mul_self` bounds
   `2 sqrt(x) log x` by `4x`; `4/e = 1.4715` works, by exactly the argument
   used here. *Why it might matter*: it is a two-line improvement to a
   Mathlib lemma that other users of `psi_le_const_mul_self` would inherit,
   and this repository now has the proof written out.
   *First step*: open a Mathlib PR replacing `(log 4 + 4)` by
   `(log 4 + 3/2)` in `Mathlib/NumberTheory/Chebyshev.lean`, carrying
   `log_le_div_exp_one` as `Real.log_le_div_exp_one` if Mathlib lacks it.
   Note the statement is for `0 <= x` there and the sharp bound needs
   `1 <= x`, so the `x < 1` case has to be handled separately (`psi x = 0`).

3. **The `omega` second-moment argument never uses the sharper first
   moment.** *What*: `sum_sq_dev_le` feeds `first_moment_lower`'s loss of
   `N` (one unit per prime) into the `+3` of `m^2 + m + 3`. The true loss is
   `pi(N)`, which is `o(N)`. *Why it might matter*: the `+3` is small next
   to `m^2`, so this is worth about `2` out of `275` today, but it becomes
   the dominant term if the Mertens band ever reaches its classical `4`
   (`4^2 + 4 + 3 = 23`, of which `3` is 13 percent).
   *First step*: replace the `card_filter_le` step in `first_moment_lower`
   by a Chebyshev-type bound on `pi(N)`, e.g. via
   `Chebyshev.psi_le_primeCounting_mul_log` read backwards, and check
   whether the resulting `L`-dependence still collapses under `1 <= L`.

4. **`sum_inv_mul_sqrt_le` is stated from `n = 1`, where it is tight, and
   used from `n = 2`, where it is not.** *What*: the hunt subtracts the
   `n = 1` term at the call site rather than restating the lemma.
   *Why it might matter*: any future consumer will hit the same friction, and
   the `n = 2` form is the one the mathematics wants.
   *First step*: add `sum_inv_mul_sqrt_Ioc_one_le : sum_{2<=n<=N} <= 2 - 2/sqrt N`
   as the primary lemma and derive the existing one from it.
