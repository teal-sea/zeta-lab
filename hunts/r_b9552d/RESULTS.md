# Gap A is not a missing calculation, it is a forbidden constant

**Hunt `r_b9552d`, run 2, run id `113786a8-1f1c-4220-b772-15160a0274fa`,
2026-08-20.** Instrument: `probe.py` (`--quick` in seconds, full in a few
minutes). Data: `results.json` (and `results_quick.json`).

Run 1 of this hunt (`37fb06a9-...`, 2026-08-18) is preserved unchanged as
`RESULTS-37fb06a9.md`, `probe_37fb06a9.py`, `results_37fb06a9.json`,
`HANDBACK-37fb06a9.json`. Nothing it settled is re-derived here, and nothing
it said is contradicted. Two of its four threads have since been answered on
`main` by other sessions and this run starts from that:

* its **thread 1** (the G4 irregular-occupancy counterexample did not
  reproduce) was withdrawn on `main` in `a735965`: the recorded 0.1200 was a
  two-sided number compared against a one-sided one. There is no recorded
  counterexample to lattice extremality.
* its **thread 2** (the Cohn–Elkies certificate route, left open by a failing
  LP) was answered analytically rather than by LP, in `7efd506`: gap B of
  `hunts/frontier_math/LATTICE-EXTREMALITY-ROUTE.md` closes with the explicit
  majorant `v = K_1(0)·(sin(x/2)/(x/2))²`.

That leaves **gap A**, which the route document names as "where the work is":
the argument bounds the centre-gas row `J(T)` by `LP_v(rho)` only for
densities `rho >= 1/(2*pi)`, and says nothing below. This run asks what a
certificate would have to be to close the sparse side, and whether the family
that closed gap B can be it.

Grade: **measured** (double precision, no enclosures, no Lean). Section 1 is
an argument, not a formalised proof. Nothing here is evidence for or against
RH (`docs/08`); no claim here uses the reserved word.

---

## 0. Notation, in the route document's conventions

`f(s) = Dam(1,s) - Kpair(s) = -kappa(s) + K_1(s)^+` is the centre-gas
summand; `J(T) = (2/m) Σ' f(a_p - a_q + nP)` is the per-centre row;
`L := 2*kappa(0) - 4*c2(0) = 0.11433003938654052...` is its value on the
uniform `2*pi` lattice and the conjectured ceiling. A **certificate** is a
`g` with `g >= f` pointwise and `ghat <= 0` everywhere; it yields, for every
`P`-periodic configuration of density `rho`,

    J(T)  <=  B_g(rho) := 2*rho*ghat(0) - 2*g(0).

## 1. What a certificate that closes gap A must be, exactly

Suppose one `g` (independent of `rho`) proves `J(T) <= L` at **every**
density. Then:

* `B_g` is affine in `rho` with slope `2*ghat(0) <= 0`, so its supremum over
  `rho > 0` is the limit at `rho -> 0`, namely `-2*g(0)`. Hence
  `-2*g(0) <= L`.
* The `2*pi` lattice attains `J = L` at `rho = 1/(2*pi)`, so
  `B_g(1/(2*pi)) >= L`. But `B_g(1/(2*pi)) <= -2*g(0) <= L`.

Both inequalities therefore bind, and that pins four things at once:

> **(P)** `ghat(0) = 0`;  `g(0) = -L/2`;  `sup_x |g| <= (1/2*pi)∫|ghat| =
> -g(0) = L/2`;  and, from equality in the Poisson identity at the lattice,
> `ghat(j) = 0` for **every** integer `j` and `g(2*pi n) = f(2*pi n)` for
> every `n != 0`.

`ghat(0) = 0` is the whole of it: it makes `B_g` constant in `rho`, which is
exactly what "closes both sides at once" means. The dense-side argument of the
route document has `ghat(0) = -4.943`, and that negative slope is precisely
why it must give up as `rho` falls.

**A cheap necessary test falls out.** `g >= f` and `sup|g| <= L/2` force
`sup f <= L/2`. Measured:

| quantity | value |
|---|---|
| `L/2` | 0.05716501969327026 |
| `sup_{s != 0} f(s)` (scan on `(0,400]`, 4·10⁶ points) | **0.0187431348** at `s = 6.3974` |
| `sup f` on `[400, 8000]` (tail) | 3.88e-06 |
| smallest `s` with `f(s) > 0` | 5.7877 |
| `f(0)` | −0.8440563 |
| margin factor `(L/2)/sup f` | **3.04992** |

**The test does not fire.** A universal certificate is not excluded by it,
with a factor of 3.05 to spare. That is a positive finding about the route:
the obvious first obstruction is absent.

## 2. The family that closed gap B cannot close gap A, and by an exact amount

Take `g = -kappa + c·s` with `s(x) = (sin(x/2)/(x/2))²`, `shat = 2*pi*(1-|xi|)^+`,
the gap-B majorant. Then `ghat(0) = -khat(0) + 2*pi*c = -4*pi*c2(0) + 2*pi*c`,
so **`ghat(0) = 0` if and only if**

    c  =  2*c2(0)  =  1.6984559986366083...

and at that `c` the bound is not merely constant in `rho`, it equals the
lattice value: `B_g(rho) = 2*kappa(0) - 4*c2(0) = L` for every `rho`.
Verified across `rho·2*pi` from 0.0063 to 6.28: spread **6.66e-16**.

So gap A would close, for every density at once, at exactly one value of `c`.
Admissibility forbids that value:

| bound on `c` | closed form | measured | value |
|---|---|---|---|
| floor, `sup K_1^+/s` (needs `g >= f`) | `K_1(0)` | 0.9115647130952511 | 0.9115647130952531 |
| **cap**, `inf khat/shat` (needs `ghat <= 0`) | `cos²(√2/2)(1+cosh 1)` | 1.4698290136442997 | **1.4698290125473032** |
| **required for `ghat(0) = 0`** | `2*c2(0)` |, | **1.6984559986366083** |

    shortfall factor  =  2*c2(0) / (cos²(√2/2)(1+cosh 1))  =  1.15554665...
    shortfall absolute =  0.22862699...

The witness is explicit: at `c = 2*c2(0)`, `ghat(xi) = -khat(xi) + c·shat(xi)`
is **positive** on a whole interval below `xi = 1`, measured maximum
`+0.08390546` at `xi = 0.87493`: so the certificate condition fails there. The
route document already records the inequality `c < 2*c2(0)` as the reason
`LP_v` "stays decreasing". The reading it does not draw is the one that
matters here: *decreasing is the failure mode*. `c = 2*c2(0)` is the exact
boundary between a bound that decays with density and a bound that is uniform
in it, and the `ghat <= 0` constraint sits 15.55% below that boundary.

## 3. Why this is a statement about a family and not about one ansatz

The Fejér kernel is not one guess among many. Suppose `v = g + kappa` is any
majorant with `vhat` supported in `[-1,1]` (the band of `khat`, and the
band that makes the frequency sum finite). Then (P) forces:

* `v >= K_1^+ >= 0`, so `v >= 0`;
* `v(2*pi n) = K_1(2*pi n)^+ = 0` for `n != 0` (`K_1 < 0` at every non-zero
  lattice point, the route document's section 5 asymptotic
  `lim K_1(2*pi n)(2*pi n)² = -0.6277706` and `clip_is_idle_on_lattice`);
* `v` is of exponential type 1 and integrable.

A non-negative `L¹` function of type 1 factors as `v = |h|²` with `h` in the
Paley–Wiener space of type 1/2 (Fejér–Riesz / Krein), and `h` must vanish at
`2*pi n` for `n != 0`. But `{2*pi n}` is the *critical* sampling set for that
space, so `h(x) = Σ_n h(2*pi n)·sinc((x - 2*pi n)/2) = h(0)·sin(x/2)/(x/2)`,
whence `v = c·s`. **Up to the constant, the Fejér kernel is the only
band-limited candidate**, and section 2 shows the constant it needs is
forbidden.

Grade this argument honestly: the factorisation and sampling steps are
standard but are quoted here, not proved, and `probe.py` checks none of them,
it checks only the two constants that make them bite. What it establishes,
subject to that, is that gap A is closed to the entire band-limited
rectification family, not just to the ansatz that closed gap B. **Any
certificate that closes gap A must put Fourier mass outside `[-1,1]`**, where
(P) requires `ghat <= 0` and `ghat(j) = 0` at every integer, while `v` stays
non-negative with double zeros on `2*pi Z\{0}`. That is a sharply specified
target and it is the concrete shape of the remaining work.

## 4. What the family does give: a uniform bound at every density

Nothing above stops one from spending the *largest admissible* `c` instead of
the smallest. At `c = cos²(√2/2)(1+cosh 1) = 1.4698290`, which is admissible
(it clears the floor 0.9116 and meets the cap with equality only in the limit
`xi -> 1`), `B_g(rho) = LP(rho) + 2c(2*pi*rho - 1)` is still decreasing, so
its value at `rho -> 0` bounds every density:

> **For every periodic configuration, at every density,**
> `J(T) <= 2*kappa(0) - 2*cos²(√2/2)(1+cosh 1) = **0.5715840115651507**`,
> which is `4.99942 × L`.

That is a factor 5.0 away from the conjectured ceiling and so proves nothing
about extremality, but it is the first bound in this route that holds on the
sparse side at all. The route document's own sparse-side illustration is
`+2.15` at `rho·2*pi = 0.4`, computed at `c = K_1(0)`; the same formula at
the largest admissible `c` gives `0.4573` there. Gap A's numerical distance
shrinks by 4.7×, and its *structural* distance does not shrink at all: the
slope is still negative, so no choice of `c` survives `rho -> 0` with the
truth.

Configurations measured against all three (full run, `N = 1500` periods;
`--quick` at `N = 400` agrees to six decimals on every shared row):

| configuration | `rho·2*pi` | `J` | family bound at `c_cap` | `L` |
|---|---:|---:|---:|---:|
| uniform `2*pi` lattice | 1.0000 | +0.114330 | 0.1143 | 0.1143 |
| lattice, spacing `1.5·2*pi` | 0.6667 | −0.121634 | 0.2667 | 0.1143 |
| lattice, spacing `2·2*pi` | 0.5000 | +0.026676 | 0.3430 | 0.1143 |
| lattice, spacing `4·2*pi` | 0.2500 | +0.006570 | 0.4573 | 0.1143 |
| lattice, spacing `10·2*pi` | 0.1000 | +0.001047 | 0.5259 | 0.1143 |
| one vacancy in 3 | 0.6667 | +0.063027 | 0.2667 | 0.1143 |
| one vacancy in 5 | 0.8000 | +0.086797 | 0.2058 | 0.1143 |
| tight pair, period `20·2*pi` | 0.1000 | −1.666859 | 0.5259 | 0.1143 |
| cluster of 3, period `30·2*pi` | 0.1000 | −3.312211 | 0.5259 | 0.1143 |
| random, `m = 5`, `P = 34.8` | 0.9019 | −0.833930 | 0.1592 | 0.1143 |
| random, `m = 4`, `P = 37.8` | 0.6652 | −1.036705 | 0.2674 | 0.1143 |
| random, `m = 2`, `P = 56.9` | 0.2208 | −0.013986 | 0.4706 | 0.1143 |
| random, `m = 3`, `P = 125.4` | 0.1504 | −0.037941 | 0.5028 | 0.1143 |
| random, `m = 2`, `P = 62.0` | 0.2026 | −0.010973 | 0.4789 | 0.1143 |
| random, `m = 2`, `P = 115.2` | 0.1091 | −0.007462 | 0.5217 | 0.1143 |

Zero violations of `L`, zero violations of the uniform bound. The sparse
configurations are not close to threatening: clustering pays `f(0) = -0.844`
per ordered coincident-ish pair and dilution pays almost nothing, so `J`
falls away from `L` in both directions off the critical lattice.

## 5. Controls

| control | result |
|---|---|
| `k1_vec` (numpy) vs `gram_form.kernel(1,·)` (scalar `cmath`) | max diff **4.3e-19** |
| `J` on the `2*pi` lattice vs the closed form `L` | −7.1e-09 (truncation) |
| `sup f <= L/2` test on the honest `f` | does not fire (correct) |
| same test on `f` inflated by 3.05× | **fires** (planted fault caught) |
| cap test rejects `c = 2*c2(0)` | yes |
| cap test accepts `c = K_1(0)` | yes |
| `c_cap` and `c_floor` re-measured vs their closed forms | agree to 1.1e-09 and 2.0e-15 |

The inflation ladder is the honest statement of this run's power: the
necessary condition of section 1 has a 3.05× margin, so it would catch a
kernel three times more positive than the real one and nothing weaker. It is
a real test that happens to pass, not a test that cannot fail.

## 6. What this settles and what it does not

* **Does not** close `k >= 3`, T1, or lattice extremality. Gap A stands.
* **Does not** produce a certificate. It produces the specification of one,
  and a proof-shaped reason the obvious family cannot supply it.
* **Does** pin every constant a universal certificate must hit: `ghat(0) = 0`,
  `g(0) = -L/2`, `sup|g| <= L/2`, `ghat` vanishing on `Z`.
* **Does** show the first necessary condition passes with margin 3.05, so the
  route is not dead.
* **Does** show the gap-B family misses the required constant by exactly
  1.15554665×, with an explicit frequency-domain witness at `xi = 0.875`, and
  argues the miss is the whole band-limited family's, not one ansatz's.
* **Does** give the first sparse-side bound in this route: `J <= 0.5715840`
  at every density, `4.99942 × L`.

**On the harness loop.** This row's brief carries the standing instruction to
record an outcome in a ledger under `harness/departments/`. Checked, and
reported rather than performed: `harness.review.standing_reasons` is empty for
both ledger claims (`blockpos-0.672529`, `urms2-0.51`), `graveyard.unguarded`
is empty, and `guards.undemonstrated` names one item, `tests/test_doors.py`,
which is not this row. This task came from the operator roster
(`operator:2026-08-17:k-ge-3-gas-split`), not from a ledger generator, and the
review ledger's own docstring says a frontier-math thread is entered "when its
subject lands, not while it moves", lattice extremality moved four times in
the last two days. So **no ledger entry was made, deliberately**, and the
generator output above is the record of the check. `scripts/70_lab_state.py`
runs clean.

## Loose threads

1. **The out-of-band certificate.** *What:* section 3 says any `g` closing
   gap A must have `ghat` supported beyond `[-1,1]`, non-positive there,
   vanishing at every integer, with `v = g + kappa >= 0` double-zero on
   `2*pi Z\{0}`. Nothing here says such a `g` exists or does not.
   *Why it might matter:* it is the entire remaining content of lattice
   extremality, which is the gas half of T1, which is blocker 2 for `k >= 3`.
   *First step:* solve the LP `min -g(0)` over `g = -kappa + c·s + w` with
   `what <= 0` supported on `[1, 3]` and `w` free-sign in space, on a grid
   sampling `f` at `2*pi Z` exactly, and see whether `-g(0)` can reach `L/2`.
   Run 1's thread 2 conditioning advice applies: concentrate the space grid on
   `[5.8, 60]` where `f > 0`, and rescale the measure by cell width.

2. **The 4.99942 coincidence.** *What:* the uniform bound of section 4 is
   `4.99942 × L`, which is 5 to four figures and is not 5. *Why it might
   matter:* if it were exactly 5, `2*kappa(0) - 2c_cap = 5(2*kappa(0) -
   4*c2(0))` would be a closed-form identity among `c2(0)`, `kappa(0)` and
   `cos²(√2/2)(1+cosh 1)`, and identities among those three are what the
   whole route is made of. *First step:* evaluate both sides at 50 digits
   with mpmath; the difference is 6.6e-05 at double precision, so 50 digits
   settles it in one line. A near-miss is the likely answer and is worth
   recording as one so nobody chases it twice.

3. **Uniqueness under a uniform certificate.** *What:* the route's uniqueness
   argument (section 4 of the route document) needs `ghat < 0` strictly on
   `(0,1)`. A gap-A certificate has `ghat(j) = 0` at every integer and
   `ghat(0) = 0`, so the Newton step must be re-derived, the strictness it
   uses is gone at `xi -> 0`. *Why it might matter:* extremality without
   uniqueness is still enough for T1, so this is a completeness question, not
   a blocker; but a proof written without noticing would be wrong.
   *First step:* redo section 4 assuming only `ghat < 0` on `(0,1)` open and
   `ghat(0) = 0`, and check whether `A_j = 0` for `1 <= j <= m-1` still
   follows.

4. **Depth.** Run 1's thread 4 is untouched and still open: everything here
   is `y = 1/2`. `LATTICE-EXTREMALITY-ROUTE.md` is stated at `y = 1/2` too,
   so the whole certificate analysis inherits it. *Why it might matter:* T1
   is an obligation for all `y` in `(0, 1/2]`. *First step:* recompute
   `c2`, `khat` and `c_needed = 2*c2(0)` at `2y = 0.5` and `2y = 0.2`: the
   `kappa` in play is `y`-dependent, so both the required constant and the
   cap move, and whether they move together decides if this section is one
   calculation or a family of them.
