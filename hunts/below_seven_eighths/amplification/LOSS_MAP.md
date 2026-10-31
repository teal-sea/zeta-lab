# Lemma 17.6, sixth-power amplification: its price and its loss map

**Hunt #136, lane b78-amplification, 2026-10-21. Lane output, unreviewed by any person.
Nothing here is a result until the case log in `hunts/README.md` says how the hunt ended.**
Files: `price.py` (the exact model: closed forms, an exact LP, an exact decision procedure
on the whole bin rectangle, the enumerations), `test_price.py` (pins every fraction and
decimal on this page and on `guo_h11.md`), `guo_h11.md` (Guo's Hypothesis 11.1).

Grades as in `MISSION.md`: *cited* (a line of a source file, quoted, the file's SHA-256
checked by `price.verify_citations`), *derived* (exact arithmetic here, pinned by a test),
*inferred* (a reading or standard step no computation here checks), *measured* (float). A
composite claim takes the grade of its weakest step. Nothing here bears on real part 1/2.
**No improvement of the half-plane is claimed.** Every abscissa below is the best target of a
stated comparison system with a stated, hypothetically changed input; the lemmas that supply
the inputs are not checked.

Sources: the 7/8 preprint `paper.tex` (16,677 lines, SHA-256 `42a5ee0f...a6a3`); Liu,
arXiv:2610.26835v1 `number_fields_v2.tex` (`c55f17c6...626f`); Guo's section 11 and Baier and
Young as in `guo_h11.md`; hunt #134's `probe.py` read from
`origin/claude/hunt-134-seven-eighths-pin` with `git show`.

## Summary

1. **What the lemma says and where it enters.** For sixth-power-free rows of norm about `U` and
   the inverse polynomial `M_u` of length `D = U^r`, `sum_u |M_u|^2 << U^(e(r) + eps)` with
   `e(r) = max{1, (1 + 5r)/6}` (lines 12362 to 12389, cited). The Part II row counts use it only
   through the long count `L(t) = 1 - delta + (alpha - delta)(t - 1)`, `alpha = 5/6` (lines 15101,
   15208), and only on `1 <= r <= t <= 3/2` (cited, line 15303). Write `e(r) = max{1, e0 + alpha r}`:
   the paper's family moves the slope with `e0 = 1 - alpha`; a mean square valid for `H >= D^theta`
   feeds the same proof and gives `alpha = 5 theta/6`, `e0 = 1/6` (derived).
2. **At hunt #134's optimum** (the paper's row counts, total accounting, geometry free) the best
   target is `(1507 - 2 sqrt 921)/1653 = 0.8749570698`, and (derived, exact in `Q(sqrt 921)`)
   `d(target)/d(alpha) = 7414/303601 - 181690 sqrt(921)/279616521 = 0.0047006135`,
   `d(target)/d(eta) = (sqrt 921 - 478)/551 = -0.8124356047` for an improvement `eta` of the direct
   exponent `l_x/2 + b/12`. Per unit, the direct exponent is worth 172.8360798139 times the slope.
   **To reach 0.8748087** the slope must drop to `144263243506939/179612914571532 = 0.8031897030`
   in hunt #134's system and in the second-step frame P2, and to `0.8028731275` with the paper's
   side conditions as printed (frame P1, where the intermediate rows bind first); or the direct
   exponent must improve by `eta = 0.0001826235` at the paper's slope.
3. **Inside Liu's refined system**, reconstructed exactly (his critical polynomial, his `ell*`,
   his `kappa` quartic and his `B_flat` quartic are reproduced, derived), the fixed point is
   `B_flat = 0.8748866470` and, with the feedback through `kappa = 2B - 1`,
   `dB/d(alpha) = 0.0073713973`, `dB/d(eta) = -0.7727666039`. **To reach 0.8748087** the fixed point
   needs `alpha = 0.8229295767` (exact rational), but there `kappa = 0.7496174000`, below the range
   `7497/10000 <= kappa <= 3/4` of Liu's admissibility; inside that range a step at
   `kappa = 7497/10000` needs `alpha = 0.8229135719`.
4. **To reach 13/15.** In hunt #134's system the slope must go to `alpha = 0`: the target exceeds
   13/15 for every `alpha > 0` and tends to it (derived). In the threshold family `theta = 2/3`
   attains it, because then `e(r) = 1` on the whole detector range and the counts are the ideal
   `1 - delta`. With the paper's side conditions as printed no `alpha` reaches it: the ceiling is
   `84031/96156 = 0.8739028246` (frame P1) or `368153/422028 = 0.8723425934` (frame P2). Liu's system
   with its admissibility as stated stops at `437/500` (one step at `kappa = 3/4`, decided at
   `alpha = 1/2` and `alpha = 0`), while Liu's endpoint alone, which has no bins below `delta = 1/8`,
   reaches 13/15 as soon as `alpha <= 1/8` (derived).
5. **Loss map.** Every step of the lemma's proof either loses no exponent or is tight relative to
   the inputs it uses (section 3). The slope is `(1 - 1/6) theta_0`: the `1/6` is forced, because the
   only multipliers that leave every row character unchanged are sixth powers (exact enumeration),
   and `theta_0 = 1` is the first width condition of Lemma 17.1, tight for every mean value valid for
   arbitrary coefficients and open for the Moebius coefficients. **No slack step was found, so this
   lane proposes no sharper input.**
6. **The only door through this lemma is `theta_0`, and it is a zero-free-region door.** A raw
   moment valid for `H >= D^theta` gives, through Lemma 17.6 at `U = 1` alone, a zero-free half-plane
   `Re s > 1/2 + 5 theta/12` for every fixed `L(s, nu)` (derived from the statement; Mellin step
   inferred). Below `theta = 0.8898838649` that trivial route already beats the whole Part II
   assembly (frame P0). Guo's Hypothesis 11.1 is `theta = 99/100` (`guo_h11.md`).
7. **A side correction to hunt #134.** At the paper's geometry, hunt #134 reports the endpoint
   margin `7/30672`; that is the value at `delta = 79/204`, where the paper's completed square is
   centred. The minimum over the rectangle lies between `228147/10^9` and `228148/10^9` (derived,
   exact decision), a little lower. The paper's printed bound `49/440640` is unaffected.

## 1. The lemma and its use, read

- `eq:raw-moment` (lines 12345 to 12358, cited): Lemma 17.1 at `Z = H`, `m = 1`, no slots, gives
  `sum_{q_u <= H} |M_u(D; W)|^2 << H (HD)^eps` for `H >= D^(1+c)`. Lemma 17.1 needs
  `r + 2z <= m - c_1` and `2r + 8z <= 3m - c_2` (line 9254); with `z = 0`, `m = 1` the first is the
  binding one, `r = log_H D < 1`.
- The proof (lines 12391 to 12469): scale supremum by a Sobolev inequality; at least `c_S P`
  amplifiers `a` with `q_a <= P`; the exact column identity
  `M_u(D) = sum_{d | rad a} mu(d) psi_u(d) q_d^(-1/2) M_{u a^6}(D/q_d)` (line 12428), from
  `psi_{u a^6}(m) = psi_u(m) 1_{(m,a)=1}` (line 12420); coefficient mass `d(a) << P^delta` (line 12430);
  injectivity of `(u, a) -> u a^6` without coprimality (line 12443); `q_{u a^6} << U P^6 << H`; then
  `sum_u |M_u|^2 << (H/P)(UD)^eps = U^(1/6) H^(5/6) (UD)^eps` (line 12449) with
  `H = max(2U, D^(1+c))`, `P = (H/U)^(1/6)` (line 12369).
- The use (Proposition 19.1, lines 15249 to 15310; endpoint, lines 15928 to 15992): for `r >= 1`,
  Markov's inequality on the amplified moment gives the count `1 - alpha + (alpha - delta) r`
  (line 15289); with `r <= t` this is `L(t)`; balancing `L(t)` against the short count
  `R_short(t)` (line 15206) gives `R_* = 1 - delta + (alpha - delta) delta P_x/(2 J)` (line 16019).
  For a general law `e(r) = max{1, e0 + alpha r}` the same minimisation gives the excess
  `R_* - (1 - delta) = delta P_x (delta_e - delta)_+ / (2 J)` with `delta_e = 3 alpha + 2 e0 - 2` and
  `J = (alpha - delta) D_x + delta P_x` (derived; `price.excess`, checked against a direct
  minimisation over `t` at 380 bin points for four laws).
- In the paper `alpha = 5/6` coincides with `2(11/12) - 1` but plays a different role (hunt #134):
  the bins satisfy `delta <= kappa` (line 15503); `alpha` is only the amplification slope.

## 2. The price

### 2.1 The comparison systems, so that they can be rebuilt

**System P** (`price.SystemP`), variables `(ell, M, b)`, objective the target
`5/6 + (M - 2 ell)/12 - eta` (hunt #134's closed form of `1 - h/6 + b/12`, lowered by `eta`). An
improvement `eta` of the direct exponent lowers the target by `eta` at fixed geometry and raises
every high exponent by `eta`, since they are measured against `Z^C(sigma_0)` (lines 15694 to 15696).
Constraints, every one affine in `(ell, M, b)` at a fixed bin:

- endpoint `-E_* = -C_0 + delta(ell + b)/2 - ell x delta - h X >= 0` on the bin rectangle, with
  `C_0 = 1/2 + ell/2 - 3M/4 + b/6 + eta`, `h = 1 + ell - M/2 + b/2`, `X` the excess above, `c = 4/9`
  (hunt #134);
- `M + ell <= 1`; `2M >= 1 + 3 ell` (hunt #134's total accounting, inferred there); `b >= 0`;
  `8b <= 3(M - 2 ell)` (Gram); `l_x > ell`.

Frame **P0** is hunt #134's: bins `0 <= delta <= 5/6`, `0 <= x <= 1/2`. Frame **P1** adds the paper's
side conditions as printed: bins from `delta = 1/50`, the floor bin at `delta_0 = 1/50` with count 1
(line 15847), the intermediate rows `d <= 1/2` with `R = 76/75 - 2 delta/3` up to `delta = 5/6`
(lines 16146 to 16165), the supply `ell/h > 7/37` and `5 ell > h`, the small rows. Frame **P2** is P1
with every bin ceiling at `delta <= 3/4`, the bins of a step justified by `beta_* <= 7/8` (as Guo and
Liu use them).

**System L** (`price.SystemL`), Liu's refined system: variables `(ell, b)` with `M = 1 - ell`,
target `11/12 - ell/4 - eta`, endpoint (lines 8987 to 8994)
`E = C_0 + delta/2 + delta x {ell + c_kappa (h/4 - l_y/2)} - (3h/4)(1 - R_kappa) + eta <= 0` on
`1/8 <= delta <= 3/4`, `C_0 = -1/4 + b/6 + 5 ell/4`, `c_kappa = 1/(3 kappa)`, with `R_kappa` built from
the same law. Frame **L0** has only `b >= 0` and `ell <= 1/5` besides; frame **L1** adds
`delta <= 5/6`, the small-`delta` endpoint (line 8999) and admissibility (1), (2), (4)
(lines 9010 to 9023). The moment parameter is either fixed or tied at the fixed point
`kappa = 2B - 1` of Liu's chain.

**Exact LP and decision.** `price.sandwich` brackets the best target: an exact LP on a finite set
of bins (a float LP proposes the basis; optimality is decided in rationals by primal feasibility
of every row and nonnegative dual weights), cuts added at the worst bin until no float violation
is left (lower end), and a nearby rational geometry whose constraints are decided on the whole
rectangle by exact interval subdivision in `x` with the `delta`-quadratic minimised exactly (upper
end). Every sandwich below has width under `10^-12`.

### 2.2 At hunt #134's optimum

Only the endpoint at `x = 1/2` binds, at the bin where the endpoint does not depend on `b`:
`X(delta, 1/2) = delta - 1/3`, i.e. `288 delta^2 - 588 delta + 185 = 0` at the paper's law (derived).
Closed forms (derived, exact in `Q(sqrt 921)`):

| quantity | exact | value |
|---|---|---|
| critical bin `delta_c` | `(49 - sqrt 921)/48` | 0.3885837123 |
| `ell` | `11/551 + 8 sqrt(921)/1653` | 0.1668383875 |
| `b` | `-4/29 + 230 sqrt(921)/26709` | 0.1234054370 |
| target | `(1507 - 2 sqrt 921)/1653` | 0.8749570698 |
| endpoint multiplier `mu` | `(73 + sqrt 921)/551` | 0.1875643953 |
| `d target / d alpha` (`e0 = 1 - alpha`) | `7414/303601 - 181690 sqrt(921)/279616521` | 0.0047006135 |
| `d target / d eta` | `(sqrt 921 - 478)/551` | -0.8124356047 |
| `d target / d theta` (`alpha = 5 theta/6`, `e0 = 1/6`) | `22490/910803 + 99110 sqrt(921)/279616521` | 0.0354493305 |

The target is B_alg of Guo and Liu (`FOLLOWUPS.md`), here as the optimum of hunt #134's system.
By the envelope theorem `d target/d alpha = mu h dX/d(alpha)` with `dX/d(alpha) = (delta P_x)^2/(2 J^2)`
at the critical bin, and `d target/d eta = mu - 1`; finite differences of the closed form agree.

In regime A the target is `11/12 - (5 - 6 delta)/(36(1 + 2 delta))`, `delta` the root of
`48 delta^2 - (90 alpha + 23) delta + 37 alpha = 0`, so a rational target gives a rational `delta`
and then a rational `alpha`: the `alpha` for 0.8748087 is `144263243506939/179612914571532`, and for
Xu and Sang's 0.8748867 it is 0.8186903585 (derived). The latter, and the ceiling `84031/96156`
below, agree with this hunt's assembly lane (`ASSEMBLY.md`, an independent implementation, read
uncommitted on 2026-10-21).

### 2.3 Inside Liu's refined system

The reconstruction (derived): from Liu's endpoint with the law left free, `dE/db = 0` at
`x = 1/2` is `X = delta (1 + c_kappa/6) - 4/9`, whose numerator is `-2 cr(delta, kappa)` with Liu's
`cr` (line 9694); there `E = -5/12 + delta/2 + ell (3/4 + delta (1 + c_kappa)/2)`, so
`ell* = (5 - 6 delta)/(9 + 6 delta + 6 c_kappa delta)`, which equals Liu's `ell*(delta, kappa)` modulo
`cr`; eliminating `delta` from `cr = 0` and `11/12 - ell*/4 = (1 + kappa)/2` gives the factor
`16686 kappa^4 - 27405 kappa^3 + 9936 kappa^2 + 1290 kappa - 275` (line 9721), and the root brackets
Liu's `B_flat` quartic (line 8863). With that check the price, with the law generalised:

| quantity | fixed point (chain limit) | one step at `kappa = 3/4` |
|---|---|---|
| `kappa` | 0.7497732941 | 3/4 |
| target | 0.8748866470 | 0.8748869894 |
| critical bin `delta_c` | 0.4693448587 | `(1519 - sqrt 715621)/1434` |
| `ell`, `b` | 0.1671200785, 0.0865349593 | |
| `lambda = dE/d ell` at the critical bin | 1.0890028233 | |
| `d target / d alpha` | 0.0073713973 | 0.0073499805 |
| `d target / d eta` | -0.7727666039 | -0.7704271941 |
| `d target / d theta` | 0.0436097239 | |

`dF/d kappa = 0.0015104302` at the fixed point (Liu bounds it by `0.0065/4`, line 9968), so the
feedback factor `1/(1 - 2 dF/d kappa)` changes the one-step price by under one percent. The slope
is worth 1.57 times as much here as in system P. The counts enter Liu's endpoint with weight
`3h/4` instead of `h`, but its `ell`-slope `lambda = 1.0890028233` is smaller than system P's
`3/4 + 3 delta_c/2 = (73 - sqrt 921)/32 = 1.3328755684` (both derived; which effect dominates is a
reading of the formulas, inferred).

What `alpha` must reach for 0.8748087 (derived; at the fixed point `kappa = 2 L - 1` is rational,
the critical bin is rational and the critical equation is linear in `alpha`):

| route | `alpha` | note |
|---|---|---|
| fixed point | 0.8229295767 | needs `kappa = 3748087/5000000 = 0.7496174000`, below Liu's `7497/10000` |
| one step at `kappa = 7497/10000` | 0.8229135719 | inside Liu's admissibility (decided exactly at `alpha` plus and minus `10^-9`) |
| one step at `kappa = 3/4` | 0.8228554917 | |

and the direct exponent alone at the paper's slope: `eta = 0.0001008670` (fixed point).

### 2.4 The price curve

Best target, exact sandwiches (10 decimals; both ends agree to `10^-12`), paper's law `e0 = 1 - alpha`:

| `alpha` | P0 (hunt #134) | P1 (as printed) | P2 (bins `<= 3/4`) |
|---|---|---|---|
| 5/6 | 0.8749570698 | 0.8749570698 | 0.8749570698 |
| 41/50 | 0.8748931216 | 0.8748931216 | 0.8748931216 |
| 4/5 | 0.8747921786 | 0.8747946020 | 0.8747921786 |
| 3/4 | 0.8745098039 | 0.8745531405 | 0.8745098039 |
| 2/3 | 0.8739158273 | 0.8741661871 | 0.8739322471 |
| 1/2 | 0.8722266776 | 0.8739028246 | 0.8727977179 |
| 1/3 | 0.8704255897 | 0.8739028246 | 0.8723425934 |
| 1/100 | 0.8667826048 | 0.8739028246 | 0.8723425934 |
| 0 | 13/15 | 84031/96156 | 368153/422028 |

At `alpha = 3/4` the P0 value is `223/255` (the critical quadratic has a rational root there,
`delta_c = 37/96`; derived). Active sets: P0 is still in regime A at `alpha = 2/3` and sits on
`b = 0` by `alpha = 1/2`; P1 leaves regime A when the intermediate rows at `delta = 5/6` bind
(between 41/50 and 4/5), and from `alpha = 1/2` down sits at the vertex of the intermediate rows,
the floor bin and `M + ell <= 1`, which involves no row count; P2 does the same with the ceiling
`delta <= 3/4`, from `alpha = 1/3` down.

### 2.5 What alpha must reach

| level | P0 | P1 | P2 | L (fixed point) |
|---|---|---|---|---|
| 0.8748087 | 0.8031897030 | 0.8028731275 | 0.8031897030 | 0.8229295767 |
| 13/15 | 0 (limit, not attained) | unreachable | unreachable | unreachable as stated (`437/500`); 1/8 in L0, which has no bins below `delta = 1/8` |

P1's entry is the exact bracket `[336749397/419430400, 2155196141/2684354560]` from bisection on
sandwiches; the others are exact. The target is nondecreasing in `alpha` (every bin's excess
grows with it, `dX/d alpha = (delta P_x)^2/(2 J^2) > 0`), which is what makes the brackets valid.
For 13/15 in P0: the unique minimiser of the target over the floor condition, `M + ell <= 1` and
`b >= 0` is `(ell, M, b) = (1/5, 4/5, 0)` (hunt #134), and there `-E_*(delta, 1/2) = -h X < 0` for
every `0 < delta < alpha`; so the target exceeds 13/15 whenever `alpha > 0` (derived), and the curve
shows it tending to 13/15.

## 3. The loss map

Each step of the proof of Lemma 17.6 (and of the two places its output is used), with what it
loses and a verdict. "Tight" means a configuration consistent with every input the step uses
attains the loss; "no exponent" means only `(UD)^eps`, logarithms or constants are lost.

| step (paper lines) | loses | verdict, and the configuration or reason |
|---|---|---|
| 1. `raw-moment` from Lemma 17.1, `Z = H`, `m = 1`, no slots (12345 to 12358, 9254) | the bound is diagonal, `H`; the range `H >= D^(1+c)` is the binding input | bound: no exponent. Range: **tight for every mean value valid for arbitrary coefficients**: with `c_n = 1` the row `u = 1` alone contributes `N^2`, so the constant is at least the number of columns `N`, about `D` (derived, one line). For the Moebius coefficients the range is **open**; extending it is Guo's Hypothesis 11.1 type and has zero-free-region strength (section 4) |
| 2. scale supremum, Sobolev in `log D'` (12392 to 12408) | `(HD)^eps`, `O(log D)` intervals | no exponent |
| 3. at least `c_S P` amplifiers (12410 to 12414) | a constant | no exponent; exact count of ideals prime to 6 with norm at most `10^4`: ratio 0.3027 to the norm bound |
| 4. **the sixth power**: `psi_{u a^6} = psi_u` off `a` (12416 to 12420) | sets `P = (H/U)^(1/6)` | **tight**: the multipliers that fix every row character are the sixth powers. Exact enumeration: of the 18144 elements of `Z[w]` of norm at most 5000, the 3 sixth powers have trivial sextic symbol at every split prime below 3000 not dividing them, and every other element has a split prime below 3000 with a nontrivial symbol (derived); for all norms by Kummer theory and Chebotarev (inferred, standard). Units and `S`-units change the row character by a fixed character, absorbed in `nu`, and add at most logarithmically many multipliers |
| 5. column identity, mass `d(a) << P^delta` (12424 to 12435) | `P^(2 delta)` | no exponent |
| 6. injectivity of `(u, a) -> u a^6`, `q_{u a^6} << H` (12437 to 12444) | nothing | exact |
| 7. **positivity**: the `~U P` image rows are bounded by the mass `H` of the whole ball (12444 to 12449) | the whole `5/6` | **tight relative to its inputs.** (i) As a max-plus LP in exponents: putting all of the ball's mass on the rows of norm `U` and their sixth-power multiples satisfies the raw moment at every radius `H' >= D^(1+c)` and attains `(1 + 5 h_0 r)/6`, dual and primal equal (derived at `r = 1, 9/8, 3/2`: 1, 53/48, 17/12 at `h_0 = 1`). (ii) In the actual family at `U = 1` the configuration is real: the rows `u = a^6` all carry `M_1`; the bound `|M_1(D)|^2 << D^(5/6)` is attained in the exponent when some `L(s, nu)` has a zero with real part 11/12 (an Omega result from the explicit formula, inferred), and the raw moment does not exclude such a zero, since the rows `a^6` then carry `H^(1/6) D^(5/6) <= H` (derived). The pointwise bootstrap bound `D^kappa` does not cut the configuration either: `(D/U)^(5/6) <= D^kappa` on `r <= 3/2` (derived) |
| 8. `H = max(2U, D^(1+c))`, `c -> 0` (12369, 12452, 15272 to 15281) | `5cr/6`, then 0 | optimal: `H/P = U^(1/6) H^(5/6)` grows with `H` |
| 9. rowwise test parameters (12457 to 12469) | `(1 + T_1)^A`, `T_1 = Z^tau`, small `tau` | no exponent |
| 10. use: Markov (15282 to 15291) | | tight relative to the second moment: `U^(e(r) - delta r)` rows at the threshold `U^(delta r)` |
| 11. use: the witness length taken at `r = t` (15302 to 15306) | | tight relative to the detector, which only gives `r <= t + O(eps)` |
| 12. use: the cutoff `t` (15963 to 15965) | | optimal, the minimum over `t` of the maximum of the two counts |

**Reading.** The exponent of the lemma is `alpha = (1 - 1/6) theta_0` with `theta_0 = 1`: step 4
fixes `1 - 1/6`, step 1 fixes `theta_0`, and step 7 is where the price is paid. Within the
information the proof uses (a ball mean value, sixth-power invariance, `|chi| <= 1`), no step has
slack: the max-plus configuration and, at `U = 1`, a hypothetical zero of a fixed `L(s, nu)` on
`Re s = 11/12` attain every bound. A smaller slope needs information the lemma does not read: how the
ball's mass is spread over its rows, or a mean value with fewer rows than columns. No slack
verdict is given, so no sharper input is proposed and the rival gate has nothing of this lane's
to test; it is applied to Guo's hypothesis in `guo_h11.md` section 4.

## 4. The threshold door, priced

The proof of Lemma 17.6 turns a raw moment valid for `H >= D^theta` into
`e(r) = max{1, 1/6 + 5 theta r/6}` (derived). Since only `r <= 3/2` matters, `theta <= 2/3` already gives
`e(r) = 1` there, the ideal counts `1 - delta` and, in P0, exactly 13/15. Best targets (exact
sandwiches) against the trivial route `1/2 + 5 theta/12` (Lemma 17.6 at `U = 1`):

| `theta` | P0 | P2 | L (fixed point) | trivial route |
|---|---|---|---|---|
| 1 | 0.8749570698 | 0.8749570698 | 0.8748866470 | 11/12 |
| 99/100 | 0.8745999251 | 0.8745999251 | 0.8744476409 | 73/80 |
| 19/20 | 0.8731166301 | 0.8731348699 | | 43/48 |
| 9/10 | 0.8711593646 | 0.8723425934 | | 7/8 |
| 5/6 | 0.8689826891 | 0.8723425934 | | 61/72 |
| 3/4 | 0.8672523186 | 0.8723425934 | | 13/16 |
| 2/3 | 13/15 | 0.8723425934 | | 7/9 |

The thresholds that reach 0.8748087 are `theta = 0.9958275690` (P0, P2; exact rational
`1292195122714234/1297609308016905`, bracketed by sandwiches at plus and minus `10^-9`) and
`0.9982147398` (Liu, fixed point, with the same `kappa` caveat as for `alpha`). The trivial route wins
below `theta` in `[0.8898838649, 0.8898838701]` in P0 and in `[0.8936222185, 0.8936222258]` in P2
(exact brackets): for a mean value that much stronger than the paper's, the Part II assembly is
no longer the best use of it.

**Information class.** A raw moment with `theta < 1` is a statement about the Moebius
coefficients that no orthogonality argument can supply (step 1), and by the trivial route it
carries a zero-free half-plane for every `L(s, nu)`. So this door is not inside the data the
current family reads: it needs zero-density or zero-free information about the row
L-functions themselves.

## 5. Controls

- Citations: every snippet in `price.CITATIONS` sits on its stated line of its pinned file, and
  every file's SHA-256 matches (measured).
- Reproductions: B_alg, `delta_c`, `ell*`, `b*` equal Guo's and Liu's closed forms
  (`FOLLOWUPS.md`); hunt #134's single-point bounds 5655673/6464057 and 44117/50422 lie below the
  optimum and the paper's geometry lies above it; Liu's `cr`, `ell*`, both quartics; Guo's
  identity, squares and bound; the paper's `R_*` (line 16019), Liu's `R` (line 8438) and Guo's
  `T_99` as cases of `price.excess`.
- Two exact decision procedures (interval subdivision in `x`, and exact root isolation of six
  polynomials) agree at the paper's geometry on the margins 0 and `49/440640` (accepted) and
  `1/4000` (refused); the subdivision procedure places the minimum there between `228147/10^9` and
  `228148/10^9`.
- Planted faults turn the tests red: a slope of `5/6 + 1/100` breaks the B_alg reproduction; the
  weight `h` in place of `3h/4` breaks Liu's `cr`; a margin above the true minimum is refused by
  the decision; an unpinned number on either page is caught.

## 6. Limitations

- The paper's lemmas, Liu's and Guo's inputs are taken at their printed exponents and are not
  checked. Total accounting of the row norm (needed for every abscissa below 7/8) is hunt #134's
  reading, inferred.
- The general-law forms of the counts and of Liu's endpoint are readings of displays written at
  fixed numbers, checked by reproduction at the printed values.
- Frames P1 and P2 inherit the paper's frozen side conditions (the intermediate count, the floor
  at 51/100); their ceilings are about those choices, not about the method.
- Liu's fixed point below `kappa = 7497/10000` uses his formulas outside the range where he
  verified his tangent family; that is flagged where it occurs.

## The doors

Candidate status: the price of the amplification slope and of the direct exponent at two
optima; parameter ranges as in section 2.1; proof status: exact arithmetic on transcribed
formulas, unreviewed.

### Active constraints at the optimum

1. **The endpoint at the critical bin, `x = 1/2`** (`delta_c = 0.3885837123` in P, `0.4693448587` in
   Liu), the only binding row family at both optima. Its multiplier is `0.1875643953` (P) and
   `0.2295678162` (Liu, `1/(4 lambda)`).
2. **`M + ell <= 1`**, the dual length, always active.
3. **Next to bind as `alpha` falls**: in P1 the intermediate rows at `delta = 5/6`; in P2 the
   intermediate rows at `delta = 3/4`; in P0 `b >= 0`; in Liu's system as stated, the principal
   region `B > 437/500` and the `kappa` range.

### The frozen-constant inventory

| constant | value | what relaxing it trades | trade shape |
|---|---|---|---|
| amplifier order | 6 | forced by the sextic symbol (step 4) | none |
| raw-moment threshold `theta_0` | 1 | the slope `5 theta_0/6`; needs zero-free-region information (section 4) | genuine, outside the current information class |
| `c` in `D^(1+c)` | `-> 0` | nothing left | none |
| detector window | `t <= 3/2` | only `e(r)` on `[1, 3/2]` matters, so a kink moved past `3/2` gives ideal counts | genuine: the target of any sharper mean value |
| intermediate rows | no slots, `t = 1`, `delta <= 5/6` | caps P1 at `84031/96156` and P2 at `368153/422028`, whatever `alpha`; Liu covers these rows by monotonicity in `d` instead (Liu, line 9592) | genuine, inside the current family |
| bin ceiling | `5/6` (P1) or `3/4` (P2) | P2 is what a second step from 7/8 may use | genuine, free |
| Liu's `kappa` range | `7497/10000` | the fixed point below 0.8748866470 needs smaller `kappa` | a re-verification, not a new estimate |
| Liu's principal region | `437/500` | the floor of Liu's system as stated; going below it needs new Euler-region margins (inferred) | genuine |

### The information class

- **Inside the current data:** re-choosing geometry, the bin ceiling, Liu's `kappa` range and
  the intermediate-row treatment. These move the abscissa only through the endpoint, at the
  prices above.
- **Inside the current family, better inputs:** the direct exponent, worth 172.8360798139 times
  the slope per unit at hunt #134's optimum, and the row-count inputs, which this hunt's other
  lanes price. The amplification slope itself is worth 0.0047006135 per unit there.
- **Reading more:** any smaller slope from this lemma needs a mean value with fewer rows than
  columns for the Moebius coefficients, which is zero-free-region strength by itself.
