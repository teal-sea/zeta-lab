# First coordinated signed-correction candidate

Date: 2026-09-06.

**Status:** new calculation produced in the coordinating ChatGPT session after the reviewed baseline in PR #199. It is a finite candidate with exact feasibility checks and a rationally separated leading-constant comparison. It is **not independently reviewed**, not an LP-optimality theorem, not an asymptotic family, not a prime-counting record, not a result about total CHHL `E(N)`, and not an RH result.

## 1. Reviewed input

The starting point is the final combined-weight repair in
`hunts/prime_pair_error/frontier/2026-09-06/certificate_route_test/`, preserved on `main` by PR #198 and reviewed in open PR #199.

The review reports

- `M = 15`, `R = 100000`, mask `210`;
- leading constant
  `C = 1.048663663793220628233678560567956282917...`;
- finite coefficient mass `2641/3`;
- tail coefficient `15`;
- 537 stage-wise repairs, 411 distinct repair cells;
- global coverage from lifted-prefix coverage plus the tail invariant.

The fixed once-per-new-prime continuation has a documented ceiling, so this pass does **not** add the next primes in the same way.

## 2. What is changed

The previous construction chose five masked carries independently with unit amplitude,

`q = 17, 19, 23, 29, 31`,

and greedily repaired each stage before seeing later stages.

This pass instead chooses a **single block of amplitudes at once**. Candidate masked-carry starts are `q = 13,...,36`, including composite starts. Positive repair variables are allowed on the 411 distinct repair cells already present in the reviewed baseline. The LP minimizes the complete leading-constant contribution of these variables, including the extra tail shield required by the selected masked-carry amplitudes.

For a candidate start `q`, let `h_q` be the same mask-210 signed carry used by the existing construction. Full-period enumeration gives `max h_q = 3` for every `q=13,...,36`. For nonnegative amplitude `y_q`, the tail shield therefore pays `3 y_q` copies of the fixed repair weight.

The finite prefix problem is linear:

`W_0(t) - sum_q y_q H_q(t) + sum_n lambda_n B_n(t) >= 1`, `1 <= t < R`,

with `y_q >= 0`, `lambda_n >= 0`. Here `H_q` is the lifted masked carry and `B_n` the lifted nonnegative carry repair. The objective is the corresponding change in the weighted integral giving the leading constant.

The floating LP only proposes a vertex. Every nonzero coefficient reconstructs to a rational with denominator dividing 108, after which all prefix constraints and tail hypotheses are checked exactly with integer/rational arithmetic.

## 3. Candidate found

The selected masked-carry amplitudes are

| q | amplitude |
|---:|---:|
| 17 | 1 |
| 18 | 29/54 |
| 19 | 79/108 |
| 23 | 43/54 |
| 24 | 19/36 |
| 25 | 25/108 |
| 29 | 1 |
| 31 | 101/108 |
| 32 | 79/108 |

All other `q=13,...,36` receive zero.

The tail multiplier becomes

`H = 3 sum y_q = 701/36`.

The positive repair dictionary uses 172 of the 411 allowed cells. Its coefficient sum is `19471/108`.

The resulting finite floor-sum coefficient mass is

`56345/108 = 521.7129...`,

compared with the reviewed baseline's

`2641/3 = 880.333...`.

The lifted prefix minimum on every integer cell `1 <= t < 100000` is exactly `1`. The seed itself is negative at 640 cells; this is allowed by the reviewed combined-weight invariant.

## 4. Leading constant

The new leading constant is

`C_new = 1.047623931379267860580006972148025253682545...`.

The reviewed baseline is

`C_old = 1.048663663793220628233678560567956282917151...`.

The decrease is approximately

`0.00103973241395276765`.

This comparison is not accepted from the floating optimizer. `refine.py`'s rational logarithm enclosures are applied to the reconstructed coefficients and the tail term. The resulting intervals are disjoint in the favorable direction: the upper endpoint for `C_new` lies below the lower endpoint for `C_old`.

The change is not just a lower constant paid for by a larger finite mass: the finite coefficient mass drops by about 40.7%. The tail coefficient rises from `15` to `701/36 ≈ 19.4722`.

## 5. Early overcount

The reviewed baseline's early lifted weights and the joint candidate are:

| t | baseline | joint |
|---:|---:|---:|
| 18 | 2 | 79/54 ≈ 1.463 |
| 19 | 2 | 245/108 ≈ 2.269 |
| 20 | 3 | 3 |
| 21 | 2 | 2 |
| 24 | 2 | 53/36 ≈ 1.472 |
| 25 | 2 | 191/108 ≈ 1.769 |
| 32 | 2 | 137/108 ≈ 1.269 |

So this does not flatten every early excess. It demonstrates the intended phenomenon: several masked corrections cooperate, some composite starts enter, some old amplitudes shrink, and the **net** integral and repair mass improve after final coverage is enforced.

## 6. Complete certificate comparisons

The actual factorial certificate `B_N` and the sufficient envelope `U_N` are both lower than the reviewed baseline at the four recorded cutoffs.

| N | decrease in B_N | decrease in U_N |
|---:|---:|---:|
| 10^4 | 7.4010 | 8,829.97 |
| 10^6 | 1,011.18 | 18,129.62 |
| 10^8 | 103,713.40 | 130,601.85 |
| 10^12 | 1,039,731,988.21 | 1,039,780,545.82 |

These are high-precision evaluations of the exact rational coefficient vectors. The strict leading-constant comparison and finite feasibility are independently exact; the displayed factorial values are diagnostics, not directed-rounding interval claims.

## 7. Exact finite checks

`joint_correction.py` performs:

- all 99,999 lifted prefix cells through `R-1`;
- full-period enumeration for every candidate masked carry `q=13,...,36`, totaling 3,390,240 period positions, with maximum exactly 3 in each case;
- exact balance of the final finite floor sum;
- rational reconstruction with denominator at most 108;
- rational logarithm enclosures proving `C_new < C_old`;
- complete sufficient-bound comparisons at `10^4,10^6,10^8,10^12`.

The reviewed tail proof carries over: the starting seed is nonnegative, each selected `h_q <= 3`, every finite repair is nonnegative, and `(701/36) W_*(t/R)` offsets the maximum aggregate subtraction for `t>=R`. Prefix coverage plus tail seed nonnegativity therefore gives global lifted coverage.

## 8. What this does and does not teach us

This is the first explicit example in this line where **coordinating the signed corrections instead of greedily repairing each stage lowers both the leading constant and the finite coefficient mass**.

It also shows that useful corrections need not be indexed only by primes: the selected block uses `18,24,25,32` as well as primes.

The restrictions are substantial:

1. positive repair variables were restricted to the 411 repair cells already appearing in the reviewed baseline;
2. masked-carry starts were restricted to `q=13,...,36`;
3. no exact LP-optimality theorem is claimed;
4. most importantly, no rule is proved showing how the gain scales when the window grows.

The next mathematical milestone is therefore **not another slightly larger LP**. It is to understand the structure of the selected block and derive a repeatable window/refinement rule with an explicit improvement-versus-complexity inequality.

## 9. Reproduce

From a Zeta Lab checkout containing the PR #198 baseline:

```bash
python joint_correction.py --output joint_results.json
```

Dependencies: numpy, scipy, mpmath and the repository's imported `certificate_route_test/refine.py`.
