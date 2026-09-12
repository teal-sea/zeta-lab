# Why the inherited repair dictionary freezes the weight at 20

Date: 2026-09-06 (local investigation date).

## Status and inputs

This is a **new analysis by the originating ChatGPT session**, separate from the
completed review on PR #200. It is not included in that review, has not been
independently refereed, and makes no novelty, LP-optimality, asymptotic-rate,
prime-counting-record, RH, or total-CHHL-E claim. No repository file or PR was
changed during this calculation.

The reviewed input is PR #200, head
`85a42e7c0c7dad8163dcab8d239bac5bb6fe1b38`, in `teal-sea/zeta-lab`.
Its `joint_correction_candidate/JOINT_REVIEW.md` reports that the candidate
survives; its `JOINT_CORRECTION.md`, script, and JSON are the unchanged three
members of `original_archives/joint_correction_candidate.zip`.
That ZIP has SHA-256
`828a4d85d471b51331b5f0a32c30818ccff4de95e9e4c91dbb836536376e8260`.

The construction and the proposed update use M=15, R=100000, and the mask 210.
`original_archives/certificate_route_test.zip` supplies the prior package and
its fixed starting and repair seeds. Nothing in these original archives was
rewritten. Extracted source inputs are under `inputs/`.

## 1. A structural statement about the full permitted LP family

Define

    b_n(t) = floor(t/n) - floor(t/(n+1)) - floor(t/[n(n+1)]),
    h_q(t) = sum_{d|210} mu(d) b_q(t/d),
    lift(f)(t) = sum_{k>=0} f(t/15^k).

Write H_q=lift(h_q), B_n=lift(b_n), and let W0 be the lift of the
period-30030 initial seed. The original joint search uses

    W(t) = W0(t) - sum_{q=13}^{36} y_q H_q(t)
           + sum_{n in S} lambda_n B_n(t)

on 1<=t<R, with all y_q and lambda_n nonnegative. The repair set S is the
411 distinct sites in the preceding baseline. Its least element is 189,
and 220 is absent. The tail shield vanishes below R.

The following are exact rows of this constraint system, not values only
at its chosen optimum:

| t | W0(t) | nonzero H_q(t) | nonzero permitted B_n(t) |
|---|---:|---|---|
|13|1|H_13=1|none|
|16|1|H_16=1|none|
|20|3|H_20=1|none|
|220|1|H_13=-1, H_16=1, H_20=1|none|

These values were evaluated directly with Fraction arithmetic and checked
against every one of the 24 permitted correction columns and all 411 repair
columns. An additional elementary check of the last repair column assertion:
for 189<=n<220, both floor(220/n) and floor(220/(n+1)) are 1 and the third
floor is 0; for n>220 all are 0. Lower dilation arguments are at most 14.
The only missing case that could contribute is n=220, which is not in S.

Since W(13)>=1 and y_13>=0, the first row forces y_13=0. The fourth row now
requires

    1 - y_16 - y_20 >= 1,

which, by nonnegativity, forces y_16=y_20=0. The third row therefore gives

    W(20)=3

for **every feasible choice in the original joint LP**, not only the
observed numerical vertex. Its excess on [20,21) is necessarily 2.

Consequently this fixed allowed family has

    C-1 >= integral_20^21 2 dt/t^2 = 1/210,

whenever its global coverage and integrability are established as in the
reviewed construction. This is a restricted-family statement, not a bound
on all possible factorial constructions. It is not a global optimality
certificate for the particular value of C in PR #200.

The obstruction is specific: the permitted correction can act at 20, but
its induced deficit at 220 cannot be repaired inside the inherited
repair dictionary. Merely choosing a different objective within that same
family cannot remove the excess at 20.

## 2. A bounded diagnostic allowing new repair sites

To test this explanation, retain the reviewed joint candidate and subtract
alpha*h_20, with alpha in {1/108, 1/2, 1}. Do not rerun an LP. Instead apply
the existing lifted-prefix greedy repair, now allowing a repair at any
newly deficient integer n<R, not only at the old 411 sites.

For each trial, form its finite balanced floor sum

    D_alpha = D_joint - alpha*h_20 + sum lambda_n b_n.

For a deficient lifted weight at n, take lambda_n=1-W(n)>0, update all
later lifted cells exactly, and continue in increasing n. The repair is
nonnegative, zero before n, and one at n, so it cannot undo prior coverage.

The full seed is

    g_alpha(t) = D_alpha(t) + (701/36 + 3*alpha) W_*(t/R).

Above R, this is the old full seed minus alpha*h_20 plus nonnegative
patches and 3*alpha W_*(t/R). The old full seed is nonnegative there,
h_20<=3 over its complete period, and W_*>=1. Thus the new seed remains
nonnegative above R. Prefix coverage plus that tail property gives global
lifted coverage by the already-reviewed descent argument.

The finite sum is balanced, the full seed is O(1+log t), and its weighted
absolute integral exists. The same factorial identity and error bound
therefore apply. The check explicitly verifies kappa(D_alpha)>0 before
dropping geometric tails. That is the assertion omitted from the original
joint proposer and supplied by its reviewer.

## 3. Results, keeping costs separate

| additional amplitude alpha | C (approximate) | finite mass | tail H | new repairs | repairs outside old S | W(20) |
|---|---:|---:|---:|---:|---:|---:|
|0 (reviewed input)|1.04762393137926786|56345/108|701/36|0|0|3|
|1/108|1.04761063660274644|9407/18|39/2|58|20|323/108|
|1/2|1.04716047462750062|32129/54|755/36|111|68|5/2|
|1|1.04698001139826880|1405/2|809/36|145|100|2|

Every trial passed exact balance and the full 99,999-cell lifted-prefix
check, rebuilt from its combined coefficients. Rational log enclosures
showed a strict decrease of C for every trial.

The independent checker, importing neither proposer nor refine.py,
fully reconstructs the alpha=1 trial and establishes:

- 99,999 lifted prefix inequalities via divisor-increment tables;
- complete period checks of the initial and repair seeds;
- all 88,200 cells of the h_20 period, with supremum 3 and infimum -3;
- exact coefficient equality, balance, mass, and the tail coefficient;
- kappa(D)>0.97694 with outward interval logs;
- an interval separation showing a decrease in C greater than
  0.0006439199809990653434.

This independent code path is a self-check by the same originating
session, not an independent-agent proof review.

For alpha=1, with S1 and S2 defined below, the all-cutoff sufficient bound is

    psi(N) <= B_new(N)
            <= C_new*N + (1405/2) S1(N) + (4045/12) S2(N).

    S1(N) = sum_{k:15^k<=N} [1+log(N/15^k)],
    S2(N) = sum_{m:100000*15^m<=N}
                   (m+1)[1+log(N/(100000*15^m))].

The coefficient costs INCREASE relative to the reviewed joint candidate.
This is not another simultaneous decrease in mass and C.

High-precision evaluations, not directed interval comparisons, give:

| N | old B_N - new B_N | old U_N - new U_N |
|---:|---:|---:|
|10^4|18.68625|-4439.66730|
|10^6|719.68036|-8231.70430|
|10^8|64824.87219|48935.93876|
|10^12|643921018.59585|643882324.38505|

Thus the complete conservative ceiling is worse at the two smaller
cutoffs, better at the two larger cutoffs. The actual factorial value is
lower in all four diagnostics. The strictly smaller C with fixed logarithmic
error allowances also gives eventual improvement of the sufficient ceiling,
without claiming a computed threshold or monotonicity at every finite N.

## 4. Interpretation and boundaries

This test identifies an inherited-support restriction and removes it in
one diagnostic. It does not establish a useful uniform refinement law.
The new W(20)=2 still leaves excess at 20, and other early excess remains.
There is no inference that repeated removal has a controlled aggregate
cost, no claim that C tends to 1, and no bound of RH strength.

The useful structural requirement for future candidate families is that
a newly introduced correction must be allowed to introduce the repair
sites its own constraint violations require. Reusing an old repair
list can create an artificial mathematical barrier even when the new
correction is explicitly present in the search.

A prospective family still needs a proof that weighted excess removed
exceeds all repair and tail costs, with useful control uniform in the
family parameter. This note neither assumes nor proves that statement.

## 5. Reproduce

From this package directory, after installing numpy and mpmath:

    OPENBLAS_NUM_THREADS=1 python test_q20_direction.py
    OPENBLAS_NUM_THREADS=1 python check_support_direction.py

`inspect_support.py` prints the exact short-row constraints. The original
archives and extracted inputs remain read-only inputs; these commands
write only this package's generated diagnostic outputs.

The new analysis and diagnostics are saved here, not committed to Zeta Lab.
PR #200 has not been merged or changed by this calculation.
