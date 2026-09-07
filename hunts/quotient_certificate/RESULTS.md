# An attainable-cell relaxation and an audit of the stopping argument

**2026-09-07.** Three finite ceilings improve after dropping constraints at
unattainable cells. Rational coefficients satisfy every retained constraint
in exact integer arithmetic. Optimization and logarithmic values remain
measured. An exact N=27 counterexample refutes the earlier prime-cell
dimension argument. No asymptotic exponent improvement or RH result is
established.

Input: the [factorial LP investigation](../prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/RESULTS.md)
at main d393e1a. This continuation tests a missing relaxation and separates
the proved statements from the proposed obstructions.

## 1. A relaxation that uses no prime locations

Let

    W_c(t) = sum_{j<=y} c_j floor(t/j),
    B_c(N) = sum_{j<=y} c_j log(floor(N/j)!),
    Q_N = {floor(N/d): 2 <= d <= N}.

The Chebyshev identity gives exactly

    B_c(N) - psi(N) = sum_{d=2}^N Lambda(d) [W_c(N/d) - 1].

It follows by expanding log(m!) as sum_{d<=m} Lambda(d) floor(m/d) and
interchanging finite sums. Floors commute under successive integer
division. Thus W_c(N/d) equals W_c(floor(N/d)).

Consequently, **W_c(n) >= 1 for n in Q_N is sufficient**. No condition at
other integer cells is needed. The omitted d=1 term has Lambda(1)=0.
The set Q_N is determined solely by integer division. It needs no sieve,
Mertens estimate, zero location, or knowledge of which d are primes.

For r=floor(sqrt(N)),

    Q_N = ({1,...,r} union {floor(N/d): 1<=d<=r}) minus {N}.

It has at most 2r-1 cells. Define T*(y,N) by minimizing the same factorial
objective over these constraints. The families satisfy

    psi(N) <= P*(y,N) <= T*(y,N) <= V*(y,N),

where P* is the earlier prime-cell relaxation and V* imposes all N cells.
The middle inclusion also holds for the earlier P* convention of retaining
all cells through r even when their prime weight is zero.

This is a ceiling at the chosen N. A coefficient vector is not asserted
valid for other cutoffs. Evaluating B accurately is also not an analytic
bound on B-N.

## 2. What the test produced

At y=floor(sqrt(N)), the excess B-psi(N) is:

| N | y | retained cells | earlier all-cell LP | rational quotient ceiling | reduction in excess |
|---:|---:|---:|---:|---:|---:|
| 1,000 | 31 | 61 | 62.92324708 | 41.28216944 | 34.4% |
| 10,000 | 100 | 198 | 323.64510369 | 226.83268961 | 29.9% |
| 100,000 | 316 | 630 | 1781.74781583 | 1035.23393535 | 41.9% |

The old column is read from the original saved results. The new column is
recomputed from results.json, which includes every coefficient numerator
and the common denominator 10^12. Rounding needed no feasibility repair in
the first two cases. Increasing the numerator of c_1 by one repaired the
third case. The largest change from the raw solver objective is below
0.000002. These are feasible ceilings; optimality is reported only to
floating LP tolerance, with dual residuals saved separately.

Every one of the 889 retained cells was checked with Python integers.
Independent factorial and weighted-prime evaluations were run at 50 and
80 decimal digits. The tests also use trial factorization for the N=1000
prime sum. The N=1000 candidate violates positivity at the omitted cell N,
so the relaxation really leaves the earlier feasible family.

These three data points do not establish a new exponent or refute the
earlier N/sqrt(y) conjecture for V*. They show that the earlier V* family
does not exhaust certificates whose constraints use no prime locations.
The attainable-cell relaxation must be assessed separately.

## 3. More columns than prime cells does not force zero excess

The earlier Section 4.2 claims P*=psi as soon as y exceeds the number of
prime-looking cells, and uses that count to assign zero to an uncomputed
N=10^6 case. The count is insufficient.

Take N=27 and y=9. Its prime-cell set, including the earlier convention
through sqrt(N), is

    S = {1,2,3,4,5,6,9,13},     |S|=8 < 9.

Let R_n=(floor(n/j))_{j=1}^9. Direct integer arithmetic gives

    -R_1 + R_3 - R_6 - R_9 + R_13 = 0.

The matrix has rank seven. In particular, it cannot interpolate the
constant vector on S: the coefficients of this row relation sum to -1.
For any feasible W, put e_n=W(n)-1 >= 0. The relation forces

    e_3 + e_13 = 1 + e_1 + e_6 + e_9 >= 1.

The weights in the excess identity at cells 3 and 13 are respectively
log(42) and log(2). All other weights are nonnegative. Therefore

    B-psi(27) >= log(2) (e_3 + e_13) >= log(2).

The coefficient vector

    c = (1,-1,-1,0,-1,1,0,0,-1)

has W=1 at every cell of S except W(13)=2. It attains the lower bound.
**Hence P*(9,27)-psi(27)=log(2), exactly.**

This is an elementary finite proof with exact-arithmetic checks of the row
relation, rank, prime weights, and attaining vector. It is not a kernel
proof or an asymptotic result. The larger zero claims require their own
feasibility evidence; this counterexample does not determine those values.

## 4. The random-sawtooth argument discards structure

For any coefficients, the identity is

    W_c(n) = n A_c - sum_j c_j {n/j},    A_c = sum_j c_j/j.

The LP does not impose A_c=0. At its earlier (N,y)=(1000,31) optimum,
A_c is measured as 0.0081388771875. The proposed balanced-field heuristic
therefore does not describe that optimizer without an additional drift
term. Nor does the observed initial Mobius segment constrain every feasible
coefficient vector.

For n uniform on a full common integer period, put
f_j(n)={n/j}-(j-1)/(2j). Exact residue averaging gives

    Cov(f_i,f_j) = (gcd(i,j)^2-1)/(12 i j),
    Var(sum_j c_j f_j) =
        (1/12) sum_{d=2}^y J_2(d) [sum_{j<=y, d|j} c_j/j]^2,

where J_2(d)=d^2 product_{p|d}(1-1/p^2). The second identity follows from
gcd(i,j)^2-1=sum_{d|gcd(i,j),d>=2}J_2(d).
The covariance is checked by exact full-period enumeration for all
400 ordered pairs 1<=i,j<=20.

There cannot be a uniform positive lower comparison with sum c_j^2 for
arbitrary balanced coefficients. Let P be a squarefree primorial,
delta=phi(P)/P and tau=2^omega(P). Use c_d=mu(d) on divisors of P, but
replace c_1 by 1-delta. Then sum c_d/d=0, and multiplicativity gives

    12 Var = tau delta - delta^2,
    sum_d c_d^2 = tau - 2 delta + delta^2.

The ratio tends to zero as delta tends to zero. Exact checks at
P=6,30,210,2310 pin these formulas. This family is not a positive ceiling,
so it does not refute a variance inequality with additional positivity
hypotheses. It refutes the unrestricted diagonal comparison.

Neither full-period covariance nor positivity supplies a fixed
three-standard-deviation law for a finite, weighted deterministic field.
The finite horizon and prime weights need their own argument.

## 5. What the cited literature actually excludes

The following are source corrections, not new results.

**Pointwise square root.** The statement psi(x)-x=O(sqrt(x)) is false:
Littlewood gives positive and negative oscillations of size
sqrt(x) log log log x. RH gives O(sqrt(x) log^2(x)); equivalently one may
use O_epsilon(x^(1/2+epsilon)) for every epsilon>0.
[Brent, Platt and Trudgian, introduction](https://arxiv.org/html/2008.06140).

**The dyadic mean square is different and valid.** Boundedness of
J(X)=integral_X^{2X}(psi(x)-x)^2 dx/x^2 is RH-equivalent. The weight on a
dyadic interval makes this equivalent to integral_X^{2X}(psi-x)^2 dx=O(X^2).
Cramer's RH implication and failure of boundedness when RH fails are
recorded in the same [paper](https://arxiv.org/html/2008.06140).
That does not bound all of CHHL's prime-pair error: its averaging variable
and target differ. CHHL prove an implication toward RH and only an
N^(5/2) times logarithms upper bound under GRH in their Theorem 2, not an
equivalence with the proposed N^(2+epsilon) error bound.
[CHHL, introduction and Theorem 2](https://arxiv.org/html/2308.14888v1).

**Nyman-Beurling.** Burnol proves an unconditional lower bound for a
global squared distance:

    liminf d_y^2 log y >= sum_{distinct Re(rho)=1/2} m(rho)^2 / |rho|^2.

This is a lower bound, and the norm is d_y, not d_y^2.
[Burnol, original paper](https://arxiv.org/pdf/math/0103058).
A matching asymptotic d_y^2~(2+gamma-log(4pi))/log y is proved under RH
and sum_{|Im(rho)|<=T}|zeta'(rho)|^(-2) << T^(3/2-delta) for some delta>0,
which includes simplicity of the zeros.
[Bettin, Conrey and Farmer, pp. 1-2](https://arxiv.org/pdf/1211.5191).
It is not a theorem that every norm has this rate.

The connection also needs a comparison theorem. Under t=1/x the
strengthened NB problem uses the global error

    1_[1,infinity)(t) + sum_j c_j {t/j}

in L^2(dt/t^2). To identify this with 1-W_c above t=1 requires A_c=0.
The finite LP has neither that restriction nor that global norm, and its
objective is an atomic prime-weighted linear excess.
[Baez-Duarte, strengthened criterion](https://arxiv.org/pdf/math/0202141).
The sawtooth representation itself is not spectrally blind. With the
Mellin convention specified explicitly,

    integral_0^infinity [1_[1,infinity)(t)+sum_j c_j {t/j}] t^(-s-1) dt
        = (1-zeta(s) sum_j c_j j^(-s))/s,    0<Re(s)<1.

This representation supplies no improved estimate by itself.

**Elementary PNT estimates.** Diamond-Steinig's exponent 1/7-epsilon
is an achieved estimate, not an impossibility theorem. Diamond's own
survey records subsequent elementary improvements to 1/6-epsilon and
discusses estimates that would improve it further.
[Diamond, Sections 1 and 8, publication](https://doi.org/10.1090/S0273-0979-1982-15057-1),
[accessible transcription of the author's article](https://studylib.net/doc/7950810/elementary-methods-in-the-study-of-the-distribution-of-pr...).

**Hyperbola.** The finite identity is a noncircular algorithm using mu and
Lambda below sqrt(N). An analytic bound on the remaining sums is the
missing step. The first half includes the main term N. A routine RH bound
of O_epsilon(N^(3/4+epsilon)) on centered pieces would be an upper bound,
not a lower obstruction proving that size unavoidable. No such lower
obstruction is established by the cited finite LP experiment.

## 6. Reproduce

From the repository root:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv/bin/python hunts/quotient_certificate/probe.py --N 1000 10000 100000 --output hunts/quotient_certificate/results.json
    .venv/bin/python -m pytest -q -n 2 tests/test_quotient_certificate.py

RUNS.md records estimates, the exploratory timeout, and verification.
The JSON reports start, completion, counts, and failures, including partial
completion if a later unit fails.

## 7. The doors

1. **Active constraints.** Positivity remains binding on attainable cells.
   Support remains y=floor(sqrt(N)). The measured relaxation saves 29.9%
   to 41.9% of the previous excess, but no exponent follows from that.
2. **Frozen choices.** Consecutive denominators, the square-root support,
   and the factorial dictionary remain fixed. Relaxing the support trades
   construction and evaluation cost against excess. The exact gcd form
   identifies correlated divisibility modes that the Gaussian argument
   omitted. To use them, keep the slope and control the actual finite
   prime-weighted excess, rather than substitute full-period variance.
3. **Information class.** The quotient relaxation uses less positivity
   than V* without reading prime locations. Adding prime-cell information
   is a further, separate relaxation. The zero-excess question is a
   feasibility and rank question, not a count of variables. The NB and
   dyadic mean-square doors require different norms and additional
   comparison estimates.

The immediate continuation is to analyze T*, including its dual measures
on attainable cells, with the exact correlations retained. The all-cell
barrier conjecture remains open, and no comparison proved here transfers
it to this relaxed family.
