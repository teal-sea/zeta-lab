# An overlap bound from a finite spectral band

This is a finite statement about a conjugation-invariant multiset. It gives no
new asymptotic bound for zeros of zeta. The arithmetic cost is stated below.
The companion `overlap_bound.py` checks the formulas on exact rational Fourier
kernels, including the two five-occurrence examples and a perturbed example.

## 1. Definitions and the positive spectral branch

Let p be an even, nonnegative, integrable Fourier profile of integral one,
strictly positive on a nonempty interval. Assume its transform

    K(z) = integral p(u) exp(2 pi i u z) du

exists at every difference used below. Let the N occurrences z_1,...,z_N form
a finite conjugation-invariant multiset. Set

    G_ij = K(z_i-z_j),       M_2 = tr(G^2),
    S = sum_i (sum_j G_ij^2)^2,
    Q = sum_ij G_ij^4,       R = rank(G).

These are ordinary complex products, not absolute values. Let s count the real
locations of multiplicity exactly one.

If every nonzero eigenvalue of G is positive, all locations are real. Here is
the finite reason, so positivity is not silently substituted for an assumption
about all zeros. The real cosine/sine Fourier feature map c(z) satisfies
c(z)^T c(w)=K(z-w), c(z)^T c(z)=1, and c(conj z)=conj c(z).
Distinct complex locations have linearly independent feature vectors: any
linear dependence would give an exponential polynomial vanishing on the
interval where p is positive, hence identically zero. For each nonreal pair
write c(z)=g+i h. In a real basis the feature operator has contributions

    m c(x)c(x)^T                 from a real location,
    2m (g g^T-h h^T)            from a nonreal pair.

All the real columns c(x), g, h are independent. Sylvester's law of inertia
therefore gives exactly one negative eigenvalue for each distinct nonreal
pair. The occurrence Gram matrix and the feature operator have the same
nonzero eigenvalues. This proves the assertion.

Consequently, in the positive branch there are R distinct real locations x_i
with integer multiplicities m_i. Their positive definite multiplicity Gram
matrix is

    H_ij = sqrt(m_i m_j) K(x_i-x_j),       H_ii=m_i.

It has exactly the nonzero spectrum of G. Put

    r_i = (H^2)_ii/m_i = sum_j m_j K(x_i-x_j)^2.

Then N=sum_i m_i, M_2=sum_i m_i r_i, S=sum_i m_i r_i^2,
and Q=sum_ij m_i m_j K(x_i-x_j)^4.

## 2. A bound stable under spectral perturbation

Suppose the nonzero spectrum is contained in [alpha,beta], where

    0 < alpha <= 1 <= beta < 4.

Write a=alpha+beta and b=alpha beta. Then

    s >= 3S/b^2 - (3a^2/b^2-1/2)N + (6a/b-5/2)R.       (1)

An integer ceiling can be taken on the right. One can also take the maximum
with zero and with the ordinary bound 2N-M_2.

Proof. Functional calculus gives H^2 <= aH-bI. Its diagonal entries imply

    0 <= r_i <= a-b/m_i.

The upper endpoint is nonnegative because it bounds the nonnegative r_i.
Squaring, multiplying by m_i, and summing gives

    S <= a^2 N-2ab R+b^2 H_1,       H_1=sum_i 1/m_i.      (2)

Every diagonal entry of H is an integer at most beta<4. Thus m_i is 1, 2,
or 3, and direct substitution of these three possibilities gives

    H_1 = s/3+(5R-N)/6.                                 (3)

Equations (2) and (3) give (1). This argument allows alpha below 1 and beta
above 3; exact equality of the eigenvalues to two prescribed values is not
required.

Without beta<4, (2) still yields the weaker general bound

    s >= 2(S-a^2 N+2ab R)/b^2-R,

because 1/m_i<=1/2 at every nonsimple location.

## 3. Stronger joint bounds when the spectrum lies in [1,3]

Under the narrower spectral condition, both of the following hold:

    s >= S/3-(3/2)M_2+(7/6)N+R,                         (4)
    s >= (4Q-M_2-15N+18R)/6.                            (5)

Formula (4) is at least as strong as (1) with alpha=1, beta=3. The difference
between their right sides is (3/2)(4N-3R-M_2), which is nonnegative by
H^2<=4H-3I.

Proof of (4). Diagonal Cauchy-Schwarz also gives r_i>=m_i, so

    m_i <= r_i <= 4-3/m_i.

For m_i=1 this forces r_i=1; for m_i=3 it forces r_i=3. For m_i=2 it gives
2<=r_i<=5/2 and therefore

    2r_i^2 <= 9r_i-10,

since the difference is -2(r_i-2)(r_i-5/2). Combining these three cases gives

    m_i r_i^2 <= (9/2)m_i r_i-(7/2)m_i-3
                +3 times the indicator of m_i=1.

Summation proves (4).

Proof of (5). An entry H_ii equal to a spectral endpoint has no off-diagonal
entries in its row: apply the positive semidefinite matrices H-I and 3I-H,
respectively. After permuting coordinates, H therefore splits as

    I_s direct-sum 3I_u direct-sum (2I_t+B),

where t and u count multiplicities 2 and 3, B is real symmetric, its diagonal
is zero, and its operator norm is at most one. Write

    D = sum_ij B_ij^2 = M_2-5N+6R-2s,
    E_4 = sum_ij B_ij^4.

Each |B_ij|<=1, so E_4<=D. The occurrence weights give the exact identity

    Q = M_2-D+E_4/4 <= M_2-3D/4.

Substituting for D and rearranging proves (5).

These bounds can be used together by taking their maximum. In particular,
they consume information about overlap which a power-trace summary need not
determine.

## 4. Equality and exact examples

If the nonzero spectrum consists only of 1 and 3, H^2=4H-3I and every step
in (2) is an equality. Thus

    s = S/3-29N/6+11R/2.                                (6)

For N=5k and R=3k this becomes s=(S-23k)/3.

Consider the strictly positive profile

    p(u)=1+cos(2 pi u)+(1/4)cos(4 pi u), |u|<=1/2,
    p(u)=0 otherwise.

Writing c=cos(2 pi u) gives p=(1/2)(c+1)^2+1/4>=1/4.
At integer arguments its transform has values K(0)=1, K(1)=1/2,
K(2)=1/8, and K(j)=0 for |j|>=3. The occurrence lists

    (0,0,0,3,6):     s=2,  S=29, Q=11,
    (0,0,1,1,4):     s=1,  S=26, Q=19/2

both have spectrum (3,1,1,0,0). Both (4) and (5) give their exact respective
simple counts, while their ordinary second-moment bound is 2N-M_2=-1.
Their entire power-trace sequences agree, M_j=3^j+2.

The exact check also changes the first harmonic to (4/5)cos(2 pi u), which
produces interior eigenvalues 6/5 and 14/5 in the two-doubleton example.
A separate check adds (1/100)cos(6 pi u) to the original profile and applies
(1) with the rational enclosing band [49/50,151/50]. This latter example has
nonzero overlap between multiplicity-1 and multiplicity-3 locations, so the
endpoint-block decomposition from Section 3 no longer applies. The perturbed
bound still has ceiling two.

## 5. Arithmetic cost and scope

If the original Fourier profile is supported in [-lambda,lambda], the pair
statistic Q uses K^4 and has total absolute Fourier frequency up to 8lambda.
The three-index statistic S uses K(x-y)^2 K(x-z)^2 and has the same maximum
8lambda. The Rudnick-Sarnak support condition sum |xi_j|<2 therefore licenses
these tests only after shrinking the original width to lambda<1/4, with the
usual smooth test and height-cutoff hypotheses. Merely correcting repeated
indices does not remove that cost. See Rudnick and Sarnak, Section 3 of
[Zeros of principal L-functions and random matrix theory](https://www.math.tau.ac.il/~rudnick/papers/nlevelDuke.pdf), for that support
condition and its smoothed complex-zero formulation.

Moreover, this note proves no zeta spectral-band estimate. The positive
branch itself excludes nonreal locations in the finite multiset. Applying
the band assumption to all zeta zeros would require a further theorem, not
just evaluation of S and Q. The present result is a finite overlap-aware
counting inequality and a stable extension of the exact spectral example.

[OverlapBand.lean](OverlapBand.lean) checks the arbitrary-size identity (6)
from its explicit matrix polynomial and multiplicity hypotheses. It also
checks the finite-sum inequality (4) from the stated scalar bounds on each
row energy. The spectral-to-row argument, bound (1), bound (5), and the
Fourier realization are ordinary mathematical proofs. Exact source hashes
and AXLE receipts are in [FORMAL-CHECKS.json](FORMAL-CHECKS.json).
