# The same complete spectrum can hide different simple-point counts

One fixed positive Fourier density gives two real multisets with identical
power traces at every order and different numbers of simple points. Their
entrywise overlaps recover the missing count. Independent copies amplify the
difference to simple-point fractions ranging from 1/5 to 2/5 while preserving
all normalized power traces.

These are original finite constructions, with ordinary proofs and the scoped
Lean checks stated below. No novelty claim or improved asymptotic statement
about zeta zeros is made.

## 1. What the spectrum already determines

Let p be an even, nonnegative, compactly supported probability density, positive
almost everywhere on some open interval. Set

    K(z) = integral p(u) exp(-2 pi i u z) du.

Take a finite conjugation-invariant complex multiset, counting multiplicities.
Let R be its number of distinct real locations, k its number of distinct
nonreal conjugate pairs, N its total multiplicity, and s its number of simple
real locations. Let A be the real signed operator of
`FINITE-THEOREM.md`, Section 10. Write nu_+ and nu_- for its positive and
negative eigenvalue counts, including spectral multiplicities. Then

    nu_+ = R+k,    nu_- = k,    rank A = R+2k.             (1)

To prove this, the functions `sqrt(p(u)) exp(-2 pi i u z)` for distinct z are
linearly independent over the complex numbers. A linear relation would give
an exponential polynomial vanishing almost everywhere on the interval where
p is positive. Continuity makes it vanish throughout that interval. Its
derivatives at an interior point form an invertible Vandermonde system, so
all coefficients vanish.

Passing to the real feature vectors for real points and the real and imaginary
feature vectors for conjugate pairs preserves independence. In this basis the
coefficient form defining A is diagonal: each real location contributes one
positive entry, and each nonreal pair contributes one positive and one negative
entry. All entries are nonzero because multiplicities are positive. Sylvester's
law of inertia proves (1).

Thus the full spectrum already determines the number of distinct locations
and whether any are nonreal. Multiplicity capacity then gives

    N >= s + 2(R-s) + 2k = 2nu_+ - s,

and consequently

    s >= max(0, 2nu_+ - N).                              (2)

This is sharp using only N and the inertia. If R>0 and
`R+2k <= N <= 2R+2k`, make exactly `N-(R+2k)` real locations double, keep
the others simple, and give every nonreal pair multiplicity one. If
`N >= 2R+2k`, make all real locations multiple and assign any surplus to one
of them. If R=0, the feasible total N is even and s=0. Arbitrary distinct
locations realize these inertia counts by the independence argument above.
This sharpness statement does not assert that every full spectrum permits
every such allocation.

In particular, a positive occurrence Gram matrix of rank N already forces all
N points to be simple and real. The earlier four-point full-rank example
therefore demonstrated loss of a statistic, but did not demonstrate loss of
the simple-point count. The construction below does.

## 2. A fixed density and two different counts

On `[-1/2,1/2]` take

    p(u) = 1 + cos(2 pi u) + (1/4) cos(4 pi u),

and set p to zero outside. With `x=cos(2 pi u)`,

    p(u) = 1/4 + (1/2)(1+x)^2 >= 1/4.

It is even and has integral one. Integer-frequency orthogonality gives

    K(0)=1,    K(1)=K(-1)=1/2,    K(2)=K(-2)=1/8,
    K(n)=0 for every integer |n|>2.                      (3)

Use the two multisets

    Z_A = (0,0,0,3,6),       multiplicities (3,1,1), s_A=2,
    Z_B = (0,0,1,1,4),       multiplicities (2,2,1), s_B=1.

Both have N=5 and three distinct real locations. If C is the kernel Gram
matrix on distinct locations and D is the diagonal matrix of their
multiplicities, the nonzero spectrum of the occurrence Gram matrix is the
spectrum of `H=sqrt(D) C sqrt(D)`. In these two cases,

          [3 0 0]                  [2 1 0]
    H_A = [0 1 0],           H_B = [1 2 0].
          [0 0 1]                  [0 0 1]

Both have eigenvalues `3,1,1`. Each five by five occurrence Gram matrix also
has two zero eigenvalues. Therefore the complete raw cycle moments agree:

    M_j(Z_A) = M_j(Z_B) = 3^j+2 for every integer j>=1.   (4)

Their different simple counts prove that the full sequence of raw moments
does not determine s, even with one specified Fourier kernel. Equation (2)
gives s>=1 for this spectrum, and Z_B attains it.

## 3. The overlaps distinguish the actual count

For the occurrence Gram matrix G define

    S = sum_i (sum_j G_ij^2)^2,
    Q = sum_(i,j) G_ij^4,

and let D_4 be the ordered four-cycle sum over pairwise distinct occurrence
indices. Distinct indices may have the same location. Exact values are

| Multiset | N | s | M_2 | M_3 | M_4 | S | Q | D_4 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Z_A | 5 | 2 | 11 | 29 | 83 | 29 | 11 | 0 |
| Z_B | 5 | 1 | 11 | 29 | 83 | 26 | 19/2 | 9/2 |

For Z_A, the Gram matrix is a three by three all-ones block and two isolated
ones. No nonzero cycle can use four distinct indices. For Z_B, the first four
occurrences form two duplicate pairs with cross entries 1/2, and the fifth
is isolated. Eight four-cycles alternate between the pairs, each contributing
1/16. The other sixteen contribute 1/4 each. This gives `D_4=9/2`.

There is also a universal count classification within this exact spectral
class, not just a comparison of the two examples. By (1), a configuration
with nonzero spectrum `3,1,1` has three distinct real locations and N=5. Its
only multiplicity patterns are `(3,1,1)` and `(2,2,1)`.

For distinct real x,y, positivity of p on an interval implies

    |K(x-y)| < 1.                                       (5)

Equality in the triangle inequality for its Fourier integral would require
the phase to be constant almost everywhere on that interval, impossible for
`x-y != 0`. Thus, in any real configuration,

    M_2-Q = sum_(locations a!=b)
                m_a m_b K(x_a-x_b)^2 [1-K(x_a-x_b)^2] >= 0,

with equality exactly when all distinct-location features are orthogonal.
Then their weighted Gram eigenvalues are precisely their multiplicities.
In particular, the shared spectrum with Q=M_2=11 forces s=2.

The other case is exact as well. Since `H` has spectrum `3,1,1`,
`H=I+2vv^T` for a real unit vector v. The diagonal is the multiplicity vector.
For multiplicities `(2,2,1)`, this forces `v_i^2=(1/2,1/2,0)`, so the only
nonzero cross-location kernel value has absolute value 1/2. Consequently
`Q=19/2` and s=1. Throughout this entire spectral class,

    s = (2Q-16)/3 = (S-23)/3.                            (6)

## 4. The count difference survives arbitrary scale

Fix a positive integer h. Translate h independent blocks by `10j`,
`j=0,...,h-1`, and choose t of them to be type A and the other h-t to be type B.
Distinct blocks have integer separation at least four, so (3) makes every
cross-block kernel entry zero. Their occurrence Gram matrices form an exact
direct sum. Hence

    N = 5h,
    M_j = h(3^j+2) for every j>=1,
    s = h+t,
    Q = (19h+3t)/2,
    S = 26h+3t,
    D_4 = (9/2)(h-t).                                   (7)

All raw moments remain fixed as t varies. The simple-point fraction ranges
from `1/5` to `2/5`, so this loss of counting information does not disappear
when the multisets grow.

The all-A member has Q=M_2 and exactly 2h simple points. In fact, any
configuration with its nonzero spectrum `3` repeated h times and `1` repeated
2h times, together with Q=M_2, has those multiplicities and hence s=2h.
However, a bound using only that full spectrum cannot exceed h, because
the all-B member has exactly the same spectrum and s=h. The overlaps can
therefore improve a finite count beyond the best bound from the spectrum alone.

## 5. S recovers the count throughout the amplified spectral class

The exact formula involving S is stronger than a property of the chosen block
family. Suppose the nonzero spectrum consists of h copies of 3 and 2h copies
of 1. Inertia again forces all points to be real. The weighted location Gram
matrix H is positive definite and satisfies

    H^2 = 4H-3I.

Its diagonal entries are the integer multiplicities `m_a`. The spectral bounds
force `m_a` to belong to `{1,2,3}`. An occurrence at location a has squared-row
sum

    sum_j G_ij^2 = (H^2)_aa/m_a = 4-3/m_a.

Writing `R=3h` and `T_1=sum_a 1/m_a` gives

    S = sum_a m_a(4-3/m_a)^2 = 16N-24R+9T_1.

For any multiset of multiplicities from `{1,2,3}`, direct separation of the
three possible values gives

    s = 3T_1 - (5R-N)/2.

Combining these identities proves, throughout this whole spectral class,

    s = S/3 - 29N/6 + 11R/2 = (S-23h)/3.                (8)

The broader overlap bound is developed separately in `OVERLAP-BOUND.md`.
Equation (8) is an exact theorem for the stated spectral class; it is not a
claim that S determines s for arbitrary spectra.

## 6. Scope and reproduction

The density has endpoint jumps. Its rescaling `q(u)=L p(Lu)` preserves every
Gram entry when every point is multiplied by L, and makes frequency support
as narrow as desired. This finite rescaling does not identify any multiset
with actual zeta zeros or supply a smooth height-cutoff transfer theorem.

`counting_overlap.py` uses exact Fraction arithmetic. It checks the expanded
five by five matrices, the matrix recurrence `G^3=4G^2-3G` that proves (4) at
all orders, direct cycle enumeration, the overlap values, and separated
amplifications. Separate 60-digit Fourier quadrature checks all integer
differences from zero through 26. The script saves its results beside the
source. Run it from the repository root:

    .venv/bin/python hunts/cycle_moments/counting_overlap.py

[CountingOverlap.lean](CountingOverlap.lean) checks the two occurrence
matrices against the same integer kernel, computes their simple counts and
overlaps, and proves equality of power traces for every natural exponent.
[OverlapBand.lean](OverlapBand.lean) checks (8) from the explicit matrix
polynomial relation and diagonal multiplicity hypotheses, in every finite
dimension. The Fourier realization, inertia argument, and passage from
eigenvalues to those hypotheses are ordinary proofs. Exact source hashes and
AXLE receipts are in [FORMAL-CHECKS.json](FORMAL-CHECKS.json).
