# One Fourier kernel, equal spectra, different distinct fourth cycles

There is one even, nonnegative, compactly supported probability density whose
Fourier kernel gives two full-rank, four-point Gram matrices with identical
spectra and different distinct fourth-cycle sums. Thus the information loss
in [MOBIUS-CORRECTIONS.md](MOBIUS-CORRECTIONS.md), Section 3, occurs even with
the Fourier kernel fixed. No novelty claim is made. This is an ordinary finite
proof, and the points are not asserted to be zeros of zeta.

## 1. One positive frequency density

Set

    (c_1,s_1) = (3/5,4/5),
    (c_2,s_2) = (5/13,12/13),
    epsilon = 1/16.

Both pairs satisfy `c_i^2+s_i^2=1`. On `[-1/2,1/2]` define

    p(u) = 1 + 2 epsilon [
        c_1 (cos(2 pi 4u) + cos(2 pi 5u))
      + s_1 (cos(2 pi 3u) - cos(2 pi 6u))
      + c_2 (cos(2 pi 28u) + cos(2 pi 35u))
      + s_2 (cos(2 pi 21u) - cos(2 pi 42u)) ],

and set `p(u)=0` outside that interval. Every cosine has zero integral over
the interval, so `integral p=1`. The density is even, and the triangle
inequality gives the explicit pointwise bound on its support

    p(u) >= 1 - 4 epsilon (c_1+s_1+c_2+s_2) = 21/65 > 0.

Write

    K(z) = integral p(u) exp(-2 pi i u z) du.

This is a single normalized Fourier kernel. For real arguments it is real and
even, and its Gram matrices are positive semidefinite because `p>=0`.

Integer-frequency orthogonality gives `K(0)=1` and the following nonzero
values at positive integers:

| Integer argument | Kernel value |
|---|---:|
| 4, 5 | epsilon c_1 |
| 3 | epsilon s_1 |
| 6 | -epsilon s_1 |
| 28, 35 | epsilon c_2 |
| 21 | epsilon s_2 |
| 42 | -epsilon s_2 |

The value at every other positive integer is zero. To check the signs and
normalization directly, for positive integers `m,n`,

    integral_(-1/2)^(1/2) cos(2 pi m u) exp(-2 pi i n u) du
      = 1/2 if m=n, and 0 otherwise.

## 2. Two point sets and their exact Gram matrices

Take the ordered point sets

    X = (0,1,4,6),
    Y = (0,7,28,42).

The six positive pairwise differences for X are exactly `1,2,3,4,5,6`.
Those for Y are `7,14,21,28,35,42`. The two difference sets are disjoint.
The preceding Fourier values therefore give

    H_1 = (K(x_i-x_j)) = (1-epsilon)I + epsilon G(c_1,s_1),
    H_2 = (K(y_i-y_j)) = (1-epsilon)I + epsilon G(c_2,s_2),

where

                [ 1   0   c  -s ]
    G(c,s) =    [ 0   1   s   c ]
                [ c   s   1   0 ]
                [-s   c   0   1 ]

For example, in H_1 the difference from 0 to 6 gives `-epsilon s_1`,
while the difference from 1 to 4 gives `+epsilon s_1`. The diagonal is one
in both matrices.

The matrix G is the Gram matrix of

    (1,0), (0,1), (c,s), (-s,c).

These vectors are the union of two orthonormal bases of the plane, so
`G^2=2G` and its eigenvalues are `2,2,0,0`. Consequently both H_1 and H_2
have eigenvalues

    1+epsilon, 1+epsilon, 1-epsilon, 1-epsilon
      = 17/16, 17/16, 15/16, 15/16.

In particular both Gram matrices are positive definite and have rank four.
For every integer `j>=1`, their power traces agree exactly:

    tr(H_1^j) = tr(H_2^j)
      = 2[(17/16)^j + (15/16)^j].                         (1)

## 3. The distinct fourth cycles differ

For a four by four matrix H, define the distinct fourth-cycle sum by

    D_4(H) = sum_(i_1,i_2,i_3,i_4 pairwise distinct)
               H_(i_1,i_2) H_(i_2,i_3) H_(i_3,i_4) H_(i_4,i_1).

The sum is over ordered tuples, so it contains 24 terms. For either H_i,
a nonzero term must alternate between the index pairs `{1,2}` and `{3,4}`.
There are eight such tuples. Each has product `-epsilon^4 c_i^2 s_i^2`.
The other sixteen terms contain a zero entry. Therefore

    D_4(H_i) = -8 epsilon^4 c_i^2 s_i^2,

and in the two cases this gives

    D_4(H_1) = -9/320000,
    D_4(H_2) = -225/14623232.                            (2)

The two fractions are unequal. Equations (1)-(2) prove that the complete
sequence of power traces does not determine D_4, even for distinct real point
sets evaluated using one specified positive Fourier kernel. The entrywise
overlap terms retained by exact distinct-index inversion distinguish them.

## 4. A strictly interior frequency support

To place the density strictly inside a frequency interval of half-width less
than `1/2`, set

    q(u) = 2 p(2u),
    K_q(z) = integral q(u) exp(-2 pi i u z) du = K(z/2).

Then q is even, nonnegative, has integral one, and is supported on
`[-1/4,1/4]`. Its support is contained in `(-lambda,lambda)` for any
`1/4 < lambda < 1/2`. Use the two point sets

    2X = (0,2,8,12),
    2Y = (0,14,56,84).

The equality `K_q(2x-2y)=K(x-y)` preserves both Gram matrices exactly.
This provides the claimed example within the finite Fourier-kernel setting
of [FINITE-THEOREM.md](FINITE-THEOREM.md), Section 10.

The density has endpoint jumps. This construction is not an invocation of a
smooth correlation theorem. Also, support `[-1/4,1/4]` by itself does not give
a strict `<2` bound on the entire fourth-cycle Fourier support. Neither issue
is needed for the finite example.

Both configurations contain four simple real points. Their simple counts
therefore agree as well. The result establishes that a spectral summary loses
this particular statistic, not that the lost statistic already improves a
counting bound for zeta.

Independent exact rational checks verified the Fourier coefficient assignments,
both Gram identities, `G^2=2G`, the spectra, and all 24 ordered distinct-cycle
terms for each matrix.
