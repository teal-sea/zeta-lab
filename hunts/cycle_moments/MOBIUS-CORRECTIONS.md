# Exact distinct-cycle corrections and information lost by power traces

The repeated-index corrections below are exact. Applying separate bounds to
their terms can lose information, and power traces alone do not determine
every corrected cycle statistic. A finite example proves that distinction.
Neither the identities nor the example establish an improved zeta proportion.
No novelty claim is made here.

## 1. Definitions, including multiplicities

Let K be a complex symmetric N by N matrix with K_ii=1. Set

    M_j = tr(K^j),
    S = sum_i (sum_j K_ij^2)^2,
    Q = sum_(i,j) K_ij^4,

and let D_j be the sum of products

    K_(i_1,i_2) K_(i_2,i_3) ... K_(i_j,i_1)

over ordered tuples of pairwise distinct indices. Products and powers are
ordinary complex products, not absolute squares. The identities do not assume
that individual terms are nonnegative.

Indices label occurrences. Distinct indices can have the same underlying zero
location or feature vector. Thus this convention retains multiplicity and
matches the distinct-index convention of the correlation theorem; replacing
it by distinct locations would require falling-factorial multiplicity weights.

## 2. The third and fourth corrections

The exact formulas are

    D_3 = M_3 - 3 M_2 + 2N,                               (1)

    D_4 = M_4 - 4 M_3 - 2S + 10 M_2 + Q - 6N.             (2)

For a partition F of the cycle positions, identify the indices within each
block, leaving indices in different blocks free. Its inclusion-exclusion
coefficient is

    mu(F) = product_(B in F) (-1)^(|B|-1) (|B|-1)!.

For three positions, the three pair identifications give M_2 and the single
triple identification gives N. This proves (1). For four positions, the full
partition calculation is:

| Identifications | Number | Combined contribution |
|---|---:|---:|
| None | 1 | M_4 |
| One adjacent pair | 4 | -4 M_3 |
| One opposite pair | 2 | -2S |
| Triple plus singleton | 4 | +8 M_2 |
| Two adjacent pairs | 2 | +2 M_2 |
| Two opposite pairs | 1 | +Q |
| All four equal | 1 | -6N |

For example, identifying the first and third positions gives
sum_(i,j,k) K_ij^2 K_ik^2=S. Identifying both opposite pairs gives
sum_(i,j) K_ij^4=Q. These weighted overlaps differ from ordinary power traces.
Replacing every identification of the same partition size by one power trace
would therefore give an incorrect simplification.

There is a useful further identity. Define

    V_3 = sum_(i,j,k pairwise distinct) K_ij^2 K_ik^2.

Separating j=i, k=i and j=k in S gives

    S = 2M_2 + Q - 2N + V_3.

Consequently the quartic correction in `FINITE-THEOREM.md` is

    Delta_4 = 2N - 5M_2 + 4M_3 - M_4
            = -D_4 - 2V_3 + M_2 - Q.                     (3)

Together with Delta_3=D_3, equation (3) expresses that score in terms of exact
distinct-cycle corrections. No inequality has yet been applied to any term.

## 3. Same full spectrum, different corrected fourth cycles

Take the following four unit vectors in R^2:

    v_1=(1,0), v_2=(0,1), v_3=(c,s), v_4=(-s,c),
    c^2+s^2=1.

They form the union of two orthonormal bases. Let V be the two by four matrix
with these columns, and K=V^T V their Gram matrix. Since VV^T=2I,

    K^2 = V^T(VV^T)V = 2K.

Induction gives K^j=2^(j-1)K for j>=1, and therefore

    M_j = 2^(j+1), j>=1.                                 (4)

Equivalently the eigenvalues are 2,2,0,0. Every power trace is independent of
the rotation. Also (K^2)_ii=2, so S=16. In contrast,

    Q = 4 + 4(c^4+s^4) = 8 - 8c^2s^2.

Substituting N=4, M_2=8, M_3=16, M_4=32 and S=16 into (2) gives

    D_4 = -8c^2s^2.                                      (5)

There is also a direct check: a nonzero distinct four-cycle must alternate
between the two bases. There are eight such ordered cycles, each with product
-c^2s^2. Every other ordered four-cycle contains a zero inner product.

Two exact instances are:

| (c,s) | Spectrum of K | D_4 |
|---|---|---:|
| (3/5,4/5) | 2,2,0,0 | -1152/625 |
| (5/13,12/13) | 2,2,0,0 | -28800/28561 |

Thus even the complete sequence of power traces does not determine D_4.
The entrywise overlap Q distinguishes these frames. This demonstrates an
actual information loss when a finite configuration is summarized by its
spectrum. It does not identify an error in exact inclusion-exclusion.
The example is a finite unit-vector family, not an asserted realization by
the zeros of zeta or by one specified Fourier kernel.

[SAME-KERNEL-EXAMPLE.md](SAME-KERNEL-EXAMPLE.md) strengthens this construction:
after adding a small identity component, both Gram matrices are realized
by distinct real point sets for one explicit positive Fourier density.

## 4. What the corrections do to Fourier support

For K(z)=hat(p)(z), let p be a nonnegative compactly supported frequency
profile. The unrestricted four-cycle kernel is

    f_4(z_1,z_2,z_3,z_4)
      = K(z_1-z_2)K(z_2-z_3)K(z_3-z_4)K(z_4-z_1).

Its Fourier transform lies on sum xi_j=0, with density

    Phi_4(xi) = integral p(t+xi_1)p(t+xi_1+xi_2)
                          p(t+xi_1+xi_2+xi_3)p(t)dt.     (6)

Suppose p>0 on (-lambda,lambda) and lambda>1/4. Choose
1/2<d<2lambda. Then

    Phi_4(d,-d,d,-d) = integral p(t+d)^2 p(t)^2 dt > 0,
    sum_j |xi_j| = 4d > 2.                               (7)

This explicitly locates nonzero Fourier density outside the region furnished
by the restricted-support correlation theorem. The same conclusion holds for
the symmetrized four-cycle kernel: symmetrization adds nonnegative densities.

For nonzero score parameter t, the coefficient of M_4 in the quartic score is
-t^2/D_t. The other power-trace terms have degree at most three in the counting
measure. To see why those terms cannot algebraically cancel (7), replace the
measure by sum_i w_i delta_(z_i) and extract the coefficient of w_1w_2w_3w_4.
Only M_4 contributes. The lower-index corrections contribute nothing to that
coefficient. Integer multiplicities suffice: an identity for every choice of
nonnegative integer w_i is a polynomial identity.

Therefore exact reorganization by (1)-(3) does not itself remove the
beyond-support four-variable term. It can move the unknown contributions
among different statistics: Q uses the kernel K(z)^4, while S uses
K(z_1-z_2)^2 K(z_1-z_3)^2. At a near-full-width p, these kernels also reach
beyond the permitted Fourier region. They cannot simply be assigned the
already-known pair or triangle constants.

This is an algebraic support statement about the displayed reorganization.
It does not exclude additional arithmetic cancellation in expectations for
actual zeta zeros, or a different counting inequality that retains entrywise
information.

## 5. Relation to the source theorem and checks

[Rudnick and Sarnak, Section 4](https://www.math.tau.ac.il/~rudnick/papers/nlevelDuke.pdf)
uses the partition-lattice coefficient in equation (4.4), unrestricted
partition sums in (4.6), and exact inversion in (4.9). Their equation (4.14)
pushes frequencies to block sums v_B=sum_(i in B)xi_i. The triangle inequality
then preserves an already-valid bound sum|xi_i|<2. It does not assert that a
larger original support shrinks into that region. Their Theorem 4.1 states
the determinant identity on the same restricted region. The final passage
also explains how the smooth version follows from their unconditional
Theorem 3.1.

`distinct_cycles.py` checks direct enumeration against both independent
partition inversion and the reduced formulas (1)-(2), using exact fractions.
Its controls include a constant kernel, a nonconstant Gram matrix with a
repeated vector, and both frames in Section 3. It checks K^2=2K, which pins
all the traces in (4), not just a finite list of moments. The saved results
are in `distinct_cycle_results.json`.

`DistinctCycles.lean` proves (1) over any commutative ring, retaining the
all-equal add-back. `IsospectralCycles.lean` proves the complete finite
unit-Gram example in Section 3, including every power trace and direct
distinct-fourth enumeration. Both passed Lean 4.33.0 through AXLE with
standard axioms only. The fixed-Fourier-kernel extension and support argument
remain ordinary mathematical proofs.

The mathematical distinction is now explicit: exact inversion retains the
overlap terms; a spectral summary can discard them. Whether retaining those
terms improves a zeta bound is a separate question left open here.
