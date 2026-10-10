# A parameterized finite Fourier network

Status: written derivation, self-reviewed; independent audit pending. No novelty or practical runtime claim. The finite network argument below is algebraic and has no zeta-zero-free hypothesis. Its all-length DFT consequence uses the exact-width compiler and transport lemmas in the pinned OpenAI source.

## Exact contract

Fix an integer h>=22. Put v=binom(h,3), d=binom(h-3,3)+3(h-3), m=h^3,

W=2v^3+3v^2(vd+h+1), Delta=2v^2(v-3h(h+1)),

P=2^a, where a is the smallest integer with 2^a>=W; lambda=m-Delta/P and theta=log(lambda)/log(m).

Let C=((1+i,1-i),(1-i,1+i))/2. There is a deterministic exact algorithm for C tensor-powered k times, on 2^k complex coordinates, using O_h(2^k(k+1)^theta) exact complex field and logarithmic-word address operations. Preparation and indexing are charged. Here h is fixed before input k, not part of the input. This distinction is essential because all hidden constants and fixed tables depend on h.

Using the pinned source's uniform local compiler (`loc:compiler`) and its synchronization and all-length transport, the unnormalized DFT F_n has cost

O_h(n(log n)^theta(log log n)^(4-theta)).

The cost model supplies one specified primitive root of explicitly computable order D<1024n^3. Coefficients and exact intermediate values are unrestricted; no precision or bit-cost assertion is made. At h=24, theta<1-39/10^11, hence the cost is O(n(log n)^(1-38/10^11)).

This is an extension of the released h=100 construction, with source attribution retained throughout. The tiny exponent improvement is not an implemented practical Fourier speedup.

## Source identity and notation

OpenAI, *An explicit power saving for the exact discrete Fourier transform*, September 25, 2026, [pinned collection commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/build/sections).

The four retained TeX files have Git blob identities checked by `verify.py`. They are text-source evidence snapshots, not mathbox PDF-cache entries. We read their complete contents. This derivation's P is the source W_*, its a replaces 71, and its h+1 replaces the literal 101. The source's binary-space line P is denoted L below to avoid a collision with the number of padded roles.

## 1. Scalar identity for arbitrary auxiliaries

Let T be the family of three-element subsets of {1,...,h}. Two distinct triples are adjacent precisely when their intersection is even, hence 0 or 2. For a fixed triple there are d adjacent triples: choose three outside it, or choose two inside and one outside. Side wires are indexed by **ordered** adjacent pairs. This ordering is required for vd, not vd/2.

Define (Vx)_(S,T)=x_T, (Gx)_j=sum_(T containing j)x_T, (Gx)_*=sum_T x_T,

(JA)_S=-sum_(T adjacent S)(|S intersection T|-1)A_(S,T)/2,

(Rc)_S=(sum_(j in S)c_j-c_*)/2.

The S,T coefficient in RG is (|S intersection T|-1)/2. It is 1 on the diagonal, 0 when the intersection has size 1, and is canceled by JV for intersection 0 or 2. Therefore RG+JV=I for every h>=3.

Perform, in order, y-=JA, y-=Rc, A+=Vx, c+=Gx, y+=Rc, y+=JA, c-=Gx, A-=Vx. This sends (x,y,A,c) to (x,y+x,A,c) for **arbitrary** starting A and c. Its inverse is the reverse sequence with signs reversed. Three invocations, from X to Y, inverse from Y to X, then X to Y, send (X,Y) to (-Y,X), restoring auxiliaries. Organize these on triples of indices (d1,d2,d3) in T^3, using one coordinate index per stage. There are 3v^2 invocations, each with vd side wires and h+1 central wires. Two data banks contribute 2v^3 more wires, giving W above.

## 2. Binary frames and admissibility for variable h

Let D=F_2^h with the ordinary dot product. Every triple indicator t has norm one. Indicators of adjacent triples are orthogonal. In D tensor-powered three times, u=t1 tensor t2 tensor t3 has norm one and integer Hamming weight 27.

For a nondegenerate subspace U of F_2^m define the orthogonal projection P_U and q_U(x)=wt(P_U x) mod4. Let J be the normalized Walsh matrix and Phi_U=J diag(i^q_U) J. These matrices establish identities; the algorithm does not run J.

If V=U orthogonal-sum E and E has an orthonormal basis z1,...,zr, then

q_V(x)-q_U(x)=sum_j wt(zj)[zj dot x] mod4.

This follows because binary orthogonality makes weight additive modulo 4. Every basis weight is odd. Walsh conjugation thus expresses Phi_V Phi_U^-1 as r factors C_z or C_z^-1, where C_z=((1+i)/2)I+((1-i)/2)R_z and R_z translates by z. Since C_z^2=R_z, each inverse costs one forward kernel and a translation. An invertible binary change of coordinates makes each forward kernel one copy of C along one coordinate direction.

Keep exactly the gate labels in source `net:labels`, with variable h. At stage j let E=D^(tensor(j-1)), L the line of the preceding triple tensor, B=L^perp in E, and Q the line of the future triple tensor. Source labels are zero except the X wire's line <u>; sink labels are the full space except the Y wire's <u>^perp. The physical chronology of the inverse second stage is still Y-side, Y-center, X-side, X-center, Y-center, Y-side, X-center, X-side. Reversing the scalar signs does not change that label table.

The source's complete residual list depends only on the orthogonal decompositions E=B orthogonal-sum L, D=<t> orthogonal-sum t^perp, and for adjacent t_X,t_Y,

t_Y^perp=<t_X> orthogonal-sum <t_X,t_Y>^perp.

Thus every consecutive pair of labels is nested and nondegenerate for variable h. To ensure an orthonormal residual basis, not merely nondegeneracy, observe that t^perp and <t_X,t_Y>^perp contain coordinate units outside supports of size at most 3 and 6. Such units exist whenever h>6. The nonzero complements B and Q^perp contain coordinate units outside tensor supports of sizes 3^(j-1) and 3^(3-j), respectively; since h>3, these supports are smaller than their ambient dimensions. The zero complements at the empty tensor boundaries are omitted. All remaining factors are full spaces or norm-one lines. Tensor products and nonzero orthogonal sums retain a norm-one vector and nondegeneracy.

A finite nondegenerate symmetric binary space containing a norm-one vector has an orthonormal basis. Split unit lines until the remaining part is alternating; it splits into symplectic planes. A unit vector w and an orthogonal symplectic pair p,q can be replaced by w+p,w+q,w+p+q, three orthogonal unit vectors, absorbing each plane. This is a constructive finite binary-linear-algebra argument. Therefore the full residual argument works for every h>6, with no parity restriction on h.

## 3. Directional budget and all physical roles

Along all physical wires, signed dimension changes telescope to Wm-2v^3. The only decreasing edges are the row3-to-row4 central edges; there are 3v^2(h+1), each decreasing by h. Replacing signed changes by absolute changes charges these losses twice. Thus the number of directional kernels is

s=Wm-2v^3+6v^2(h+1)h=Wm-Delta.

The frames commute with scalar gates acting on whole arrays. Intermediate frames cancel. The exceptional X-to-Y terminal frame ratio is R_u C^(tensor m), since

wt(P_(u-perp)x)-wt(P_u x)=wt(x)+2[u dot x] mod4.

Here wt(u)=27 is odd. Correct the known translation and the bank signs at the end. Every auxiliary role also undergoes C^(tensor m), rather than being assumed to start at zero. Tensoring all frames with f columns and spectator bits gives the same interface for C^(tensor mf) on every physical role.

Delta>0 exactly when v>3h(h+1). For h>=3 this is h^2-21h-16>0. It fails at h=21, holds at h=22, and increases thereafter. Hence h>=22 guarantees both the geometric admissibility h>6 and a strict saving. Also Delta<2v^3<=W<=P, so m-1<lambda<m, in particular 1<lambda<m.

## 4. Exact batching with the changed constants

Pad W roles to P=2^a, spending m directions on each extra role. The new total is S=Pm-Delta, so S/P=lambda. Set the base threshold K=m(a+1). For k>=K write k=mf+r with 0<=r<m and f>=a+1. Each directional step decomposes into 2^(k-f) fibers of length 2^f. Since k-f>=(m-1)f>=a, that fiber count is divisible by P. There are no partially filled recursive batches.

The source's column-table digit traversal and packing argument uses only that m and P are fixed. It therefore remains O_h(2^k), with logarithmic-size address words. If t(k) is the cost of simultaneously transforming P arrays divided by P2^k, then

t(k)<=A_h+lambda t(floor(k/m)).

All smaller k are computed directly with a fixed bound. Unrolling the recurrence gives t(k)=O_h((k+1)^theta). A single-array transform initializes P-1 additional roles to zero at O_h(2^k) cost. This is mathematically legitimate in the stated asymptotic model, although astronomically impractical.

## 5. Downstream transfer and exact exponent

The local compiler uses only the fixed 2x2 kernel C and contains no h, m, W, Delta, lambda, or 71 assumption. Its Newton/Toeplitz decomposition, restored borrowed-coordinate replay, and fixed six-C shear word therefore need no alteration. Synchronization calls the tensor algorithm on sectors of dimension 2^k with k<=number of axes; it uses only its exponent theta>0. The all-length construction uses coprime small-prime axes and a power-of-two factor, then chirp convolution. Again h enters only through the tensor exponent and fixed constants. It yields the claimed n(log n)^theta(log log n)^(4-theta) bound; the root order bound is unchanged.

At h=24 the exact checker verifies m=13824, W=34666942577344, P=2^45, Delta=1835266048. Put epsilon=Delta/(mP)=448063/118747255799808. Rational arithmetic verifies

epsilon > (39/10^11)(48/5),

sum_(j=0)^39 (48/5)^j/j! > 13824.

Positivity of the remaining exponential series gives log(m)<48/5, so epsilon>(39/10^11)log(m). Since 1-epsilon<exp(-epsilon), lambda=m(1-epsilon)<m^(1-39/10^11), proving theta<1-39/10^11. The fixed loglog power is eventually at most (log n)^(1/10^11), establishing the pure-log exponent 1-38/10^11. No floating comparison is used in this conclusion.

## Audit boundary

The universal derivation above is separate from the finite tests. Source equations, label decompositions, recurrence and compiler interfaces were self-reviewed. The checker verifies rational counts, source identity, scalar schedules, and selected small exact phase identities; it is not a formal proof of the whole algorithm. Independent audit should start from the raw source and quantified claim, not the author's verdict. Novelty is unverified. No claim of global optimality in h, an implementable crossover, numerical stability, finite-field applicability, or bit-complexity improvement is made.
