# Eliminate a redundant central wire in the exact DFT network

Written derivation, self-review; fresh independent audit pending. No novelty claim. The modification is allowed in the exact-complex-field DFT model. It is **not** automatically valid in the earlier Gaussian-dyadic integer-multiplication model, because it uses1/3.

## Claim and assumptions

Take the pinned OpenAI triple network described in `../dft/PROOF.md` and raw `../dft/sources/network.tex`, collection commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Fix h>=21, v=binom(h,3), d=binom(h-3,3)+3(h-3), m=h³. There is a version with

W'=2v³+3v²(vd+h), Delta'=2v²(v-3h²).

Let P' be the smallest power of two at least W', a'=log2(P'), lambda'=m-Delta'/P', and theta'=log_m(lambda'). The arbitrary-role tensor bound is O_h(2^k(k+1)^theta'). With the same upstream exact-width compiler and all-length transfer it gives O_h(n(log n)^theta'(loglog n)^(4-theta')) DFT cost, including preparation and logarithmic-word addressing, with one supplied specified root of order<1024n³. Every h is fixed before the input. No numerical stability, practical crossover, or bit-complexity assertion is made.

At h24, theta'<1-52/10^11, so the pure-log bound is O(n(log n)^(1-51/10^11)). The fixed-side-correction central rank is exactly h, proving that fewer central coordinates cannot represent that same central matrix via a linear gather/scatter factorization.

## The new scalar identity

Let B be the v×h triple-incidence matrix B_(S,j)=1 if j belongs to S, else0. The published gather is G=B^T with one additional total-sum row. But each triple has cardinality3, hence 1_h^T G=3·1_v^T. The extra gather row is redundant.

Delete the extra central wire. For c in C^h define

(R'c)_S=(sum_(j in S)c_j-(1/3)sum_(j=1)^h c_j)/2.

The coefficient of x_T in R'Gx is (|S intersection T|-1)/2, exactly the old central matrix M. Keep the old side injection JV, so JV+R'G=I_v. The eight-row sequence is now y-=JA, y-=R'c, A+=Vx, c+=Gx, y+=R'c, y+=JA, c-=Gx, A-=Vx.

Its net change is y+=(JV+R'G)x=x, and it restores A and c. This identity holds for arbitrary original c; it does not assume that c satisfies any relation to a deleted coordinate. Thus we are defining a new h-coordinate circuit, not restricting the old circuit to a subspace of initial states. The reverse sequence with negated signs is its inverse. The same three-stage shear composition sends (X,Y) to(-Y,X) and restores auxiliaries.

The new scatter uses all h central values, but the published central gate already includes all targets and central wires. The gather/scatter remain fixed finite linear maps, so the unchanged common-frame commutation argument applies. The rational1/3 scalar is prepared once by dividing1 by3, whose nonzeroness is explicit. It requires no new root or operation outside the DFT cost model.

## Labels and directional budget

Keep all data and side labels, and the published label path on each of the surviving h central wires. Deleting one identically labeled central role does not alter an inclusion or an orthogonality relation. The geometric label dimension is still h: reducing the number of central roles is not reducing the ambient binary label space.

All residual complements have an orthonormal binary basis exactly as in the audited variable-h derivation: h>6 leaves coordinate units outside supports of at most six; tensor complements also have norm-one witnesses. The stage-two reversed schedule has the same physical touch pattern as before. Its linear maps changed but the wires touched and their common labels did not.

There are3v² invocations, each with vd side roles and h central roles. This proves W'. The signed dimension budget is W'm-2v³. There are3v²h central decreasing edges, each losing h dimensions. Thus

s'=W'm-2v³+6v²h²=W'm-Delta'.

Every surviving auxiliary role has source frame0 and final full frame; hence all roles undergo the same tensor transform, including arbitrary initial auxiliary data. No hidden zero initialization has replaced that requirement.

The strict saving condition is binom(h,3)>3h², equivalently h²-21h+2>0 for h>0. It fails at h20 and holds at h21, after which the polynomial increases. For h>=21, 0<Delta'<2v³<=W'<=P', so1<lambda'<m. Padding and exact batching are unchanged with threshold K'=m(a'+1). The recurrence t(k)<=A_h+lambda' t(floor(k/m)) yields the stated tensor exponent. Downstream compiler, synchronization and root-order arguments use only C, theta'>0 and fixed constants, so they preserve the DFT conclusion.

## Exact h24 certificate

The independently reproducible rational checker verifies

v=2024, d=1393, m=13824, W'=34666930287616, P'=35184372088832,

Delta'=2425172992, s'=479235641870830592,

epsilon'=Delta'/(mP')=2368333/474989023199232.

It checks epsilon'>(52/10^11)(191/20) and sum_(j=0)^39 (191/20)^j/j!>13824. The positive exponential series implies log(m)<191/20, so lambda'<m^(1-52/10^11). Absorb the fixed loglog power in (log n)^(1/10^11) for sufficiently large n. This proves the final exponent1-51/10^11 without floats.

## Optimal central rank for this fixed side correction

The required central matrix is M=(BB^T-J_v)/2. Since B1_h=3·1_v,

M=B H B^T, where H=(I_h-(1/9)J_h)/2.

For h>=4,

B^T B=alpha I_h+beta J_h,

alpha=(h-2)(h-3)/2>0 and beta=h-2>0. This follows by counting triples containing a given point or pair. Therefore B has full column rank. H has eigenvalue1/2 on the sum-zero subspace and (9-h)/18 on constants. Consequently rank M=h except at h9, where rank M=h-1. One may also derive its nonzero spectrum from HB^T B: (h-2)(h-3)/4 with multiplicity h-1 and (9-h)(h-1)(h-2)/12 once; the remaining v-h eigenvalues are zero (with one more zero at h9). At h24 these are231/2 and-1265/2; their multiplicities give trace2024, agreeing with the diagonal entries1.

Any factorization M=RG through c central coordinates has rank M<=c. Thus c>=h for h>=21, and the new factorization achieves the minimum. This only concerns this fixed side correction and this linear gather/scatter interface. It does not rule out different side matrices, scalar networks, label families, nonlinear algorithms, or lower DFT complexity.

## Evidence and independent review

`verify.py` reconstructs both old and new central maps over rationals, checks their equality on arbitrary inputs, executes the new schedule and inverse with nonzero auxiliary values, verifies incidence Gram/rank formulas, and rejects deliberate missing-total-correction and wrong-budget variants. The finite tests do not prove the full label theorem; the symbolic argument above carries that step. Raw pinned sources remain in the sibling directory and are read-only. Prior-art classification of the original h24 tuning is in `../dft/LITERATURE.md`; this elementary central elimination has no established novelty status.
