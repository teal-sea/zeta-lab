# Independent central-compression audit

## Claim and verdict

Replace the h+1 central coordinates in the pinned triple network by h
coordinates. Retain incidence gather G=B^T, replace scatter by
R'c=(Bc-(sum_j c_j)1_v/3)/2, and keep the side maps and surviving labels.
For every fixed integer h>=21 the proposed counts are
W'=2v^3+3v^2(vd+h) and Delta'=2v^2(v-3h^2). With physical padding
P'=2^ceil(log2 W'), the proposed tensor exponent is
theta'=log_(h^3)(h^3-Delta'/P'). At h=24 the all-length exact-complex DFT
claim is O(n(log n)^(1-51/10^11)), under the same root and word-cost model.

**Primary verdict: conditional on a named input.** The new central circuit,
dimension budget, h>=21 threshold, fixed-correction rank optimality and exact
exponent pass independent derivation and bounded exact tests. The final
all-length DFT implication is conditional on the pinned upstream exact-width
compiler and transport, as in the earlier independent audit at
`../dft/AUDIT.md`. No new gap was identified in applying those interfaces.
This is neither a full implementation nor a formal proof of the upstream DFT.

The author proof was visible during this audit; this was not a blind review.
The scalar identity, rank proof, costs, and tests below were independently
reconstructed, and no producer checker was imported or executed as evidence.

## Exact revision and dependency graph

Source commit supplied by the parent:
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Raw source leaves remain in `routes/dft/sources/`; their source provenance and
interfaces are recorded in the sibling audit. This pass does not claim a
new independent authentication of that remote commit.

Reviewed `routes/dft-central-compression/PROOF.md` SHA256:
`d33bf988ebc1d096d2d8f3d9c7f67cd038d1db4ca344470ea584ad7a3d99a2c5`.
Reviewed `verify.py` SHA256:
`c55fd74758606005f5c14ac3fa564c38a11db351f645b981877c8678c2e11e64`.
After the independent run, the producer added an old-budget negative control
to its checker. The final checker SHA256 is
`35a9d7259d6f70095c077689aedc7938c32c26e911bfc6f804ac535898a63d84`.
That added assertion was inspected; the proof hash and audited mathematical
target remain unchanged. The independent run output intentionally retains
the producer revision present when it executed.

The proof dependency chain is:

1. Each incidence column has sum three -> R'G equals the original central
   matrix M [internal algebra].
2. M+JV=I -> eight-row cancellation for independent arbitrary auxiliaries ->
   three global bank shears [internal algebra and independent small checks].
3. Unchanged gate groups and surviving labels -> same residual bases and
   terminal frames, one fewer center path per invocation [raw source geometry,
   previously audited and checked again for the changed gates].
4. New role/loss counts -> positive saving for h>=21 -> exact padded recursive
   batching [internal count and recurrence].
5. Tensor bound -> DFT bound [named upstream compiler/transport inputs].
6. Exact rational certificate -> stated eventual pure-log exponent
   [internal analysis and independent arithmetic].

The rank lower bound is separate: incidence Gram matrix and H factorization
-> rank M -> minimal inner dimension of a factorization M=RG. It is not used
to claim global optimality of the network or DFT algorithm.

## Decisive algebra and gate audit

For a basis input x_T, Gx has ones precisely at the three elements of T,
so sum_j(Gx)_j=3. For each S,
(R'G)_(S,T)=(|S intersection T|-1)/2. Keeping the old JV therefore gives
R'G+JV=I. In particular, no relation among the *initial* c_j is needed:
the first subtraction uses R'c, and the later addition uses R'(c+Gx).
Their difference is R'Gx for every c in C^h. The subsequent subtraction
of Gx restores the central contents. The same cancellation holds for the
side register. Correlation with other data does not affect this linear-map
identity.

The new scatter is dense across central coordinates. This does not force
new frame changes: the existing central gates at rows 1 and 4 already touch
all targets and all central wires, sharing one common label. The gather
gates at rows 3 and 6 similarly share the source-bank label. The old sparsity
of individual scatter coefficients was not a frame-commutation assumption.
In the reversed second stage, the physical grouping sequence remains the
same. Thus pointwise scalar maps still commute with the common frames.

Each surviving central role traverses the old path; deleting the total role
removes its complete source-to-sink path. It does not change the binary
ambient factor D=F_2^h. In particular every central decrease still has
dimension h. There are 3v^2h of them, so the absolute directional cost is
W'm-2v^3+2(3v^2h)h. This is exactly W'm-Delta'. All surviving auxiliary
source labels are zero and sink labels full, hence they receive the same
tensor transform on arbitrary initial contents. No zero-workspace shortcut
was introduced.

For h>0, v>3h^2 is equivalent to h^2-21h+2>0. The polynomial is negative
at 20, positive at 21, and strictly increasing thereafter. The independent
integer checks give Delta'(20)=-155952000 and Delta'(21)=24764600.
The residual unit-vector argument already holds for h>6, so h=21 has no
geometric exception.

With a'=log2 P' and K'=m(a'+1), k>=K' gives f=floor(k/m)>=a'+1 and
k-f>=(m-1)f>=a'. Each directional step therefore partitions exactly into
P'-array recursive batches, with no fractional last batch. Padding pays m
directions per added role. The recurrence coefficient is consequently
(P'm-Delta')/P', not (W'm-Delta')/W'. The scalar work added by computing
the central total remains a fixed cost per array entry for fixed h.

## Rank statement and its limits

B1_h=3*1_v, so M=BHB^T with H=(I_h-J_h/9)/2. Counting triples containing
one and two specified elements gives
B^TB=((h-2)(h-3)/2)I_h+(h-2)J_h. For h>=4 both its eigenvalues are
positive; B is injective and B^T surjective over C. Therefore rank(BHB^T)
equals rank H, not merely an upper bound on it.

H has eigenvalues 1/2 on the (h-1)-dimensional sum-zero space and
(9-h)/18 on constants. Thus rank M=h for h>=4 except at h=9, where it is
8. At h=3 the formula asserting full column rank of B does not apply:
there is only one triple and M has rank 1. The producer restricts that
argument to h>=4, so this is not a counterexample to its statement.

The nonzero eigenvalues are ((h-2)(h-3))/4 with multiplicity h-1 and
((9-h)(h-1)(h-2))/12 once, with the zero-eigenvalue interpretation at h=9.
At h=24 these are 231/2 and -1265/2; their trace is 2024=v.
Any linear factorization through c central scalar coordinates has rank at
most c. Hence h central coordinates are necessary and sufficient **for this
fixed correction M and single linear gather/scatter factorization** when
h>=21. Multiple replays, changed side maps or other computational models
are not covered by that lower bound.

## Arithmetic model

Exact complex field operations can form 3 from 1 and invert it once. That
denominator is nonzero, and all added coefficients are rational, so no new
root of unity or complex zero test is needed. The inherited compiler and
root-order bound <1024n^3 are unaffected.

R' has coefficient 1/3 on an incident coordinate and -1/6 on a nonincident
one. Those coefficients are not Gaussian dyadic. Thus this particular
compression is not an implementation over the Gaussian-dyadic coefficient
ring, and it must not be inserted into the integer-multiplication proof
without a separate construction and precision audit. This observation does
not rule out a different dyadic factorization.

## Independent checks, exponent and obligation status

`check.py` uses only standard-library exact integers and fractions. It does
not load producer code. It checks the full three-stage exchange at h=4,
with 64 entries in each bank, 48 invocations, and distinct nonzero arbitrary
central/side values per invocation. All auxiliaries are restored. Mutations
replacing the total coefficient 1/3 by zero or 1/2 fail the required exchange.
It independently computes literal ranks of 2M by integer elimination at
h=4,6,9, obtaining 4,6,8; checks all 2024 possible T against one S at h=24;
and checks count/batching boundaries for h=7,...,128. These finite ranges
supplement the universal algebra, not replace it.

At h=24 it obtains W'=34666930287616, P'=35184372088832,
Delta'=2425172992 and epsilon'=2368333/474989023199232. Independently of
the producer's 9.55 logarithm bound, a rational exponential partial sum
through degree 64 proves log(13824)<477/50=9.54. Rational comparison gives
epsilon'>(52/10^11)(477/50), hence
1-theta'=-log(1-epsilon')/log(13824)>52/10^11.
The fixed (loglog n)^(4-theta') factor is eventually dominated by
(log n)^(1/10^11), proving the stated pure-log exponent 1-51/10^11.
This is an eventual asymptotic bound, with no feasible crossover claim.

| Obligation | Status |
|---|---|
| Central identity and all initial auxiliary values | Passed |
| Three-stage inverse chronology | Passed |
| Common-frame gate grouping and retained residual bases | Passed |
| Changed role and loss counts; h=21 boundary | Passed |
| Padding, floors, scalar preparation and address overhead | Passed in stated fixed-h model |
| Rank lower bound and h=9 exception | Passed in stated fixed-correction scope |
| Exact exponent arithmetic | Passed |
| Entire upstream DFT compiler correctness | Conditional on named source inputs |
| Gaussian-dyadic/integer-multiplication extension | Not established |
| Novelty, global optimality or practical performance | Not addressed |

## Source leaves and reproducibility

The controlling raw leaves are `network.tex` labels `net:schedule`,
`net:scalar`, `net:labels`, `net:residuals`, `net:telescoping`,
`net:finite-interface`, `net:indexing`, and `net:tensor-bound`;
`local.tex` `loc:compiler`; `synchronization.tex` `prop:tensor-fourier`;
and `all-lengths.tex` `eq:working-transform`, `eq:master-root`,
`eq:root-size`. Exact line locators are in the preceding sibling audit.
Novelty was not inferred from this audit or absence in those sections.

Reproduce from the task workspace:

```sh
zeta-research/.venv/bin/python audits/dft-central-compression/check.py
```

Run succeeded; output is in `check-results.json`. No paid/heavy compute or
Git operations occurred. The strongest safe statement is a written and
independently checked exact-complex central-register improvement, with the
all-length conclusion conditional on the inherited compiler. No missing
implication was found within this modification. Independent verification
of the upstream compiler remains the highest-value separate audit step.
