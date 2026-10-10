# Bounded prior-art check: DFT central-wire compression

Checked 2026-10-08. Scope: deleting the dependent total gather from the
complex triple network, implementing it with 1/3, and the rank-h lower bound
for the unchanged central correction. This report does not change the proof
or its independent audit.

**Conclusion:** the fixed-cardinality dimension reduction is established
prior-art mathematics. The exact DFT circuit deletion was not found in the
primary sections checked. The appropriate classification for this package
is a **formal corollary not stated**: an elementary algebraic circuit
simplification of the released construction, with its auxiliary restoration,
frame budget and exponent checked explicitly. No worldwide priority claim
or claim of a new rank/compression principle is supported.

## Precise target

For triples S,T in [h], the unchanged central matrix is
M_(S,T)=(|S intersection T|-1)/2. Writing B for triple incidence,
the published gather stores B^T x and also 1_v^T x. Since
1_h^T B^T=3*1_v^T, the latter coordinate can be reconstructed by dividing
the sum of the former by three. The modified scatter is
R'c=(Bc-(1_h^T c)1_v/3)/2. The circuit application must still restore
arbitrary initial auxiliaries and respect common-frame gate grouping.
The independent audit establishes those points separately from this search.

## Closest primary sources

### 1. The released DFT construction: exact circuit overlap

OpenAI, *An explicit power saving for the exact discrete Fourier transform*,
September 25, 2026, supplied pinned revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
[Pinned network source](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/build/sections/network.tex).
The complete local snapshot `routes/dft/sources/network.tex` was read in the
proof audit and its gather/scatter and count inspected again here.

`net:schedule`, `net:scalar`, `net:wire-count`, and `net:residuals` explicitly
use h+1 central roles, including the total sum. The source already supplies
the arbitrary-auxiliary cancellation, label geometry and the loss formula.
Deleting the dependent coordinate is not stated in the inspected section.
Our change retains its triple graph, side correction, three-stage network,
frames, compiler and recurrence. The new work is the concrete smaller
central realization and checked consequences, not a new Fourier mechanism.

### 2. Earlier integer-multiplication network: same matrix, different ring

OpenAI, *Integer multiplication below n log n*, September 23, 2026,
same pinned collection revision.
[Pinned motif section](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Integer-multiplication-below-n-log-n-September-23-2026/build/sections/03-motifs.tex).
Local snapshot: `routes/dft/literature-sources/motif-03-motifs.tex`.

Lines 44–64 introduce the h coordinate wires plus total wire in the complex
case. Lines 117 and 136 identify the same M and h+1 count. The section's
`lem:motif-residuals` already parameterizes the dimension loss as I*c*h.
Its complex scalar ring is explicitly Z[i,1/2]. The proposed scatter has
coefficients 1/3 and -1/6, so this particular realization leaves that ring.
Its admissibility over C does not prove a corresponding integer-multiplication
improvement. No deletion was found in this complete cached section. The
already existing h-wire *bit* network uses a different field and correction;
it is not the proposed complex circuit.

### 3. Alon 1998: matching intersection polynomial and an explicit dimension-reduction pointer

Noga Alon, *The Shannon Capacity of a Union*, Combinatorica 18 (1998),
301–310. [Author primary PDF](https://www.tau.ac.il/~nogaa/PDFS/shann3.pdf).
Checked §3's remark after the proof of Theorem 1.1 and §5's first bullet,
through the provider's full-text extraction.

The §3 real polynomial is
Q_A(x)=product_(i=1)^(p-1)(sum_(j in A)x_j-(p^2-1-ip)). At p=2 it is
sum_(j in A)x_j-1, the unnormalized polynomial behind M. The paper's selected
ground-set size is p^3; our variable h is a specialization of the formula,
not its numerical parameter choice. In §5 Alon states that the capacity
estimate based on sum_(i=0)^(p-1) binom(r,i) can be reduced to binom(r,p-1),
citing Alon–Babai–Suzuki. At p=2 these dimensions are r+1 and r.
That remark concerns graph-capacity estimates, not the DFT circuit or its
arbitrary-register interface. Classification: **partial or adjacent result
only** for the circuit; direct ancestry for its polynomial and dimension idea.

### 4. Alon–Babai–Suzuki 1991: the actual fixed-cardinality relation

N. Alon, L. Babai and H. Suzuki, *Multilinear polynomials and
Frankl–Ray-Chaudhuri–Wilson type intersection theorems*, J. Combinatorial
Theory A 58(2) (1991), 165–180,
[DOI](https://doi.org/10.1016/0097-3165(91)90058-O),
[author primary PDF](https://web.math.princeton.edu/~nalon/PDFS/suzuki1.pdf).
Checked §2, proof of Theorem 1.1, displayed equation (7), author manuscript
printed page 7 (PDF page index 7).

The proof incorporates the functions x_I(sum_j x_j-k), which vanish on
the characteristic vectors of a k-uniform family, and subtracts their
dimension from the degree-at-most-s polynomial space. At s=1 the vanishing
function is sum_j x_j-k itself. For k=3 over the reals or rationals this
gives 1=(sum_j x_j)/3 on the triple layer, exactly the dependency used in
our gather elimination. The paper attributes the proof technique to
Blokhuis. It does not state the DFT circuit modification or this fixed
matrix's exact spectrum. Classification: **known after translation of
notation** for the eliminated dependency; not a source for the complete
circuit claim.

## Rank claim: what is and is not being contributed

Our rank statement concerns this one fixed M, not the minimum rank over all
fitting matrices for a graph. Directly,

M=B(I_h-J_h/9)B^T/2,

B^TB=((h-2)(h-3)/2)I_h+(h-2)J_h.

For h>=4, B has full column rank; the middle factor has rank h except at
h=9, when it has rank h-1. Thus rank M=h for the relevant h>=21.
The lower bound on the intermediate number of scalar coordinates is the
elementary inequality rank(RG)<=inner_dimension. These calculations are
useful explicit checks, not evidence of a new general rank theorem. This
search did not locate a primary source stating this precise exceptional-h
spectrum, and does not infer novelty from that. The existing independent
proof supplies the claim without requiring an unverified external theorem.

## Search boundary and reproducibility

Two approaches were used: direct comparison against cached, pinned source
sections; and a backward citation trace from their Alon reference through
Alon's §5 to the author copy of Alon–Babai–Suzuki. This trace produced the
decisive positive overlap. The author PDFs were read via web extraction;
no PDF bytes were saved or hashed, since this task permits writing only this
report. Publisher metadata confirmed the 1991 DOI. Cached-source identity
records are in `routes/dft/LITERATURE.md` and the independent audit.

Supplementary web queries included:

- `"Fourier" "central" "motif" "Alon"`
- `"linear circuit" "triple" "intersection" "rank" Fourier`
- `"An explicit power saving" "Fourier"`
- `Fourier central wire compression` with a requested GitHub domain filter
- `"DFT" "central wire"`
- `Gottlieb inclusion matrices rank` and `Wilson diagonal form incidence matrices subsets`
- `"Multilinear polynomials and Frankl-Ray-Chaudhuri-Wilson"`

Several broad queries returned irrelevant results, including results outside
requested domain filters. They provide no meaningful negative evidence.
The exact-title query found the primary 1991 paper. No theorem from an
unverified Gottlieb/Wilson source is asserted here. No exhaustive forward
citation, Google Scholar, MathSciNet, zbMATH, non-English, or private-draft
coverage was achieved. The public revision history recorded in the earlier
producer report was not independently repeated in this task.

Suggested public wording, if publication is separately authorized:
“We remove a dependent gather coordinate from the released exact-complex
DFT network using the classical fixed-cardinality relation. We verify that
the smaller circuit still restores arbitrary auxiliaries and compute its
improved explicit dimension budget. No novelty is claimed for the underlying
linear-algebra reduction.”
