# DFT overlap check, 2026-10-08

**Verdict: the h=24 result is an optimized instantiation and a formal quantitative corollary of the released construction, not a new Fourier mechanism.** The general h>=22 statement is not explicitly stated in the inspected source, but its proof is obtained by retaining variable parameters in existing identities. Independent correctness audit does not establish novelty. The best description is a reproducible sharpening of the released constants with a parameter-admissibility derivation.

## Precise source question

Does earlier primary work already quantify the ground-set size h, contain the smaller motif, or imply the same exact-arithmetic exponent? Does the proposed extension change the algorithmic model? Search scope: the pinned release's backwards citations `motif`, `exactfourier`, `Alon1998`, and prior exact DFT complexity results cited there; public Git history of the two motif source files; English primary material available 2026-10-08. This is an overlap check, not a global novelty search.

All release source locators below are relative to `https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`. TeX snapshots are retained in `literature-sources/`, preserving contents with possibly one extra terminal newline from the file tool. Git blob SHA identifies the authenticated original bytes, distinct from the snapshot SHA256.

## Primary sources and exact overlap

1. **OpenAI, An explicit power saving for the exact discrete Fourier transform, September 25, 2026.** `preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/build/sections/network.tex`, blob `991c7706b7a03f45fbf3ba22bfb4372bf111fb4a`. Exact places: `net:parameters` fixes h=100; `net:residuals` and its proof already give Delta=2v²(v-3h(h+1)); `net:padding` and `net:tensor-bound` turn the saving into the exponent. These identities already contain the mathematics optimized by h=24. The literal 100 is chosen, not used as a special algebraic property. Our work checks which replacements preserve the proof, corrects the recursive cutoff to m(a+1), and proves the displayed stronger exponent with exact rational inequalities. Classification: **formal corollary not stated**, with parameter-range bookkeeping.

2. **OpenAI, Integer multiplication below n log n, September 23, 2026.** `preprints/Integer-multiplication-below-n-log-n-September-23-2026/build/sections/03-motifs.tex`, blob `cdb0ba527aa8df5d57c151183fd3893c1a7e21ab`. It starts by fixing h=100, v=binom(h,3), m=h³ and uses precisely the same three-stage complex triple network. The source's `lem:motif-residuals` gives the variable-symbol budget Wm-2N+2Ich, with c_b=100, c_c=101. The complex construction is explicitly over Gaussian dyadic scalars, unlike the later general exact-complex DFT model. It credits the graph's degree-one intersection representation to Alon. No variable-h theorem or h=24 value occurs in the inspected complete section. Classification: the **same construction**, not an independent antecedent that leaves us a new mechanism. Parameter variability is evident in its proof, even though its selected values are fixed.

3. **OpenAI, Finite tensor savings and exact Fourier circuits, September 25, 2026.** `preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/build/sections/01-introduction.tex`, blob `2f95210b98f4157658aaa494a218cbddccb35b94`; `08-reflection.tex`, blob `53c95e2728809fd6d753716abd1f62ada151d011`. Exact theorem `thm:finite-win` asserts existence of an invertible nonmonomial finite matrix A and a word for A tensor b with fewer than b q^(b-1) A calls. `thm:main` is a nonuniform liminf statement along an unbounded sequence of DFT lengths. Its price/reflection argument has a separate integer d>30 and does not parameterize our triple network. It proves a **more general existence principle in a different uniformity contract**, not the numerical h24 exponent. Transferring any finite saving is already an upstream mechanism, not ours.

4. **Noga Alon, The Shannon Capacity of a Union, Combinatorica 18 (1998), 301–310, DOI10.1007/PL00009824.** [Author PDF](https://www.tau.ac.il/~nogaa/PDFS/shann3.pdf), checked ten-page primary text, especially §3 remark after Theorem1.1, pp.5–6. Its Frankl–Wilson variant uses subsets of size p²-1, a modular intersection graph and real polynomial representations of its complement. At p=2 this supplies triples and a degree-one real intersection polynomial. The upstream network explicitly changes the ground-set size to100. Alon's paper is about graph capacity, not this DFT circuit; it establishes the combinatorial ancestry and defeats any claim that the subset/intersection idea originated here. No PDF hash recorded because the web provider supplied extraction rather than downloaded bytes.

5. **Josh Alman and Kevin Rao, Faster Walsh–Hadamard and Discrete Fourier Transforms From Matrix Non-Rigidity, arXiv2211.06459v2, June14 2023.** [Primary full text](https://arxiv.org/html/2211.06459v2), §1.2, Theorem1.2 and §§5–8. Improves the leading real-operation constant for power-of-two DFTs to15/4; it does not assert an all-length logarithmic-power saving. Source model and result were checked, not its entire proof. Classification: adjacent algorithmic prior art, not overlap with our displayed exponent. Its practical small-constant setting is very different from the enormous fixed motif here.

6. **Nir Ailon, arXiv1403.1307v5, July24 2014.** [Primary version](https://arxiv.org/abs/1403.1307v5). The abstract states a conditioning-dependent lower bound and an extra-space extension. This supplies a model warning, not a theorem used in our derivation. We did not verify every hypothesis of its full theorem, so it is not used to derive an impossibility claim. Our circuit has unrestricted intermediate conditioning.

Source bibliography identities: DFT references `aafd3724963d27571393c6b507b571088aaaf7da`; integer-multiplication references `bf01cae12597f2777199c8ee74ee9f6933a1b56e`.

## Public history check

GitHub's path-filtered commits endpoint returned one source-changing commit for each of the two motif files, `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, initial commit2026-10-06T21:58:50Z. Thus no earlier public revision of these paths was exposed by that history query. This does not exclude earlier unpublished drafts, versions under another path, or other authors' work. We have no basis to claim the first parameter optimization.

## A different, concrete circuit change

The published complex network stores h coordinate sums plus a total sum. These are dependent: each triple has size3, so sum_j(Gx)_j=3 sum_T x_T. Delete C_* and replace scatter by

(R'c)_S = (sum_(j in S)c_j - (1/3)sum_j c_j)/2.

Then R'G has exactly the old coefficient (|S intersection T|-1)/2. This changes the circuit's number of physical roles and its dimension-loss budget; it is not merely h tuning. The subtraction/copy/add/restore schedule still must be checked for arbitrary old central values. The frame labels are unchanged on the surviving h central wires, so the proposed loss is 3v²h², rather than3v²h(h+1). Its candidate saving is 2v²(v-3h²), allowing h>=21. At h24 it gives Delta2425172992 and a floating exponent gap about5.22969896e-10. Those numbers alone do not establish the circuit result.

**Critical model distinction:** R' uses1/3. This is permitted by the exact-complex-field DFT model but not automatically by the earlier network's Gaussian-dyadic scalar restriction. Do not transplant the modification to the integer-multiplication theorem without a separate precision/arithmetic audit. No occurrence of this deletion was found in the checked two source sections; the algebraic elimination itself is elementary and no novelty is claimed.

**Cheap discriminator:** exact eight-row forward/reverse execution with nonzero arbitrary auxiliaries, then a fresh label-and-budget audit after deleting C_*. If this passes, it is a small structural circuit simplification and useful starting point for the genuinely different combinatorial direction below.

## Combinatorial direction beyond h tuning

Search for **low-rank rational fitting matrices on a different collection of odd binary vectors**, rather than the full Johnson triple family. Let v norm-one labels in F_2^h have a rational matrix K with diagonal1 and off-diagonal support only on orthogonal pairs. A rank-c factorization K=RG drives the central gather/scatter, while the side channel cancels off-diagonal entries. With e directed off-diagonal nonzeros the same three-stage architecture suggests W=2v³+3v²(e+c) and Delta=2v²(v-3ch). The necessary gain is v>3ch; central rank compression is the first simplest case.

A bounded first experiment can enumerate constant-weight odd-vector families at h<=12 and solve small exact rational fitting/rank candidates, tracking both c and e. It must also check every binary residual is nonalternating; adding one always-unused coordinate is a conservative way to retain a norm-one vector in complements but raises h and may destroy the gain. A useful target is a certificate with smaller h³ and smaller padded W at comparable exponent saving, not a bigger brute-force search. The labels, fitting matrix, exact rank factorization, nonalternating residual proof, and budget form the audit artifact. This is a research question, not a theorem or an assertion of unexplored territory; minrank/graph-representation literature must be checked before making novelty claims.

## Coverage limits

No exhaustive forward-citation search, no zbMATH/MathSciNet coverage, no private drafts, and no general novelty theorem. The result of this check is positive overlap attribution: the parameter sweep reuses an existing construction and transfer. The central-wire change and new fitting-matrix search have not received a comprehensive prior-art review.
