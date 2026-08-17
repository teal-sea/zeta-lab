# FRONTIER_MAP - state of the art, from primary sources, August 2026

Assembled 2026-08-17 by eleven parallel literature surveys; each entry
carries the URL its statement was checked against, or is marked
memory-unverified. Verbatim survey text is machine-scrubbed for the
hunts/ lexical rules; quoted wording is otherwise the surveys' own.
Judgment sections at the bottom are the campaign coordinator's.


## Territory A: proportions of zeros of zeta on/near the critical line ,  Levinson/Conrey mollifier records, the August 2026 unconditional "more than two thirds" inertia-compression framework, Montgomery–Taylor and Cheer–Goldston simple-zero constants, pair-correlation-conditional 100% results, distinct-zero proportions, and zeros of derivatives of xi

### Unconditional two-thirds theorem (Theorems A, B, D of the August 2026 paper)
- statement: Unconditionally, liminf_{T→∞} N*₀(T,2T)/N(T,2T) ≥ 2/3 (distinct on-line zeros), at least (2/3 − o(1))N(T,2T) zeros are simple and on the critical line, and with the optimal (Montgomery–Taylor) window the constant becomes 2 − 1/c*₁ = 3/2 − (1/√2)cot(1/√2) = 0.67250070367941164573…, where c*₁ = 2tan(1/√2)/(√2 + tan(1/√2)) = 0.75329606785607… and 1/c*₁ = 1/2 + 2^{-1/2}cot(2^{-1/2}) = 1.3274992963205883543… is the Montgomery–Taylor constant. Proportion H(λ) = 2 − 1/λ − λ/3 for band-limit λ ≤ 1 gives 2/3 at λ=1.
- constant: 0.67250070367941164573 (simple and on line, distinct on line); ceiling of method 0.68185
- status: unconditional | Claude (Anthropic); problem posed by J. Sumner, contextualized by R. Furman and L. Alpöge (2026)
- citation: 'More than two thirds of the zeros of the Riemann zeta function lie on the critical line', dated August 10, 2026, Anthropic preprint (not yet peer-reviewed); Lean 4 formalization at github.com/anthropics/zeta-23-lean (sorry-free, standard axioms)
- checked against: https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf (full PDF read); https://github.com/anthropics/zeta-23-lean
- technique: Compression of Weil's Hermitian explicit-formula form to a d ≈ λN dimensional Gabor family (modulated copies of a window ϕ at critical sampling density); zero side read by Sylvester's law of inertia (off-line pair {ρ,1−ρ̄} = signature (1,1) block) plus a rank–trace inequality via von Neumann's trace inequality; prime side is Montgomery's unconditional band-width ≤ 1 pair-correlation second moment (as made explicit by BGSTB 2024)
- bottleneck: Band-limit λ ≤ 1: for X ≫ T·l the off-diagonal prime terms require Hardy–Littlewood/pair-correlation information for α > 1. Remark 1.1: no configuration-by-configuration certificate reading only bandwidth-one data can exceed 0.68185; reaching 0.70/0.80/0.90 would need Fourier support out to ≈ 1.04/1.26/1.70
- tunable: window profile v = ϕ² (solved: v''+2λ²v=0 ⇒ cos(√2λs), the Montgomery–Taylor kernel); taper/ramp shape; weight function ψ(m) over multiplicities; number of moments used; sampling density; choice of invariants beyond tr and ‖·‖_F
- gap: The 0.6725007–0.68185 window inside bandwidth one is open: the proof uses only two traces (tr, tr²); the extremal-law ceiling 0.68185 has not been attained. The lab's prior-art gap-census transplant reaches 0.6725106958 (do not re-derive). Higher unconditional moments are unavailable for λ ∈ (2/3,1); conditional HL*(4,λ) would give 13/18 = 0.72222 (§7.5(f))

### Unconditional distinct-zeros proportion 5/6 (Theorem C)
- statement: Unconditionally liminf_{T→∞} N_d(T,2T)/N(T,2T) ≥ 5/6 = 0.8333…, improved by the optimal window to (3 − 1/c*₁)/2 = 0.83625035183970582287…; previous unconditional records were 0.6395 (Farmer 1995, via simple-zero proportions of ξ^(j)) and 0.6603 (Wu 2015)
- constant: 0.83625035183970582287 (unconditional); 0.85082 (RH, cubic weights); cf. 0.8477 (RH, CGdL 2020)
- status: unconditional | Claude (Anthropic); previous: D. Farmer; X. Wu (2026)
- citation: Same Anthropic preprint, Theorem C/D; Farmer, 'Counting distinct zeros of the Riemann zeta-function' (1995); Wu (2015)
- checked against: https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf
- technique: Integrality m² ≥ 3m − 2 (the CGG98 device) made unconditional: multiple on-line points and off-line pairs sit on the inertia-index side at flat charge 4, simple zeros on the rank side
- bottleneck: Same band-limit λ ≤ 1; sharpness: the extremal configuration (2N/3 simple on-line + N/6 on-line doubles) realizes tr = N, ‖·‖²_F = 4N/3, so no improvement from these invariants alone
- tunable: cubic weight ψ(m) = m/2 + (2m²−m³)/18 + (4/9)1_{m=1} (LP-optimal in span{m,m²,m³,1_{m=1}}); window in the third-moment functional 2m₂(1,v) − m₃(1,v) (= 0.68524… at v = cos(8s/5), unoptimized)
- gap: Under RH the paper's cubic certificate (§7.5(g)) gives N_d ≥ 0.85082… with an ad hoc window cos(8s/5); the window there is NOT optimized (only the weight is LP-optimal for that window), and no unconditional cubic route exists for λ ∈ (2/3,1)

### Levinson-method record for zeros on the critical line (still the record for N₀ counted with multiplicity)
- statement: κ ≥ 0.417293962 of the nontrivial zeros are on the critical line, and κ* ≥ 0.407511457 are simple and on the critical line. Obtained with mollifier ζ(s) + λ₁ζ'(s)/log T + … (d = 1, K = 3), two-piece mollifier with θ_C = 4/7 − ε (Conrey/Deshouillers–Iwaniec length) and Feng piece at θ_F = 6/11 − ε (incomplete Kloosterman sums, Pratt–Robles), explicit optimized polynomials P₁,P₂,P₃,Q and R = 1.1167 printed in §8
- constant: 0.417293962 (on line), 0.407511457 (simple and on line)
- status: unconditional | Kyle Pratt, Nicolas Robles, Alexandru Zaharescu, Dirk Zeindler (2020)
- citation: arXiv:1802.10521v3, 'More than five-twelfths of the zeros of ζ are on the critical line', Res. Math. Sci. 7 (2020)
- checked against: https://arxiv.org/pdf/1802.10521 (PDF §1, §8 read directly)
- technique: Levinson's method with autocorrelation-of-ratios evaluation (CFKRS/CFZ/CS) of the twisted second moment for coefficients (μ⋆Λ₁^{⋆k₁}⋆…⋆Λ_d^{⋆k_d}); proof of 'Feng's conjecture' on square-free main terms
- bottleneck: Mollifier length: θ = 4/7 − ε for the Conrey piece (Deshouillers–Iwaniec Kloosterman bounds); 17/33 − ε is the best generic-coefficient length (Bettin–Chandee–Radziwiłł); pushing any θ toward 1 is the whole game and is blocked by exponential-sum technology; diminishing returns in the polynomial degrees
- tunable: mollifier lengths θ_C, θ_F; number of Feng pieces K; derivative order d; polynomial coefficients of P₁, P₂, P₃, Q; R parameter
- gap: Note: this remains the record for N₀/N counted WITH multiplicity; the 2026 inertia result counts distinct on-line points (N*₀), so the two are formally incomparable at the count level even though 0.6725 > 0.4173. No Levinson-side improvement since 2020; the polynomial/parameter optimization was described by the authors as 'interim'

### History chain of κ and the mollifier-length ladder
- statement: Selberg 1942: κ > 0 (unspecified small); Levinson 1974: κ ≥ 1/3; Conrey 1989: κ > 0.4088 (with θ = 4/7 − ε via Deshouillers–Iwaniec); Bui–Conrey–Young 2011: κ > 0.4105 (two-piece with χ(s)-twisted second piece, y₂ = T^{1/2−ε}); Feng 2012: κ > 0.4107 rigorous with θ_F = 3/7, claimed 0.4128 with θ_F = 1/2 (gap found in [8,48,58,60]); Pratt–Robles 2018 validated θ_F = 6/11 − ε hence κ > 0.4128; PRZZ 2020: 0.417293962. Best generic Dirichlet-polynomial twist length: θ = 17/33 − ε (Bettin–Chandee–Radziwiłł, via Duke–Friedlander–Iwaniec trilinear Kloosterman improvements)
- status: unconditional | Selberg; Levinson; Conrey; Bui–Conrey–Young; Feng; Pratt–Robles; Bettin–Chandee–Radziwiłł (2020)
- citation: As catalogued in arXiv:1802.10521 §1.3 (with Feng's numerical value 0.417288 credited in §8); Heath-Brown 1979 observed Levinson's zeros are simple
- checked against: https://arxiv.org/pdf/1802.10521
- technique: Mollified second moments of ζ near the line; exponential sums (incomplete Kloosterman) to extend mollifier length
- bottleneck: κ(θ) as a function of mollifier length saturates: each length increment costs a new exponential-sum theorem; 46 years moved κ from 0.333 to 0.4173
- tunable: θ per mollifier piece; crossing terms between mollifier pieces (BCY 'technical nightmare' remark on three-piece crossing)
- gap: θ = 17/33 has never been exploited inside the full PRZZ machinery (their pieces use 4/7 and 6/11); whether θ = 17/33 for the Feng piece moves the fourth decimal is, to our knowledge, uncomputed

### Montgomery 2/3 and Montgomery–Taylor 0.6725 for simple zeros (RH-conditional, now subsumed)
- statement: Assuming RH: at least 2/3 of zeros are simple (Montgomery 1973, Fejér kernel, from Σ_ρ m²_ρ ≤ (4/3 + o(1))N(T) and m² ≥ 2m − 1); improved to ≥ 0.6725007… by Montgomery–Taylor 1975 with the kernel whose Fourier transform is cos(√2·) on [−1/2,1/2], the optimizer of K(0)/(K̂(0) + ∫|α|K̂(α)dα) over K = |v̂|², optimal by Chirre–Carneiro-type one-delta extremal analysis (CCLM17 Cor. 14). The 2026 paper reaches the identical constant unconditionally, so the RH hypothesis is now redundant at this constant
- constant: 2/3 (1973); 0.67250070367941164573 (1975)
- status: RH-conditional | H. L. Montgomery; H. L. Montgomery and (P.) Taylor (1975)
- citation: Montgomery, 'The pair correlation of zeros of the zeta function', Proc. Sympos. Pure Math. 24 (1973); Montgomery 1975 [Mon75] as cited in the 2026 paper §7.1
- checked against: https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf (history §1.2 and §7.1; primary Mon75 not fetched)
- technique: Pair correlation with band-limited test functions, F(α) evaluation on [−1,1], integrality of multiplicities
- bottleneck: Support of F(α) restricted to [−1,1]; the constant 3/2 − (1/√2)cot(1/√2) is extremal for the one-delta problem with this data
- tunable: pair-correlation test function/kernel K with supp K̂ ⊆ [−1,1]
- gap: Under RH the record moved past it (0.6727 CG93, 19/27 BHB13, 0.6792 CGdL20 using F beyond [−1,1]); unconditionally 0.6725007 is now the frontier and the RH-side surplus (0.6727–0.7037) marks exactly what the unconditional method has not yet absorbed

### Cheer–Goldston gap-census improvement (RH-conditional)
- statement: Assuming RH, the proportion of simple zeros is ≥ 0.6727 (improving Montgomery–Taylor's 0.6725007 by a census of consecutive-gap configurations: zeros counted in blocks by neighbor multiplicity patterns)
- constant: 0.6727 (digits beyond four not confirmed here)
- status: RH-conditional | A. Y. Cheer, D. A. Goldston (1993)
- citation: Cheer & Goldston, 'Simple zeros of the Riemann zeta-function', Proc. Amer. Math. Soc. 118 (1993), as cited in the 2026 paper §1.2 [CG93]
- checked against: https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf (secondary); primary memory-unverified
- technique: Montgomery pair correlation plus combinatorial floor on multiplicity distribution from gap census
- bottleneck: Same F(α) support [−1,1]; gains from the census are in the fourth decimal
- tunable: census partition of gap configurations; test function per census class
- gap: The lab has already transplanted a Cheer–Goldston-type gap-census floor into the 2026 unconditional framework (0.6725007037 → 0.6725106958; PRIOR ART, not to be re-proposed). The remaining question is whether stronger census invariants (multi-window inertia rather than nearest-neighbor counts) reach further toward 0.68185

### Bui–Heath-Brown 19/27 simple zeros (RH-conditional record by non-SDP methods)
- statement: Assuming RH, at least 19/27 = 0.703703703… of the zeros of ζ are simple; previously obtained under RH + Generalized Lindelöf by Conrey–Ghosh–Gonek 1998, who also proved N_d(T) ≥ (5/6 − o(1))N(T) under RH via m² ≥ 3m − 2 [CGG98 (1.2)]
- constant: 19/27 = 0.703703703703…
- status: RH-conditional | H. M. Bui, D. R. Heath-Brown (2013)
- citation: arXiv:1302.5018, 'On simple zeros of the Riemann zeta-function', Bull. LMS 45 (2013); Conrey–Ghosh–Gonek, Proc. LMS 76 (1998)
- checked against: https://arxiv.org/pdf/1302.5018 (listing seen in search; constants cross-checked against 2026 paper §1.2)
- technique: Mollified first and second moments of ζ and ζ' at the zeros (Cauchy–Schwarz on Σ ζ'(ρ)M(ρ)); removes GLH from CGG98
- bottleneck: Mollifier length θ (they use θ < 9/17? ,  length-limited twisted moments); asymptotic large sieve would push further
- tunable: mollifier coefficients and length; combination weights of ζ, ζ' moments
- gap: 19/27 is the RH-conditional simple-zero record by moment methods; the unconditional 2/3 sits 0.037 below it. Nobody has combined the 2026 inertia framework with a BHB-type mollified moment (the two use disjoint arithmetic inputs: twisted moments vs pair correlation)

### Chirre–Gonçalves–de Laat SDP bounds (RH-conditional records via F(α) outside [−1,1])
- statement: Assuming RH, via semidefinite programming over pair-correlation test functions exploiting positivity of Montgomery's F(α) outside [−1,1]: proportion of simple zeros ≥ 0.6792 (as quoted in the 2026 paper; the SDP framework also gives distinct zeros ≥ 0.8477, and for ξ': ≥ 0.8825 simple, ≥ 0.9412 distinct), plus small-gap and multiplicity-sum bounds
- constant: 0.6792 (simple, RH); 0.8477 (distinct, RH); 0.8825/0.9412 (ξ', RH)
- status: RH-conditional | Andrés Chirre, Felipe Gonçalves, David de Laat (2020)
- citation: arXiv:1810.08843, 'Pair correlation estimates for the zeros of the zeta function via semidefinite programming', Adv. Math. 361 (2020)
- checked against: https://arxiv.org/abs/1810.08843 (abstract); constants via 2026 paper §1.2, §7.5(g), Remark 7.3
- technique: Numerically-assisted extremal test functions: SDP over sums of squares times Gaussians; uses F(α) ≥ 0 for all α (available under RH), i.e. data beyond band-width one
- bottleneck: Off-[−1,1] information exists only under RH (F ≥ 0), so nothing transfers unconditionally; SDP certificates are numerical-to-rigorous via rounding
- tunable: SDP over test-function cone; choice of constraint moments
- gap: The 2026 paper's Remark 1.1 explicitly scopes its 0.68185 ceiling to on-[−1,1] data 'so such majorants operate in a different regime': an SDP hunt for the best CONFIGURATION-BY-CONFIGURATION bandwidth-one certificate (the unconditional regime) has not been run ,  the CGdL machinery pointed at the unconditional inertia framework is unmined

### Unconditional Montgomery theorem for F(α) over all complex zeros
- statement: Montgomery's form-factor asymptotic F(α) holds unconditionally when the sum runs over all complex zeros (weighted appropriately): the pair-correlation second moment / Fejér-kernel sum over zero differences equals (4/3 + o(1))(T/2π)log T for band-width 1; and if all zeros with T^{3/8} < γ ≤ T satisfy |β − 1/2| < 1/(2 log T)·(box condition variant), at least 61.7% of zeros are simple
- constant: 4/3 (second-moment constant); 0.617 (simple zeros under box variant)
- status: unconditional | Siegfred Alan C. Baluyot, Daniel Alan Goldston, Ade Irma Suriajaya, Caroline L. Turnage-Butterbaugh (2024)
- citation: arXiv:2306.04799, 'An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function', Acta Arith. 214 (2024); see also Aryan (2022)
- checked against: https://arxiv.org/abs/2306.04799
- technique: Montgomery–Vaughan mean value for the prime side without RH; explicit-formula bookkeeping for complex (off-line) zeros
- bottleneck: Without RH the zero side cannot be read termwise as a positive sum over real ordinates: the diagonal γ = γ' cannot be isolated by sign ,  precisely the obstacle the 2026 paper's inertia reading removed
- tunable: smoothing weight W; height cutoffs; band-width
- gap: This is the arithmetic engine of the whole 2026 development; its error terms (T^{3/8} threshold, weight W(ρ−ρ')) have slack that has not been re-optimized since the inertia application appeared

### Narrow-box theorem: 2/3 simple + 2/3 critical under a shrinking-box hypothesis
- statement: If all zeros ρ = β + iγ with T < γ ≤ 2T lie in the box |β − 1/2| ≤ b/log T with b = b(T) → 0, then at least 2/3 of the zeros are simple, at least 2/3 lie on the critical line (and in the companion paper, at least 2/3 are asymptotically simultaneously simple and on the line)
- constant: 2/3
- status: density-conditional | Baluyot, Goldston, Suriajaya, Turnage-Butterbaugh; Goldston & Suriajaya (2025)
- citation: arXiv:2501.14545 (submitted 2025-01-24, rev. 2025-11-21), 'Pair correlation of zeros of the Riemann zeta function I'; arXiv:2603.28104 (2026-03-30), 'Zeta zeros in a narrow vertical box'; expository companion arXiv:2511.20059 'Zeta zeros on the critical line' (rev. 2026-02-05)
- checked against: https://arxiv.org/abs/2501.14545; https://arxiv.org/abs/2603.28104; https://arxiv.org/abs/2511.20059
- technique: Pair correlation with a general estimate for a double sum over zeros replacing RH; box hypothesis restores termwise positivity
- bottleneck: The box hypothesis is a strong zero-density statement nobody can prove (known density theorems give boxes of width ≫ 1/log T only for almost all zeros, Selberg); superseded logically by the 2026 unconditional result, which needs no box
- tunable: box width b; weight in the double zero-sum
- gap: The intermediate regime ,  fixed b (not → 0) ,  yields constants interpolating below 2/3; a quantitative b ↦ proportion curve is computed nowhere, and the 2026 inertia method should reproduce and beat it; also the series promises 'II' papers (distinct zeros) still to appear

### Pair Correlation Conjecture implies 100% simple and 100% on the line (no RH assumed)
- statement: Assuming only Montgomery's Pair Correlation Conjecture (in the form of the asymptotic for the pair-correlation sum, without RH), asymptotically 100% of the zeros of ζ are simple and 100% lie on the critical line; introduces 'horizontal multiplicity' to convert vertical PCC information into horizontal position information. Companion paper II analyzes the Alternative Hypothesis as the extremal obstruction
- constant: 1 (i.e. 100%)
- status: pair-correlation-conditional | Daniel A. Goldston, Junghun Lee, Jordan Schettler, Ade Irma Suriajaya (2025)
- citation: arXiv:2503.15449 (rev. 2026-03-30), 'Pair correlation conjecture for the zeros of the Riemann zeta-function I: simple and critical zeros'; II: arXiv:2507.06823 (Alternative Hypothesis); cf. arXiv:2508.10857
- checked against: https://arxiv.org/abs/2503.15449
- technique: Gallagher–Mueller 1978 method with RH removed; PCC with unbounded support replaces the band-width-1 restriction
- bottleneck: Full-support PCC is far beyond reach (equivalent to strong Hardy–Littlewood prime-pair information); the unconditional world has support ≤ 1 only
- tunable: support of PCC assumed; test function against the assumed asymptotic
- gap: Quantitative interpolation: PCC on support [−1−δ, 1+δ] for small δ should give 2/3 + c(δ); the function c(δ) is not computed in the literature (the 2026 paper's §7.5 moment ladder HL*(k,λ) is a different parametrization of the same gap: HL*(4) alone gives 13/18)

### Short mollifiers: positive proportion at any mollifier length via variational derivative combinations
- statement: By calculus of variations, there is a sequence of linear combinations of derivatives of ζ adapted to Levinson's method that yields a positive proportion of zeros on the critical line regardless of how short the mollifier is; with Levinson's original mollifier the method more than doubles the critical-line proportions for modular (GL(2)) L-functions previously obtained by Bernard and by Kühn–Robles–Zeindler, with identical arithmetic inputs. Optimizing the linear combination has a more pronounced effect than refining the mollifier when the mollifier is short
- status: unconditional | J. Brian Conrey, David W. Farmer, Chung-Hang Kwan, Yongxiao Lin, Caroline L. Turnage-Butterbaugh (2025)
- citation: arXiv:2508.11108 (2025-08-14), 'Short mollifiers of the Riemann zeta-function'
- checked against: https://arxiv.org/abs/2508.11108
- technique: Levinson's method; Euler–Lagrange optimization of the vector of derivative-combination coefficients (a functional-analytic upgrade of Feng's finite λ_k combination)
- bottleneck: At short mollifier lengths the proportion is small; the open question is whether the variational family adds anything at the full θ = 4/7 length where PRZZ optimized a finite-dimensional truncation
- tunable: the linear-combination functional (continuum of λ's); mollifier length and coefficients
- gap: The variational optimum has not been run jointly with the PRZZ two-piece mollifier at θ_C = 4/7, θ_F = 6/11; for GL(2) the doubled proportions are still single-digit percentages, far from the GL(1) 41.7% ,  the degree-2 length barrier (θ ~ 1/2 needed for nonvacuous Levinson, cf. the 2026 paper's Λ* > 1/2 degree obstruction) is the wall

### Zeros of ξ': the complete current scoreboard
- statement: For zeros of ξ'(s): (i) Conrey 1983 (unconditional, Levinson-type): ≥ 79.874% simple and on the critical line, with the proportion for ξ^(m) → 1 as m → ∞; (ii) Wu 2015 (unconditional): ≥ 0.86957 on the critical line (no simplicity); (iii) Farmer–Gonek–Lee 2014 (RH): > 85.84% simple via Montgomery's method with the ξ' pair-correlation form factor; (iv) CGdL 2020 (RH, SDP): 0.8825 simple, 0.9412 distinct; (v) Claude 2026 (unconditional, inertia method): simple-and-on-line ≥ 0.85838 (flat window) and ≥ 0.86864 with the quartic window v(s) = 1 − (7/100)(2s)² − (51/200)(2s)⁴, distinct ≥ 0.92919 resp. 0.93432 ,  i.e. FGL's RH constant with RH removed, still below Wu's on-line-only 0.86957
- constant: 0.85838 / 0.86864 (uncond. simple-on-line); 0.92919 / 0.93432 (uncond. distinct); 0.86957 (uncond. on-line, Wu); 0.8825 (RH simple)
- status: unconditional | J. B. Conrey; X. Wu; D. Farmer, S. Gonek, Y. Lee; Chirre–Gonçalves–de Laat; Claude (2026)
- citation: Conrey, 'Zeros of derivatives of Riemann's xi-function on the critical line', J. Number Theory 16 (1983); Farmer–Gonek–Lee [FGL14]; Wu [Wu15]; 2026 Anthropic preprint Remark 7.3 (formalized as Zeta23.XiPrime.xiDeriv_simple_on_line and quartic_stdform)
- checked against: https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf (Remark 7.3); https://github.com/anthropics/zeta-23-lean
- technique: For (v): same inertia compression, with the ξ' zero-density/prime-side constants replacing ζ's; window optimization only attempted over a two-parameter quartic family
- bottleneck: The quartic window is an ad hoc truncation: the exact Euler–Lagrange maximizer for the ξ' functional (analogue of v'' + 2λ²v = 0) was not solved; RH-conditional 0.8825 marks what remains unabsorbed
- tunable: window polynomial coefficients (currently only 2 free parameters used); order m of derivative
- gap: OPEN, fine-grained: solve the ξ' variational problem exactly; any value > 0.86957 would make the unconditional simple-on-line constant exceed the best known on-line-only constant, a qualitatively new statement. Also ξ^(m), m ≥ 2, is untouched by the inertia method (needs the ξ^(m) prime-side second moment, known under RH from FGL-type work)

### Dirichlet L-functions: critical-zero proportions, fixed q and hybrid
- statement: For a fixed primitive χ mod q (Theorem E of the 2026 paper, unconditional): ≥ (2/3 − o(1))N_χ(T,2T) zeros on the critical line, same for simple-on-line, ≥ (5/6 − o(1)) distinct, all improvable to 0.6725007/0.6725007/0.83625 via the Montgomery–Taylor window. Previous Levinson-method records for individual L(s,χ) (log q = o(log T)): about 41.7% on line, 40.7% simple (Wu 2019). Hybrid range: the 2026 paper's Remark 7.2(i) HEURISTICALLY extends to q ≤ T^ϑ with proportion H(1/(1+ϑ)) > 0 for ϑ < √6/3 = 0.81649…, explicitly flagged 'we have not checked the uniformity of every error term and do not claim this'. Degree obstruction: for an individual GL(2) L-function the method gives c = 6/13 < 1/2, i.e. nothing
- constant: 0.67250070…, 0.83625035… (fixed q); ~0.417/0.407 (Wu 2019, log q = o(log T)); threshold ϑ < √6/3 ≈ 0.8164965809
- status: unconditional | Claude (2026); X. Wu (2019); q-aspect family analogues: Conrey–Iwaniec–Soundararajan school (2026)
- citation: 2026 Anthropic preprint, Theorem E and Remark 7.2 (Lean: Zeta23.ThmE.thmE_A₀ etc.); Wu [Wu19]
- checked against: https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf
- technique: Same inertia compression with ν_{X,χ} prime side; unimodular χ(n) factors leave the diagonal unchanged
- bottleneck: Fixed q only, as proved; hybrid uniformity unverified; family-average q → ∞ version needs a Gevrey-class taper in the tail proposition (Prop 4.2 analogue) and 'is not carried out'
- tunable: taper class (Gevrey); band-width Λ < 1/(1+ϑ); family averaging weights
- gap: Two concrete unclaimed theorems sitting in remarks: (a) rigorous hybrid q ≤ T^ϑ version; (b) family-averaged 2/3-on-line for all χ mod q with T as small as a power of log q, which would smash all q-aspect Levinson records

### The conditional moment ladder inside band-width one (HL*)
- statement: §7.5(f) of the 2026 paper: let HL*(k₀,λ) be the hypothesis that tr G̃^k = d·ℓ₁^k(m_k(λ) + o(1)) for k ≤ k₀, where m_k(λ) are moments of the limiting spectral distribution of the sine-kernel Gram matrix (a theorem for kλ < 2, Rudnick–Sarnak range; for k = 4, λ > 1/2 it encodes a Hardy–Littlewood-type asymptotic for Σ_m (Λ⋆Λ)(m)(Λ⋆Λ)(m+h), |h| ≤ X²/T). Then m_k(1) = 1, 4/3, 2, 13/4 for k ≤ 4; HL*(4,λ) for all λ < 1 gives liminf N^s₀/N ≥ 13/18 = 0.72222…, and HL*(k₀,λ) for all k₀, λ gives proportion 1. Unconditionally, higher moments add nothing on λ ∈ (1/2,1) (k = 3 only for λ < 2/3, and odd moments do not lower the Christoffel function Λ₁(0))
- constant: m_k(1) = 1, 4/3, 2, 13/4; Λ₂(0;1) = 5/36; conditional proportion 13/18 = 0.7222…
- status: conjecture | Claude (Anthropic) (2026)
- citation: 2026 Anthropic preprint §7.5(d)-(f); Rudnick–Sarnak (1996) for kλ < 2; Hejhal (1994) triple correlation
- checked against: https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf
- technique: Chebyshev–Markov–Stieltjes one-sided bound: with normalized moments up to 2m, sharp lower bound for n₊/d is 1 − Λ_m(0), Λ_m the Christoffel function at 0
- bottleneck: tr G̃⁴ for λ near 1 requires additive correlations of Λ⋆Λ ,  Hardy–Littlewood territory, unproved; this is THE quantitative wall between 2/3 and 1
- tunable: number of moments; λ; window in the moment functionals
- gap: Nobody has numerically measured tr G̃⁴/(dℓ₁⁴) against the sine-kernel prediction 13/4 at accessible heights ,  a direct falsification target for the smoothing/o(1) structure, well inside this lab's machinery


## Territory B: zero-density estimates and zero-free regions ,  Guth-Maynard 2024 and aftermath, density-hypothesis exponents, explicit zero-free regions (Mossinghoff-Trudgian-Yang, Bellotti), Korobov-Vinogradov, large values of Dirichlet polynomials, explicit zero-density inputs to explicit prime-counting bounds (state of the art as of August 2026)

### Guth-Maynard zero-density theorem
- statement: N(sigma,T) <= T^{30(1-sigma)/13 + o(1)} uniformly for 1/2 <= sigma <= 1; equivalently A(sigma) <= 30/13 = 2.3076923..., the first improvement at the key point sigma near 3/4 over Ingham/Huxley in 80+ years (Huxley's 12/5 = 2.4). The sharper sigma-dependent form recorded in the ANTEDB is A(sigma) <= 15/(3+5sigma) for 7/10 <= sigma < 19/25, which equals 30/13 exactly at sigma = 7/10. Consequences: asymptotic PNT in intervals [x, x+x^{17/30+eps}] (17/30 = 0.5666..., replacing Huxley's 7/12), and primes in almost all short intervals of length x^{2/15+eps} (2/15 from 1 - 2*(13/30); this last consequence from memory of the paper, not re-verified in the abstract).
- constant: A(sigma) <= 30/13 = 2.307692...; A(sigma) <= 15/(3+5sigma) on [7/10, 19/25); primes-in-intervals exponent 17/30 = 0.56666...
- status: unconditional | Larry Guth, James Maynard (2024)
- citation: arXiv:2405.20552; Annals of Mathematics (2) 203 (2026), no. 2, 623-675
- checked against: https://arxiv.org/abs/2405.20552 and https://teorth.github.io/expdb/blueprint/zero-density-chapter.html
- technique: New large-value estimates for Dirichlet polynomials at values V near N^{3/4}: dichotomy on the additive energy of the set of large-value points, matrix/operator-norm arguments replacing the classical mean-value + Halasz-Montgomery pair
- bottleneck: The large-values problem at V ~ N^{3/4}: their energy bound is not believed tight; every step carries T^{o(1)} losses (dyadic decompositions, divisor bounds), so the result is intrinsically non-explicit as stated
- tunable: Choice of raise-to-power k in Dirichlet polynomial, additive-energy threshold, dyadic decomposition parameters, the LV(sigma,tau) exponent tuples fed into the zero-density LP
- gap: No explicit (finite-T, all-constants) version exists (searched Aug 2026: nothing); gap between 30/13 and the density hypothesis value 2 at sigma = 3/4; Tao-Trudgian-Yang already extracted more from the same LV inventory in some sigma ranges, suggesting further LP slack

### Current best piecewise zero-density exponent table A(sigma) (ANTEDB, mid-2026)
- statement: N(sigma,T) << T^{A(sigma)(1-sigma)+o(1)} with the current record piecewise: A(sigma) <= 3/(2-sigma) for 1/2 <= sigma <= 7/10 (Ingham 1940); 15/(3+5sigma) for 7/10 <= sigma < 19/25 (Guth-Maynard 2024); 9/(8sigma-2) for 19/25 <= sigma < 127/167, 15/(13sigma-3) for 127/167 <= sigma < 13/17, 6/(5sigma-1) for 13/17 <= sigma < 17/22 (Ivic 1980-84); 2/(9sigma-6) for 17/22 <= sigma < 41/53 (Bourgain-improved); 9/(7sigma-1) for 41/53 <= sigma < 7/9 (Ivic); 9/(8(2sigma-1)) for 7/9 <= sigma < 1867/2347 (Bourgain-improved); 3/(2sigma) for 1867/2347 <= sigma < 4/5 (Bourgain 2000); 3/(10sigma-7) for 7/8 <= sigma < 279/314 and 9/10 < sigma <= 31/34 (Heath-Brown 1979); 24/(30sigma-11) for 279/314 <= sigma <= 9/10 (Chen-Debruyne-Vindas 2024); Bourgain-optimized pieces for 31/34 < sigma < 1. Density hypothesis A(sigma) <= 2 known exactly for sigma >= 25/32 = 0.78125 (from 9/(8(2sigma-1)) <= 2), unchanged by Guth-Maynard.
- status: unconditional | Ingham, Ivic, Heath-Brown, Bourgain, Chen-Debruyne-Vindas, Guth-Maynard; table curated by Tao-Trudgian-Yang (ANTEDB) (2026)
- citation: ANTEDB blueprint, Chapter 11 (teorth.github.io/expdb); arXiv:2501.16779
- checked against: https://teorth.github.io/expdb/blueprint/zero-density-chapter.html
- technique: LP combination of large-value estimates (mean values, Halasz-Montgomery, exponent pairs, additive energy) into zero-density exponents; machine-assisted optimization
- bottleneck: Each piece is the LP optimum over the currently-catalogued LV inventory; improving a piece requires either a new LV estimate or finding slack the LP search missed
- tunable: The full catalogue of LV(sigma,tau) and zeta-moment exponents; exponent pair choices; the LP itself
- gap: The many awkward crossover points (19/25, 127/167, 13/17, 17/22, 41/53, 1867/2347, 279/314) mark exactly where two methods tie, i.e. where a small new input moves the record; the density-hypothesis threshold 25/32 has not moved since 2000

### Tao-Trudgian-Yang systematic exponent-pair / zero-density / additive-energy improvements
- statement: Four new exponent pairs: (89/1282, 997/1282), (652397/9713986, 7599781/9713986), (10769/351096, 609317/702192), (89/3478, 15327/17390); several new zero-density estimates A(sigma) in ranges left open between Guth-Maynard and Ivic/Bourgain pieces (Table 2 of the paper; e.g. an improved Heath-Brown-type zero-density theorem using the exponent pair (3/40, 31/40)); new additive-energy estimates A*(sigma) for zeta zeros. Obtained by combining and optimizing existing methods, explicitly not by new analytic technique.
- status: unconditional | Terence Tao, Tim Trudgian, Andrew Yang (2025)
- citation: arXiv:2501.16779
- checked against: https://arxiv.org/abs/2501.16779 and https://arxiv.org/html/2501.16779v1
- technique: Machine-assisted systematic optimization over the ANTEDB inventory: exponent pairs, large values, moment bounds, energy estimates, combined by LP
- bottleneck: The optimization is over known inputs; further gains need either new LV/energy inputs or a finer search (their own framing invites this)
- tunable: Exponent pair selection, LP weightings, sigma-range decompositions, energy vs cardinality tradeoffs
- gap: The authors state more can be extracted; the combination space (which LV theorems, which exponent pairs, which sigma subintervals) is far from exhausted, and the q-aspect analogue of this systematic pass has not been done

### q-aspect zero-density exponent 7/3 for Dirichlet L-functions (Guth-Maynard transplant)
- statement: Zero-density estimate for Dirichlet L-functions with exponent 7/3 = 2.333... replacing Huxley's 12/5 = 2.4: summed zero counts N(sigma,T,chi) bounded by (qT)^{7(1-sigma)/3+eps} in the stated aspect (per the abstract; exact aggregation over chi mod q as stated in the paper). Applications: least Goldbach numbers in APs modulo primes, primes in short intervals for prime-power moduli.
- status: unconditional | Bin Chen, Vishal Gupta, Yung Chi Li (2025)
- citation: arXiv:2507.08296 (submitted 2025-07-11, revised 2026-07-27)
- checked against: https://arxiv.org/abs/2507.08296
- technique: Guth-Maynard large-value method adapted to character sums: sharp bounds for sums over affine transformations with GCD-twist functions
- bottleneck: The GM energy method transfers with loss: 7/3 > 30/13, so the q-aspect lags the t-aspect record; the affine/GCD-twist estimates are the limiting input
- tunable: GCD-twist sum estimates, energy thresholds, choice of character-sum large sieve inputs
- gap: Closing 7/3 down to 30/13 in the q-aspect; nobody has yet run a TTY-style systematic LP pass over the q-aspect LV inventory (paper is 13 months old, one revision)

### Best explicit classical zero-free region (Mossinghoff-Trudgian-Yang)
- statement: zeta(sigma+it) != 0 for sigma >= 1 - 1/(5.558691 log|t|), |t| >= 2. Same paper also proves the explicit Korobov-Vinogradov-type region sigma >= 1 - 1/(55.241 (log|t|)^{2/3} (loglog|t|)^{1/3}) for |t| >= 3, and records that the combination improves the largest known zero-free region for 3*10^12 <= |t| <= exp(64.1) and |t| >= exp(1000).
- constant: R = 5.558691 (classical); 55.241 (KV-type, same paper)
- status: unconditional | Michael J. Mossinghoff, Timothy S. Trudgian, Andrew Yang (2022)
- citation: arXiv:2212.06867; Research in Number Theory 9 (2023), art. 55
- checked against: https://arxiv.org/abs/2212.06867
- technique: Landau-method with an optimized nonnegative trigonometric polynomial (degree 16), explicit bounds on zeta and zeta'/zeta, plus Ford-style Vinogradov-Korobov machinery for the (log)^{2/3} region
- bottleneck: Classical region: the trigonometric-polynomial method is near its intrinsic limit (the optimal-polynomial constant is essentially saturated); KV region: explicit Vinogradov-mean-value constants dominate
- tunable: Nonnegative cosine polynomial coefficients (degree, class), smoothing kernels in the explicit zeta'/zeta bounds, crossover height engineering
- gap: 5.558691 has stood since Dec 2022 with no successor found (searched Aug 2026); remaining slack is in the polynomial class (Arestov-type enlargements, cf. Nielsen 2022) and in the explicit zeta bounds fed in; mid-range exp(64.1) < |t| < exp(1000) is owned by the classical region and is where hybrid improvements would land

### Best explicit Korobov-Vinogradov zero-free region (Bellotti)
- statement: zeta(sigma+it) != 0 for sigma >= 1 - 1/(54.004 (log|t|)^{2/3} (loglog|t|)^{1/3}), all |t| >= 3, improving asymptotically to constant 48.0718 for large |t| (arXiv v1 abstract; the published JMAA version is cited by Johnston 2024 with constant 53.989, becoming the largest known zero-free region for |t| > e^{481958}). Underlying explicit growth bound: |zeta(sigma+it)| <= 70.7 |t|^{4.438(1-sigma)^{3/2}} (log|t|)^{2/3} for 1/2 <= sigma <= 1, |t| >= 3, improving Ford's 76.2 |t|^{4.45(1-sigma)^{3/2}}.
- constant: 54.004 (all |t|>=3), 48.0718 (asymptotic), zeta-bound pair (70.7, 4.438)
- status: unconditional | Chiara Bellotti (2024)
- citation: arXiv:2306.10680; J. Math. Anal. Appl. 541 (2025)/S0022247X24001719 (constant 53.989 vs 54.004 across versions: both seen in sources, flagged)
- checked against: https://arxiv.org/abs/2306.10680 (cross-checked against https://arxiv.org/html/2411.13791)
- technique: Explicit Vinogradov integral / exponential-sum bounds sharpening Ford's pipeline, then Landau method with the improved zeta growth bound
- bottleneck: Explicit Vinogradov mean value theorem constants: the sharp (Bourgain-Demeter-Guth) decoupling VMT has no usable explicit version, so explicit KV constants (48-54) sit far above what the asymptotic method should give
- tunable: Explicit VMT parameters, the exponent constant 4.438, trigonometric polynomial, choice of mollifying kernel in the Landau argument
- gap: Any explicit-decoupling progress collapses 4.438 and hence the 48-54 range; also the |t| >= 3 uniform constant (54.004) vs asymptotic (48.0718) gap is pure optimization of crossover regimes

### Explicit Ingham-type zero-density estimates (Kadiri-Lumley-Ng; Chourasiya explicit Carlson)
- statement: Kadiri-Lumley-Ng give a fully explicit version of Ingham's N(sigma,T) = O(T^{8(1-sigma)/3} (log T)^5): N(sigma,T) <= C1(sigma) T^{8(1-sigma)/3} (log T)^{5-2sigma} + C2(sigma) log^2 T for sigma in a high range (exact C1, C2 tabulated in the paper, not in the abstract). Chourasiya (2024) gives the explicit Carlson-type bound N(sigma,T) <= 0.78 T^{4sigma(1-sigma)} (log T)^{5-2sigma} for T >= 3 (ANTEDB records the closely-related form 0.7756 T^{4sigma(1-sigma)} log^{5-2sigma} T for sigma >= 3/5).
- status: unconditional | Habiba Kadiri, Allysa Lumley, Nathan Ng; Shashi Chourasiya (2021)
- citation: arXiv:2101.12263 (KLN); arXiv:2412.02068 (Chourasiya, An explicit version of Carlson's theorem)
- checked against: https://arxiv.org/abs/2101.12263 and search results for arXiv:2412.02068
- technique: Explicit mollified second/fourth moments plus explicit Littlewood/Jensen zero-counting lemmas, with numerics for small T
- bottleneck: Explicit moment constants and the log-power bookkeeping; these estimates still lose badly against non-explicit exponents (8/3 vs 12/5 vs 30/13)
- tunable: Mollifier coefficients in the moment estimates, kernel in the zero-detection step, sigma-range decompositions, numerical verification height as input
- gap: No explicit density estimate exists with exponent better than Ingham-type in the central range; the entire Huxley 12/5 and Guth-Maynard 30/13 layer is unexplicit, so every explicit prime-counting application still runs on 1937-40 era exponents with 2021+ constants

### Explicit form of Ingham's zero-density estimate with sharpened log power (Chourasiya-Simonic)
- statement: Explicit version of Ingham's 1940 bound N(sigma,T) << T^{3(1-sigma)/(2-sigma)} log^5 T, with the log exponent reduced to (7-5sigma)/(2-sigma) (so log^{(7-5sigma)/(2-sigma)} T), together with an explicit fourth-power-moment estimate for zeta on the critical line as the engine. Also ANTEDB Theorem 11.39 records the companion explicit bound N(sigma,T) <= 8.604 T^{3(1-sigma)/(2-sigma)} log^3 T + 9.461 log^2 T + 167.8 log T for T >= 3, 1/2 <= sigma <= 5/8 (small-model transcription of the ANTEDB page; exact constants should be re-read from source before use).
- status: unconditional | Shashi Chourasiya, Aleksander Simonic (2025)
- citation: arXiv:2507.15184 (submitted 2025-07-21, revised 2025-09-30)
- checked against: https://arxiv.org/abs/2507.15184 and https://teorth.github.io/expdb/blueprint/zero-density-chapter.html
- technique: Explicit fourth moment of zeta plus Ingham's convexity argument, with explicit constant tracking through the zero-detector
- bottleneck: The explicit fourth-moment constant (leading asymptotic 1/(2 pi^2) T log^4 T) carries slack in its explicit error terms; that slack propagates linearly into the density constant
- tunable: Fourth-moment smoothing weights, split points between moment ranges, log-power vs constant tradeoffs
- gap: Fresh paper (13 months old): its fourth-moment input has known slack, and nobody has yet fed this new explicit Ingham into the ψ(x)/prime-gap pipelines that currently cite KLN 2021

### Bellotti explicit log-free and near-unity zero-density estimates
- statement: Log-free: N(sigma,T) <= A T^{B(1-sigma)} explicitly, the sharpest known explicit zero-density estimate uniformly for sigma in [alpha_0, 1] with 0.985 <= alpha_0 <= 0.9927 and 3*10^12 < T <= exp(6.7*10^12) (A, B tabulated in the paper). Near-unity: first explicit estimate of the form N(sigma,T) <= C T^{B(1-sigma)^{3/2}} (log T)^{C'} with log-power C' improved to 10393/900 = 11.5477...
- status: unconditional | Chiara Bellotti (2024)
- citation: arXiv:2405.12545 (J. Number Theory, S0022314X24002166); arXiv:2311.05136
- checked against: https://arxiv.org/abs/2405.12545 and https://arxiv.org/abs/2311.05136
- technique: Explicit Halasz-Montgomery/Turan power-sum methods near sigma = 1 with Korobov-Vinogradov zeta bounds
- bottleneck: Same explicit-VMT wall as the KV zero-free region: the (1-sigma)^{3/2} exponent constant B and the huge log powers come from non-sharp explicit exponential sum bounds
- tunable: Power-sum parameters, choice of detector polynomial, crossover heights, explicit zeta-bound inputs
- gap: The T-window (T <= exp(6.7*10^12)) and sigma-window (sigma >= 0.985) are artifacts of crossovers between competing explicit tools; widening either window is an optimization exercise with existing inputs

### Numerical verification of RH to height 3*10^12 (Platt-Trudgian)
- statement: All zeros beta + i*gamma of zeta with 0 < gamma <= 3*10^12 have beta = 1/2, verified rigorously with interval arithmetic (isolation of zeros via Turing's method). This height is a load-bearing input to every explicit zero-free region, explicit zero-density estimate, and explicit PNT bound above.
- status: numerical | David J. Platt, Timothy S. Trudgian (2021)
- citation: arXiv:2004.09765; Bull. London Math. Soc. 53 (2021), 792-797
- checked against: https://arxiv.org/abs/2004.09765
- technique: Rigorous interval-arithmetic evaluation of Z(t) (Riemann-Siegel with enclosure-checked error), Turing-method zero counting
- bottleneck: Pure compute plus enclosure-checked-arithmetic engineering; cost grows slightly worse than linearly in height
- tunable: Verification height H itself; per-zero certification cost; how H enters each downstream constant
- gap: Height has not moved publicly since 2020 despite hardware gains; every explicit constant downstream (5.558691, 54.004, PNT constants) improves mechanically with a higher verified height

### Sharpest explicit PNT error bounds (Fiori-Kadiri-Swidinsky)
- statement: |psi(x) - x| < 9.22022 x (log x)^{3/2} exp(-0.8476836 sqrt(log x)) for all x > 2, and |psi(x) - x| < 4.9678*10^{-15} x for all x >= exp(3000) (improving Platt-Trudgian's 4.51*10^{-13} x). Companion: |pi(x) - Li(x)| <= 9.2211 x sqrt(log x) exp(-0.8476 sqrt(log x)) for x >= 2.
- status: unconditional | Andrew Fiori, Habiba Kadiri, Joshua Swidinsky (2023)
- citation: arXiv:2204.02588 (JMAA 2023); arXiv:2206.12557 (Res. Number Theory 2023)
- checked against: https://arxiv.org/abs/2206.12557 and search results for arXiv:2204.02588
- technique: Explicit formula with optimized weight functions, classical explicit zero-free region + KLN explicit zero-density + verified RH height, leveraging numerics at small x
- bottleneck: Uses the classical (sqrt(log x)) regime; the KV-region-driven exp(-c (log x)^{3/5} (loglog x)^{-1/5}) regime only wins for astronomically large x because explicit KV constants are 48-54
- tunable: Weight/kernel in the explicit formula, zero-density vs zero-free-region tradeoff per x-range, verification height, epsilon-allocation across error terms
- gap: Published before Bellotti 2024 (KV 54.004/48.0718, log-free density), before Chourasiya-Simonic 2025 and Chourasiya 2024 explicit densities: the pipeline has not been re-run with the newest inputs (no successor found in Aug 2026 searches)

### Optimality of the zero-density-to-PNT transfer (Johnston)
- statement: If zeta has no zeros with 1 - beta < 1/(c (log t)^{2/3} (loglog t)^{1/3}) then |psi(x)-x|/x << exp(-omega(x)) (log x)^9 / (loglog x)^3 where omega(x) = min_{t>=3} {eta(t) log x + log t}; this removes the exp(-(1-eps) omega(x)) loss in Pintz's classical transfer and is shown essentially optimal for the assumed region. Improves the machinery by which zero-free regions and zero-density estimates convert to PNT error terms.
- status: unconditional | Daniel R. Johnston (2024)
- citation: arXiv:2411.13791 (submitted 2024-11-21, revised 2025-10-21)
- checked against: https://arxiv.org/abs/2411.13791
- technique: Refined Pintz-style explicit-formula analysis splitting zeros by density estimates near the region boundary
- bottleneck: The polynomial factor (log x)^9 (loglog x)^{-3} is likely not optimal; and the framework's inputs (which explicit region + which explicit density) determine everything downstream
- tunable: eta(t) profile (union of all known explicit regions), the minimizing t(x), power of log in the transfer
- gap: Feeding Bellotti's 48.0718/53.989 and the 2024-25 explicit densities through this now-lossless transfer to get numerically best |psi(x)-x| in the KV regime appears not yet done as a full table

### Primes in [x - x^{0.52}, x] via numerically-optimized Harman sieve (Runbo Li, preprint)
- statement: Nontrivial upper and lower bounds for the number of primes in [x - x^{theta}, x] for 0.52 <= theta <= 0.525, in particular the interval [x - x^{0.52}, x] contains primes for all sufficiently large x, refining Baker-Harman-Pintz 2001 (theta = 0.525). Method is Harman's sieve with machine-computed sieve decompositions and integral estimates (ancillary C++ at theta = 0.520, 0.521, 0.522, 0.523, 0.524, 0.5248, 0.525). Caution: preprint at v8 (Oct 2025), not yet peer-reviewed; treat the 0.52 claim as provisional.
- status: numerical | Runbo Li (2025)
- citation: arXiv:2308.04458 (v8, 2025-10-16)
- checked against: https://arxiv.org/abs/2308.04458
- technique: Harman's sieve with new arithmetic information plus extensive rigorous-numerical evaluation of sieve integrals
- bottleneck: The sieve loss functions: high-dimensional integrals over admissible decompositions, evaluated numerically; correctness rests on the numerical integration being trustworthy
- tunable: Sieve decomposition tree, Buchstab iteration depth, role of exponent-pair inputs, integral quadrature
- gap: The sieve-decomposition search is a discrete/continuous optimization done by hand+code; independent enclosure-checked re-evaluation of the integrals (interval arithmetic) would either confirm or break the 0.52 claim, and further decomposition search could push below 0.52

### State of the cosine-polynomial optimization underlying zero-free regions
- statement: Landau-method regions are governed by nonnegative cosine polynomials sum a_k cos(k theta) >= 0 with a_1 > a_0: Arestov (1992) determined the optimal polynomials for degree <= 6; Tan (2024-25) numerically computed optimal polynomials of degrees 7 and 8 and the resulting zero-free region; Nielsen (2022) showed that enlarging the admissible class by an explicit factor (1 + cos theta) raises the relevant asymptotic leading constant for the Vinogradov-Korobov region from 0.5507 to 0.55127, a strict (small) improvement to the best proven asymptotic zero-free region constant.
- status: numerical | V. V. Arestov; Hong Sheng Tan; Pace P. Nielsen (2024)
- citation: arXiv:2411.01385 (Tan); arXiv:2210.14130 (Nielsen); Arestov 1992
- checked against: https://arxiv.org/abs/2411.01385 and search results for arXiv:2210.14130
- technique: Extremal problems for nonnegative trigonometric polynomials; numerical optimization; class enlargement
- bottleneck: The classical extremal problem has an intrinsic limit (the method cannot push R below a known threshold); remaining gains are in enlarged polynomial classes and in coupling the polynomial choice to the rest of the pipeline rather than optimizing it in isolation
- tunable: Polynomial degree and coefficients, admissible class (extra nonnegative factors), joint optimization with kernel choices in the explicit region proofs
- gap: Tan's degree 7-8 optima are numerical, not enclosure-checked; degrees >= 9 unexplored; Nielsen's enlarged class has not been exhaustively optimized nor integrated into the explicit MTY/Bellotti pipelines


## Territory C: moments of the Riemann zeta function on the critical line ,  asymptotics for 2k=2,4; conditional/unconditional sharp upper and lower bounds; CFKRS-type conjectures for 2k>=6; shifted, twisted and amplified moments; mollified moments feeding Levinson-type critical-line proportions; negative moments; short-interval moments and the FHK maximum

### Second moment with error term (Atkinson / Bourgain-Watt)
- statement: Int_0^T |zeta(1/2+it)|^2 dt = T log(T/(2*pi)) + (2*gamma - 1)T + E(T) with E(T) <<_eps T^(1515/4816 + eps). 1515/4816 = 0.3145764...; previous record was 131/416 = 0.3149038... The conjectured truth is E(T) << T^(1/4+eps), and Omega(T^(1/4)) is known (Good).
- constant: E(T) << T^(1515/4816+eps), 1515/4816 = 0.31457641...
- status: unconditional | J. Bourgain, N. Watt (building on Atkinson 1949) (2017)
- citation: arXiv:1709.04340, 'Mean square of zeta function, circle problem and divisor problem revisited'
- checked against: https://arxiv.org/abs/1709.04340 (via search snippet quoting the exponent and predecessor 131/416)
- technique: Atkinson's formula plus exponential-sum estimates upgraded by decoupling-flavoured bilinear/trilinear bounds shared with the circle and divisor problems
- bottleneck: The exponent is locked to the state of the art for the exponential sums appearing in the Voronoi/Atkinson expansion; further progress needs new exponent pairs or decoupling inputs, not moment-side ideas
- tunable: exponent-pair selection, dyadic decomposition parameters, weight functions in the Atkinson truncation; largely combinatorial search over exponent-pair algebra
- gap: 0.3145 vs conjectured 0.25; the identical machinery controls Dirichlet's divisor problem, so any improvement transfers three ways. No improvement since 2017.

### Fourth moment asymptotic and its error term E_2(T)
- statement: Int_0^T |zeta(1/2+it)|^4 dt = T*P_4(log T) + E_2(T), leading coefficient 1/(2*pi^2) (Ingham 1926); Heath-Brown 1979 gave the full degree-4 polynomial with E_2(T) << T^(7/8+eps); Zavorotnyi and then Ivic-Motohashi via the spectral (Kuznetsov) approach gave E_2(T) << T^(2/3) (log T)^C; Palojarvi-Trudgian (June 2025) improve the powers of log T in the known E_2(T) bounds and deduce small logarithmic improvements for the 2k-th moments with 8 <= 2k <= 12. Omega(T^(1/2)) lower bounds for E_2 are known and the mean square of E_2 is of order T^(3/2).
- constant: E_2(T) << T^(2/3) (log T)^C with C reduced by Palojarvi-Trudgian 2025 (exact C in their Thm 1.1, 12-page paper)
- status: unconditional | A. E. Ingham; D. R. Heath-Brown; Y. Motohashi; A. Ivic; N. Palojarvi, T. Trudgian (2025)
- citation: arXiv:2506.16766, 'On the error term of the fourth moment of the Riemann zeta-function' (Palojarvi-Trudgian); Ingham, Proc. LMS 1926
- checked against: https://arxiv.org/abs/2506.16766 (abstract fetched)
- technique: spectral theory of automorphic forms (Motohashi's explicit formula for the shifted fourth moment) plus large-value estimates; the 2025 paper is explicit constant/log-power chasing through that chain
- bottleneck: T^(2/3) is the spectral barrier: the Kuznetsov-side terms genuinely contribute at that size; only the log powers and implied constants are currently movable
- tunable: truncation points in Motohashi's formula, interpolation exponents between the 4th and 12th moments, large-value parameter choices; all finite-dimensional and explicit
- gap: the log powers C in T^(2/3)(log T)^C are explicitly stated by Palojarvi-Trudgian to be optimizable further; nobody has run a systematic parameter optimization over their lemma chain

### Twelfth moment (Heath-Brown)
- statement: Int_0^T |zeta(1/2+it)|^12 dt << T^2 (log T)^17 (Heath-Brown 1978), equivalent in strength to the Weyl subconvexity bound zeta(1/2+it) << t^(1/6+eps); the exponent 2 has never been improved; Palojarvi-Trudgian 2025 obtain small logarithmic improvements for moments of order between 8 and 12 via their improved E_2(T) bounds.
- constant: T^2 (log T)^17 (log power from Heath-Brown's original paper)
- status: unconditional | D. R. Heath-Brown (1978)
- citation: Heath-Brown, 'The twelfth power moment of the Riemann zeta-function', Q. J. Math. 29 (1978); surveyed in arXiv:2509.20335 (Florea)
- checked against: https://arxiv.org/abs/2509.20335 and semanticscholar entry for Heath-Brown 1978; exact log power 17: memory-unverified
- technique: combining the fourth moment with large-value estimates for Dirichlet polynomials (Halasz-Montgomery) at the critical exponent where the two balance
- bottleneck: improving the T^2 requires either a better fourth-moment error term in short intervals or fundamentally better large-value estimates (connected to Guth-Maynard-style progress); the log^17 is soft
- tunable: the split point between moment and large-value ranges; the choice of large-value inequality; log-power bookkeeping
- gap: log^17 has visible slack per Palojarvi-Trudgian; also nobody has redone Heath-Brown's balance with the Guth-Maynard 2024 large-value theorem to see if any secondary term improves

### RH-conditional sharp upper bounds for all moments (Soundararajan -> Harper)
- statement: Assume RH. For every k >= 0, Int_0^T |zeta(1/2+it)|^(2k) dt <<_k T (log T)^(k^2) (Harper 2013), refining Soundararajan 2009 which had (log T)^(k^2+eps). Tao (2024) optimized the implicit constant in Harper's refinement and computed the implicit constant in Soundararajan's bound under certain conditions.
- constant: T(log T)^(k^2) with inexplicit C(k); Tao 2024 gives the first explicit values
- status: RH-conditional | K. Soundararajan; A. J. Harper; T. Tao (Tingyu Tao, explicit constants) (2013)
- citation: arXiv:1305.4618 (Harper); Soundararajan, Ann. of Math. 170 (2009); arXiv:2407.20023 (Tingyu Tao)
- checked against: https://arxiv.org/abs/2407.20023 (abstract fetched); Harper via search results quoting the theorem
- technique: Soundararajan's upper bound for log|zeta| as a Dirichlet-polynomial average under RH, plus Harper's iterated splitting of [0,T] by the size of partial sums over increasing prime ranges
- bottleneck: removing RH entirely for k>2; and the implicit constant C(k) grows badly in k (double-exponential in Harper's original argument), which blocks explicit conditional applications
- tunable: the sequence of prime-range cut points beta_i in Harper's iteration, the number of iterations, Chebyshev-polynomial approximations to exp on each range: an explicit finite-dimensional optimization
- gap: Tao's optimization exists only for restricted conditions and has not been pushed to explicit enclosure-checked C(k) for the k=3,4 values that feed conditional sixth/eighth-moment applications; no ball-arithmetic-enclosure-checked version exists

### Unconditional sharp upper bounds for 0 <= k <= 2 (Heap-Radziwill-Soundararajan)
- statement: For all real 0 <= k <= 2, Int_0^T |zeta(1/2+it)|^(2k) dt << T (log T)^(k^2), unconditionally. Improves Ramachandra, Heath-Brown (k=1/n and rational cases) and Bettin-Chandee-Radziwill.
- constant: << T(log T)^(k^2), 0<=k<=2
- status: unconditional | W. Heap, M. Radziwill, K. Soundararajan (2019)
- citation: arXiv:1901.08423; Q. J. Math. 70 (2019), 1387-1396
- checked against: https://arxiv.org/abs/1901.08423 and QJM page (search results)
- technique: Radziwill-Soundararajan style comparison: splitting according to whether a short Dirichlet polynomial over primes is well-behaved, using the unconditional fourth moment as the anchor (hence the ceiling k=2)
- bottleneck: k=2 is exactly the last unconditionally-known asymptotic; any unconditional k>2 upper bound of the sharp order would need a sixth-moment-strength input
- tunable: length and shape of the prime polynomial, the truncation level of exp approximations, the exceptional-set decomposition
- gap: the method gives k slightly beyond 2 in weaker forms (weak-type bounds T(log T)^(k^2+eps) for k in (2, 2+delta)?) ,  whether the HRS mechanism plus the twisted fourth moment of BBLR (length T^(1/4)) yields sharp bounds for some k>2 is not written down anywhere

### Unconditional sharp lower bounds for all k > 0 (Radziwill-Soundararajan; Heap-Soundararajan)
- statement: For every real k > 0, Int_0^T |zeta(1/2+it)|^(2k) dt >>_k T (log T)^(k^2), unconditionally: k >= 1 by Radziwill-Soundararajan (2013), 0 < k < 1 by Heap-Soundararajan (2020/2022). Combined with HRS, the order of all moments with 0 <= k <= 2 is known unconditionally.
- constant: >>_k T(log T)^(k^2), all real k>0
- status: unconditional | M. Radziwill, K. Soundararajan; W. Heap, K. Soundararajan (2022)
- citation: arXiv:2007.13154; Mathematika 68 (2022), 1-14
- checked against: https://arxiv.org/abs/2007.13154
- technique: Holder/Cauchy comparison of the moment against mixed moments of zeta times a short Dirichlet polynomial approximating zeta^k, computable by the second (or fourth) moment
- bottleneck: the constant delivered is far from the conjectured Keating-Snaith constant a_k*g_k/(k^2)!; extracting the sharp constant from this route needs longer polynomial approximations than the twisted second moment permits
- tunable: polynomial approximation length theta, coefficient smoothing, Holder exponents
- gap: explicit numeric lower-bound constants at k=3 were only recently pushed to 34.4/42 of conjecture (Durkan-Page 2026, separate entry); for non-integer k>2 no explicit-constant lower bound is on record

### Sixth moment under the ternary additive divisor conjecture (Ng)
- statement: A conjectural asymptotic (with power-saving error) for ternary additive divisor sums sum_{n<=x} d_3(n) d_3(n+h) implies Int_0^T |zeta(1/2+it)|^6 dt ~ 42 * a_3 * T (log T)^9 / 9!, where a_3 is the standard arithmetic factor prod_p [(1-1/p)^4 (1+4/p+1/p^2)]; 42 = g_3 matches Conrey-Ghosh and Keating-Snaith (9! * G(4)^2/G(7) normalization).
- constant: 42 * a_3 / 9! as leading coefficient (Conrey-Ghosh)
- status: conjecture-conditional (ternary additive divisor conjecture) | N. Ng (2021)
- citation: arXiv:1610.04977, 'The sixth moment of the Riemann zeta function and ternary additive divisor sums' (published Discrete Analysis 2021)
- checked against: https://arxiv.org/abs/1610.04977
- technique: moment -> long Dirichlet polynomial mean values (length up to T^2) -> shifted convolutions of d_3 via the delta method heuristic; rigorous reduction to the divisor conjecture
- bottleneck: the ternary additive divisor conjecture itself, i.e. shifted convolution sums of d_3 with power saving uniform in the shift; spectral methods handle d_2 but not d_3 (GL(3) issue)
- tunable: the smoothing weights in the reduction, the delta and h-range in the hypothesis, choice of mollified splitting between diagonal and off-diagonal
- gap: the required uniformity range in the shift h and the size of the needed power saving delta have slack: nobody has computed the minimal delta and h-uniformity that still yields the asymptotic, which is exactly the kind of bookkeeping a numerical/symbolic audit can settle

### Eighth moment under RH + quaternary additive divisor conjecture (Ng-Shen-Wong)
- statement: Assuming RH and a quaternary additive divisor conjecture (shifted convolutions of d_4 with power saving), Int_0^T |zeta(1/2+it)|^8 dt ~ 24024 * a_4 * T (log T)^16 / 16!, where 24024 = g_4 is the Conrey-Gonek / Keating-Snaith constant. A key input is a sharp RH-conditional bound for a certain shifted moment of zeta.
- constant: 24024 * a_4 / 16! leading coefficient
- status: RH-conditional + divisor-conjecture-conditional | N. Ng, Q. Shen, P.-J. Wong (2022)
- citation: arXiv:2204.13891; J. Eur. Math. Soc. (to appear/published, EMS Press 14298487)
- checked against: https://arxiv.org/abs/2204.13891 (via ADS/search snippets)
- technique: long Dirichlet polynomial decomposition, quaternary shifted convolutions for the off-diagonal, and Harper-method shifted-moment upper bounds under RH to control error ranges
- bottleneck: RH is used only through the shifted-moment bound; the additive divisor conjecture for d_4 is the hard unproven core
- tunable: shifted-moment exponents, mollifier lengths in the decomposition, the assumed delta in the divisor conjecture
- gap: Curran's 2024 sharpened correlation/shifted-moment bounds (log-factor savings over Chandee) have not been propagated through this proof; it is unaudited whether they weaken the required divisor-conjecture power saving or shrink the error term

### Unconditional sixth-moment lower bound via two-piece amplified moments (Durkan-Page)
- statement: Unconditionally, M_3(T) = Int_0^T |zeta(1/2+it)|^6 dt >= (34.4 + o(1)) * c_3 * T (log T)^9 where c_3 is the normalized conjectural constant (conjecture predicts 42 in the same normalization; hence 34.4/42 = 81.9% of the conjectured sixth moment is attained). Also asymptotic formulae for two-piece amplified second and fourth moments and effective lower bounds for all joint integer moments consistent with Keating-Snaith / Keating-Wei predictions.
- constant: 34.4 (fraction 34.4/42 = 0.819 of conjecture)
- status: unconditional | B. Durkan, T. Page (2026)
- citation: arXiv:2606.27323, 'Amplified moments of the Riemann zeta function' (June 2026)
- checked against: https://arxiv.org/abs/2606.27323 (abstract fetched)
- technique: twisted/amplified second and fourth moments with two-piece amplifiers (Dirichlet polynomials mimicking zeta^r), lengths limited by BCR (second moment, T^(17/33)) and BBLR (fourth moment, T^(1/4)); constant emerges from a variational optimization over amplifier profiles
- bottleneck: amplifier length ceilings T^(17/33) and T^(1/4); within those ceilings the constant is a pure optimization over coefficient profiles that the authors solved within a restricted family
- tunable: amplifier coefficient profiles (functions on [0,1] discretized), the two piece lengths, the split of exponent r between pieces; a quadratic-form maximization ideal for numerical attack
- gap: 34.4 vs 42: the profile family they optimize over is restricted (two pieces, specific shapes); a wider function class or an optimized piece-length split plausibly moves the constant, and the paper is two months old so this surface is unmined

### Twisted/amplified fourth moment: polynomial length record and fourth-power amplifier
- statement: Asymptotics for Int |zeta(1/2+it)|^4 |A(1/2+it)|^2 dt hold for arbitrary Dirichlet polynomials A of length T^(1/4-eps) (Bettin-Bui-Li-Radziwill 2020, improving Hughes-Young's T^(1/11-eps)). Bui-Hall-Subira Jorge (Nov 2025) establish the fourth moment times the FOURTH power of an amplifier mimicking zeta(s)^r, with applications to gaps between zeros of zeta and to lower bounds for moments.
- constant: length exponents 1/11 -> 1/4 (arbitrary), amplifier^4 (structured, Nov 2025)
- status: unconditional | C. Hughes, M. Young; S. Bettin, H. M. Bui, X. Li, M. Radziwill; H. M. Bui, R. R. Hall, M. Subira Jorge (2025)
- citation: arXiv:2511.14415, 'Amplified Fourth Moment of the Riemann Zeta-Function and Applications'; arXiv:0709.2345 (Hughes-Young)
- checked against: https://arxiv.org/abs/2511.14415 (abstract fetched)
- technique: delta method / divisor correlations for the off-diagonal of the twisted fourth moment; the 2025 paper extends to amplifier^4 by exploiting multiplicative structure of the amplifier coefficients
- bottleneck: length T^(1/4) for arbitrary coefficients: beyond it the binary additive divisor problem must be understood in wider uniformity; structured (amplifier-like) coefficients are the current way around
- tunable: amplifier exponent r, coefficient profile, test functions in the gap functional (Wirtinger quotient), length allocation
- gap: the gaps-between-zeros constants and moment lower bounds extracted in 2511.14415 come from Wirtinger-type quotients over the amplifier coefficients, optimized by hand; a numerical re-optimization of those quotients is unattempted in print

### Twisted second moment / mollifier length and the Levinson pipeline
- statement: The mean square of zeta(1/2+it) times an arbitrary Dirichlet polynomial has an asymptotic for polynomial length up to T^(0.5+0.01515) = T^(17/33-eps) (Bettin-Chandee-Radziwill 2017+). For the specific mollifiers of Levinson's method, length T^(4/7-eps) is admissible (Conrey 1989, via Deshouillers-Iwaniec Kloosterman-sum estimates). Pipeline outputs: kappa >= 0.417293 of zeros on the line and kappa* >= 0.407511 simple (Pratt-Robles-Zaharescu-Zeindler, arXiv:1802.10521, decimals as reported in the paper); August 2026: at least 67.250% (0.6725007037) of zeros simple and on the critical line ('More than two thirds' paper, with Lean 4 formalization; this lab's candidate improvement to 0.6725106958 via a Cheer-Goldston gap-census floor is prior art). Conrey-Farmer-Kwan-Lin-Turnage-Butterbaugh (Aug 2025) construct via calculus of variations new derivative combinations adapted to Levinson's method yielding positive proportion for arbitrarily short mollifiers, and more than double prior proportions for modular L-functions (vs Bernard, Kuhn-Robles-Zeindler) with the same arithmetic input.
- constant: theta = 17/33 (arbitrary), 4/7 (Levinson mollifiers); kappa >= 0.6725007037 (Aug 2026)
- status: unconditional | S. Bettin, V. Chandee, M. Radziwill; J. B. Conrey; K. Pratt, N. Robles, A. Zaharescu, D. Zeindler; Conrey, Farmer, Kwan, Lin, Turnage-Butterbaugh (2026)
- citation: arXiv:1802.10521; arXiv:2508.11108; Anthropic 'More than two thirds of the zeros of the Riemann zeta function lie on the critical line' (Aug 2026, www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf)
- checked against: https://arxiv.org/abs/1802.10521 ; https://arxiv.org/abs/2508.11108 ; https://www.techtimes.com/articles/324173/20260812/claude-raises-riemann-zeta-zeros-672-two-papers-no-one-had-combined.htm
- technique: twisted second moments of zeta and its derivatives by multi-piece mollifiers; autocorrelation-of-ratios for the main terms; Kloosterman/spectral inputs for length beyond 1/2; calculus of variations over the derivative-combination and mollifier coefficients
- bottleneck: mollifier length theta: 4/7 for Levinson-type mollifiers, 17/33 for arbitrary polynomials; each length increase feeds directly into the proportion via Levinson's inequality
- tunable: mollifier coefficient polynomials P_i, piece lengths theta_i, derivative-combination weights (the CFKLT-B variational solution), the R parameter in Levinson's inequality
- gap: the variational derivative-combination lever of 2508.11108 and the two-thirds framework's gap-census lever are independent; whether they compose, and whether the 2508.11108 Euler-Lagrange optimum evaluated at theta=4/7 adds anything on top of the 0.67250 framework, is unexamined in print (distinct from this lab's gap-census transplant)

### Shifted moments: Chandee's conjecture proved under RH; sharpened correlations
- statement: Assume RH. For fixed k_1,...,k_m > 0 and shifts t_j = t + alpha_j with |alpha_j| <= T/2, Int_T^(2T) prod_j |zeta(1/2+i(t+alpha_j))|^(2k_j) dt << T (log T)^(k_1^2+...+k_m^2) * prod_{j<l} min(|alpha_j-alpha_l|, 1/log T)^(-2 k_j k_l)-type factors, i.e. Chandee's 2011 conjectured upper bounds hold in sharp form (Ng-Shen-Wong 2022, Canad. J. Math. 76 (2024) 1556-1586, via Harper's method). Curran (Mathematika 70 (2024), e12268) sharpened correlation upper bounds of shifted values, and unconditional lower bounds of matching order for shifted moments were obtained in arXiv:2405.08725 (2024).
- constant: exponent k_1^2+...+k_m^2 with cross terms 2k_jk_l, exactly Chandee's predicted shape
- status: RH-conditional (upper bounds); unconditional (lower bounds, restricted ranges) | V. Chandee (conjecture); N. Ng, Q. Shen, P.-J. Wong; M. J. Curran (2024)
- citation: arXiv:2206.03350 (Canad. J. Math. 76 (2024) 1556-1586); Curran, Mathematika 70 (2024) e12268; arXiv:2405.08725
- checked against: https://arxiv.org/abs/2206.03350 (abstract fetched; journal ref confirmed)
- technique: Harper's iterated Dirichlet-polynomial splitting adapted to products over shifts; the shift-dependence enters through sums of cos(alpha log p)/p
- bottleneck: unconditional versions beyond the fourth-moment-anchored range; and the exact log-power in the transition regime |alpha| ~ 1/log T
- tunable: same Harper cut-point parameters, now shift-dependent; choice of the min(|alpha|,1/log T) interpolation
- gap: these bounds are the load-bearing input to the NSW eighth moment and to sharp bounds for moments of |zeta| products; Curran's log-savings have not been chained into any downstream application

### Negative moments (Bui-Florea, toward Gonek's conjecture)
- statement: Assume RH. For k < 1/2 and shift alpha with roughly alpha >> 1/log T, Bui-Florea obtain asymptotic formulas for Int_T^(2T) |zeta(1/2+alpha+it)|^(-2k) dt, settling Gonek's conjecture in those ranges; for much smaller shifts, non-trivial upper bounds hold as long as log(1/alpha) << log log T. For k > 1/2 the naive Gonek prediction is expected to fail (Forrester-Keating freezing-transition corrections); no asymptotics are known there.
- constant: asymptotics for k<1/2, alpha >> (log T)^(-1); upper bounds down to log(1/alpha) << log log T
- status: RH-conditional | H. M. Bui, A. Florea (2024)
- citation: arXiv:2302.07226; J. reine angew. Math. (Crelle), doi:10.1515/crelle-2023-0091
- checked against: https://arxiv.org/abs/2302.07226
- technique: Dirichlet-series expansion of 1/zeta against RH-conditional bounds for zeta and its logarithmic derivative; zero-repulsion enters through the shift
- bottleneck: k >= 1/2: individual zeros dominate and the moment is governed by the closest-zero distribution, outside current technology; even the correct conjectural exponent (Gonek vs Forrester-Keating) is contested
- tunable: shift alpha, exponent k, smoothing; on the theory side, the mollifier for 1/zeta
- gap: no published numerical study maps the k-alpha phase diagram at realistic heights; the contested regime k in (1/2, 1], alpha ~ 1/log T is exactly where cheap computation can discriminate the two conjectured exponents

### Short-interval moments and the Fyodorov-Hiary-Keating maximum (Arguin-Bourgade-Radziwill)
- statement: For t sampled uniformly in [T, 2T], max_{|h| <= 1} |zeta(1/2 + i(t+h))| = exp( log log T - (3/4) log log log T + M_T ) where the recentered maximum M_T is tight (bounded in probability), with right-tail decay P(M_T > y) << y e^(-2y): FHK conjecture I (upper bound, arXiv:2007.00988 / Duke 2020-2023) and II (lower bound + tightness, arXiv:2307.00982, 2023). Moments over short intervals (log T)^theta were computed by Arguin-Ouimet-Radziwill-type work (arXiv:1901.04061).
- constant: recentering log log T - (3/4) log log log T; tail y e^(-2y)
- status: unconditional | L.-P. Arguin, P. Bourgade, M. Radziwill (2023)
- citation: arXiv:2307.00982, 'The Fyodorov-Hiary-Keating Conjecture. II'
- checked against: https://arxiv.org/abs/2307.00982 (via ADS/search snippets)
- technique: branching-random-walk multiscale analysis of partial sums of log|zeta| over primes, iterated barrier arguments, twisted moment computations at each scale
- bottleneck: convergence in distribution of M_T (the full FHK prediction: convergence to a randomly shifted Gumbel with the Berestycki-style martingale limit) remains open
- tunable: barrier shapes and scale decompositions (theory); window length, height range, sample count (numerics)
- gap: the subleading constant and the law of M_T are numerically probeable: the lab's Hardy-Z machinery can sample max over [t,t+1] windows at many heights and test the y e^(-2y) tail and the -(3/4) log log log T recentering at finite T, where no published numerics exist at scale

### CFKRS integral-moment conjecture and the divisor-correlation recovery program
- statement: Conjecture (Conrey-Farmer-Keating-Rubinstein-Snaith 2005): Int_0^T |zeta(1/2+it)|^(2k) dt = Int_0^T P_k(log(t/2pi)) dt + O(T^(1/2+eps)), with P_k an explicit degree-k^2 polynomial given by a 2k-fold residue/contour formula; leading coefficient a_k g_k/(k^2)! with g_k = (k^2)! * prod_{j=0}^{k-1} j!/(j+k)! (g_1=1, g_2=2, g_3=42, g_4=24024). Conrey-Keating (papers I-V) rederive the full polynomial from correlations of divisor sums in long Dirichlet polynomials; Baluyot (Mathematika 2024, mtk.12243) organizes the stratification via Vandermonde integrals.
- constant: g_3 = 42, g_4 = 24024; general g_k = (k^2)! prod_{j=0}^{k-1} j!/(j+k)!
- status: conjecture (numerically confirmed for k<=4 at available heights; theorems only for k<=2) | J. B. Conrey, D. Farmer, J. Keating, M. Rubinstein, N. Snaith; Conrey-Keating; S. Baluyot (2005)
- citation: CFKRS, 'Integral moments of L-functions', Proc. London Math. Soc. 91 (2005) 33-104; Baluyot, Mathematika 70 (2024), mtk.12243
- checked against: https://aimath.org/~kaur/publications/43.pdf (Conrey-Gonek high moments, g_3=42, g_4=24024); https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/mtk.12243
- technique: random-matrix analogy (Keating-Snaith CUE moments) plus arithmetic factor via the recipe; divisor-correlation route makes each polynomial coefficient a divisor-sum identity
- bottleneck: the O(T^(1/2+eps)) error term is far beyond reach for k>=3; even the shape of the second-order term is only conjectural
- tunable: none in the conjecture itself; in the numerics: sampling design, unbiased estimators for (log T)^j coefficients, variance control via GUE covariance
- gap: full-polynomial numerical confrontation for k=3,4 at heights >= 10^10 using stored |zeta| samples (not zero-recomputation) is thin in the literature; a systematic coefficient-by-coefficient fit would either support or strain the divisor-conjecture error shapes assumed by Ng and Ng-Shen-Wong


## Territory D: pair correlation and zero statistics ,  Montgomery pair correlation, simple/distinct zero proportions, small and large gaps between zeta zeros, Fourier/SDP extremal test-function optimization (Carneiro-Chandee-Milinovich school, Chirre-Gonçalves-de Laat), de la Bretèche-Fiorilli variance results, GUE statistics, and the August 2026 unconditional pair-correlation framework

### Montgomery's pair correlation theorem and conjecture
- statement: On RH, Montgomery's form factor F(α,T) = N(T)^{-1} Σ_{0<γ,γ'≤T} T^{iα(γ-γ')} w(γ-γ') satisfies F(α,T) = (1+o(1))T^{-2|α|}log T + |α| + o(1) uniformly for |α| ≤ 1; the Pair Correlation Conjecture (PCC) asserts F(α,T) = 1 + o(1) for |α| ≥ 1, equivalently Σ pair correlation density 1 - (sin πu / πu)². Via the Fejér-kernel test function this yields N_s(T) ≥ (2/3 + o(1))N(T) simple zeros on RH.
- constant: 2/3 simple on RH; F determined only on |α| ≤ 1
- status: RH-conditional (theorem for |α|≤1); conjecture for |α|>1 | H. L. Montgomery (1973)
- citation: Montgomery, 'The pair correlation of zeros of the zeta function', Proc. Sympos. Pure Math. 24 (1973), 181-193; restated with proofs in arXiv:2511.20059
- checked against: https://arxiv.org/abs/2511.20059 (Goldston-Suriajaya restatement fetched)
- technique: Explicit formula turning zero sums into Dirichlet polynomial mean values; diagonal evaluation limits support of the Fourier transform of admissible test functions to [-1,1]
- bottleneck: The explicit-formula/mean-value evaluation only controls F on |α| ≤ 1; extending support requires shifted convolution / additive divisor correlations currently out of reach
- tunable: Even test functions g ≥ 0 with supp(ĝ) ⊆ [-1,1]; the extremal problem is a Beurling-Selberg/Fejér-type minimization
- gap: Any unconditional or weaker-hypothesis control of F(α) for |α| slightly beyond 1 would cascade through every constant below

### Simple zeros on RH via moments (current RH-conditional record)
- statement: Assuming RH, at least 19/27 = 0.703703... of the nontrivial zeros of ζ are simple, asymptotically. Conrey-Ghosh-Gonek had proved this under RH + Generalized Lindelöf; Bui-Heath-Brown removed GLH via careful use of the generalized Vaughan identity.
- constant: 19/27 = 0.7037037...
- status: RH-conditional | H. M. Bui, D. R. Heath-Brown (after Conrey-Ghosh-Gonek) (2013)
- citation: arXiv:1302.5018, 'On simple zeros of the Riemann zeta-function'
- checked against: https://arxiv.org/abs/1302.5018 (via search snippet confirming statement and method)
- technique: Asymptotics of Σ ζ'(ρ) M(ρ) against mollified second moment, Cauchy-Schwarz; mollifier of restricted length
- bottleneck: Mollifier length restriction θ; 19/27 is exactly what the attainable θ delivers, and lengthening mollifiers is the same wall as in critical-line proportion work
- tunable: Mollifier coefficients and length θ; choice of Vaughan-identity decomposition
- gap: PRZZ-style long mollifiers (Kloosterman-sum technology) have never been fully injected into the ζ'(ρ)M(ρ) simple-zeros framework; even a small θ gain moves 19/27

### Simple and distinct zeros via pair correlation + semidefinite programming
- statement: Assuming RH: N*(T) ≤ (1.3208+o(1))N(T) for the multiplicity-weighted count (Montgomery-Taylor 1.3275 was previous), hence N_s(T) ≥ (0.6792+o(1))N(T) simple (previous pair-correlation record 0.6727, Cheer-Goldston) and N_d(T) ≥ (0.8477+o(1))N(T) distinct (previous 0.8051, Farmer-Gonek-Lee). Under GRH: 1.3155, 0.6845, 0.8486 respectively; for primitive Dirichlet L-functions in q-aspect, ≥ 0.9350 simple under GRH (previous 0.9322, Sono); for ξ'(s), N_1*(T) ≤ (1.1175+o(1))N_1(T) under RH.
- constant: 0.6792 (simple, RH), 0.8477 (distinct, RH), 1.3208 (N*/N, RH)
- status: RH-conditional (GRH variants as stated) | A. Chirre, F. Gonçalves, D. de Laat (2020)
- citation: arXiv:1810.08843; Advances in Mathematics 361 (2020), 106926
- checked against: https://ar5iv.labs.arxiv.org/html/1810.08843 (theorem-by-theorem constants fetched)
- technique: Replace bandlimited test functions with the Cohn-Elkies sphere-packing function class (Hermite/eigenfunction expansions), optimize via SDP with rigorous rounding
- bottleneck: The SDP is essentially converged for this fixed constraint set: the binding constraint is Montgomery's theorem on |α| ≤ 1 only. New arithmetic inputs (not larger SDPs) are needed
- tunable: Coefficients of Hermite-expansion test functions; SDP dual certificates are explicit and independently checkable
- gap: The SDP machinery has NOT been re-run inside the new unconditional pair-correlation framework (BGST 2025 / August 2026), where the constraint structure differs; that surface is unmined

### Unconditional critical-line and simple-zero proportions (pre-2026 record)
- statement: Unconditionally, the proportion κ of nontrivial zeros on the critical line satisfies κ ≥ 0.41729 (more than five twelfths), and the proportion both on the line and simple is ≥ 0.40758. Previous: Conrey 1989, κ ≥ 0.4088.
- constant: κ ≥ 0.41729; simple-and-critical ≥ 0.40758 (last digits of the simple constant hedged: sources state 'more than 40.7%')
- status: unconditional | K. Pratt, N. Robles, A. Zaharescu, D. Zeindler (2020)
- citation: arXiv:1802.10521; Res. Math. Sci. 7 (2020), article 2
- checked against: https://arxiv.org/abs/1802.10521 (via search snippet confirming constants)
- technique: Levinson's method with long mollifiers built from moments of L-functions and sums of Kloosterman sums
- bottleneck: Mollifier length barrier θ < 0.6 territory; each extension costs major exponential-sum machinery
- tunable: Mollifier coefficient polynomials P_i, length θ, smoothing parameters R
- gap: Superseded in August 2026 by the unconditional pair-correlation route (next entry); the Levinson lineage itself still caps near 0.42

### Unconditional pair correlation and the narrow-box theorem
- statement: Assuming only that all zeros β+iγ with T < γ ≤ 2T lie in a box |β - 1/2| ≤ b/(2 log T) with b → 0 (a hypothesis strictly weaker than RH), pair correlation methods give: at least 2/3 of zeros simple, at least 2/3 on the critical line, and at least 1/3 both simple and on the critical line. Companion papers show that removing RH from Montgomery's simple-zero proof automatically yields 2/3 on the critical line.
- constant: 2/3 simple, 2/3 critical, 1/3 simple-and-critical, under the b/log T box
- status: conditional on the narrow-box hypothesis (weaker than RH) | S. A. C. Baluyot, D. A. Goldston, A. I. Suriajaya, C. L. Turnage-Butterbaugh; companion: Goldston-Suriajaya (2025)
- citation: arXiv:2501.14545 (v2, Nov 2025); companions arXiv:2511.20059, arXiv:2603.28104
- checked against: https://arxiv.org/abs/2501.14545 and https://arxiv.org/abs/2511.20059 (abstracts fetched)
- technique: Unconditional/weak-hypothesis pair correlation: horizontal distribution extracted from a method previously thought purely vertical
- bottleneck: Removing the narrow-box hypothesis entirely; and the 1/3 for the joint count lags the 2/3 for each separately
- tunable: Test functions in the pair correlation window; box width b; weighting w(γ-γ')
- gap: The joint simple-and-critical 1/3 looks like an intersection-bound artifact (2/3 + 2/3 - 1); a direct joint pair-correlation functional could beat it

### More than two thirds of zeros simple and on the critical line, unconditional (August 2026 framework)
- statement: Unconditionally, at least 67.250% (constant 0.6725007037) of the nontrivial zeros of ζ are simple zeros on the critical line (also: distinct zeros on the critical line), removing the narrow-box restriction from the BGST framework. Accompanied by a Lean 4 formalization with main theorem files free of sorrys. The manuscript itself notes the technique averages over zeros and is unlikely to reach 100%.
- constant: 0.6725007037 (this lab's prior art: candidate improvement to 0.6725106958 via a Cheer-Goldston-type gap-census floor; do not re-propose)
- status: unconditional (pending conventional peer review as of Aug 2026) | Claude (Anthropic) (2026)
- citation: Anthropic preprint, https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf; Lean repo github.com/anthropics/zeta-23-lean
- checked against: https://kingy.ai/blog/claude-riemann-hypothesis-67-percent-result/ (fetched; confirms unconditional status, constant, Lean audit)
- technique: Unconditional pair-correlation input (BGST lineage) + removal of the box hypothesis; formalized in Lean 4 + Mathlib
- bottleneck: The averaging structure of pair correlation cannot exclude sparse exceptional sets; each further digit comes from sharper test-function or gap-census inputs
- tunable: Admissible test functions under the framework's (unconditional) constraint set; gap-census floors; joint simple/critical functionals
- gap: The Chirre-Gonçalves-de Laat SDP function class has not been transplanted into this framework (the lab's existing transplant is the gap-census floor, a different lever); Cohn-Elkies-class functions could plausibly move the third decimal, not the fifth

### PCC implies almost all zeros simple and on the critical line
- statement: Montgomery's Pair Correlation Conjecture alone (a statement about vertical distribution, with no RH assumption) implies that asymptotically 100% of the nontrivial zeros are simple and lie on the critical line. Proof introduces a notion of 'horizontal multiplicity'.
- constant: 100% (density one), no rate
- status: pair-correlation-conditional | D. A. Goldston, J. Lee, J. Schettler, A. I. Suriajaya (2025)
- citation: arXiv:2503.15449 (v4, March 2026), 'Pair Correlation Conjecture for the zeros of the Riemann zeta-function I: simple and critical zeros'
- checked against: https://arxiv.org/abs/2503.15449 (abstract fetched)
- technique: Horizontal multiplicity bookkeeping fed by the full-strength PCC on all supports
- bottleneck: No effective rate: the deduction gives density one with no explicit dependence on the modulus of convergence in PCC
- tunable: Support parameter A, test functions on [-A,A], the ε in F ≤ 1+ε
- gap: An effective/quantitative version (proportion as a function of a finite-support PCC bound F(α) ≤ 1+ε on 1 ≤ α ≤ A) is not in the paper and would interpolate between 2/3 and 1

### Small gaps between zeros: liminf normalized gap (RH record)
- statement: Let μ = liminf (γ' - γ) (2π/log γ)^{-1} over consecutive ordinates. Under RH, μ < 0.50895 (Inoue 2026, resonance-correlation method), breaking the barrier of μ < 0.515396 (Preobrazhenskiĭ 2016) that stood for a decade. The paper establishes 0.508 as the rigorous theoretical floor of the Montgomery-Odlyzko method, leaving a ~0.0009 gap.
- constant: μ < 0.50895; method floor 0.508; previous 0.515396
- status: RH-conditional | Shōta Inoue (2026)
- citation: arXiv:2604.05733, 'Small gaps between consecutive zeros of the Riemann zeta-function' (Apr 7, 2026)
- checked against: https://arxiv.org/html/2604.05733v1 (fetched, including method limits and ansatz)
- technique: Resonance-correlation: quadratic count N_h(t)² - N_h(t) instead of N_h(t)-1, approximator Dirichlet polynomial A_X(s) for log ζ shifts, inequality |z|² ≥ 2Re(z w̄) - |w|², resonator coefficients from Bui-Milinovich-Ng
- bottleneck: Oscillating cross terms bounded only via the approximator; and the explicit test-function choice is a LINEAR ansatz f(x) = 1 - 0.7x, which the author flags as improvable by higher-degree polynomials
- tunable: Test function f (currently 1-0.7x), resonator coefficients, approximator coefficients/length X, shift parameter h
- gap: Unharvested and explicitly flagged: optimize f over degree-k polynomials (or general functions) and re-optimize resonator/approximator coefficients jointly; the remaining 0.00095 to the 0.508 floor is the prize

### Small gaps in the pair-correlation window (positive-proportion version)
- statement: Assuming RH, the number of gaps between consecutive zeros smaller than 0.6039 times the average spacing is ≫ N(T); under GRH the constant improves to 0.5769 (previous GRH record 0.5781, Goldston-Gonek-Özlük-Snyder).
- constant: 0.6039 (RH), 0.5769 (GRH)
- status: RH-conditional (GRH variant stated) | A. Chirre, F. Gonçalves, D. de Laat (2020)
- citation: arXiv:1810.08843, Theorem 4; Adv. Math. 361 (2020)
- checked against: https://ar5iv.labs.arxiv.org/html/1810.08843 (fetched)
- technique: SDP over Cohn-Elkies-class test functions applied to the small-gap counting functional
- bottleneck: Same F(α) support restriction; SDP near-converged for the current constraint set
- tunable: SDP test-function coefficients; gap-count weighting
- gap: Inoue's resonance-correlation weighting has not been combined with the SDP function class; the two methods bound different functionals and their hybrid is unexplored

### Large gaps between zeros (unconditional record)
- statement: Unconditionally, there are infinitely many pairs of consecutive zeros of ζ on the critical line whose gap exceeds 3.18 times the average spacing 2π/log γ; i.e. λ = limsup of normalized gaps satisfies λ > 3.18.
- constant: λ > 3.18 (previous GRH-conditional 3.033, Bui 2009)
- status: unconditional | H. M. Bui, M. B. Milinovich (2017)
- citation: arXiv:1410.3635, 'Gaps between zeros of the Riemann zeta-function' (final version 2017)
- checked against: https://arxiv.org/abs/1410.3635 and https://arxiv.org/abs/2412.15481 (abstracts fetched)
- technique: Wirtinger-type inequality plus moments of ζ and ζ' with long Dirichlet polynomials (Hall's method upgraded)
- bottleneck: Moment inputs: higher/twisted moments of |ζ|² |ζ'|² with longer polynomials are the binding constraint
- tunable: Choice of the Wirtinger test function; moment polynomial lengths and coefficients
- gap: Gonek-Sahay (arXiv:2412.15481, Dec 2024) open the question of r CONSECUTIVE moderate gaps ≥ 2πc/log T, a fresh functional with no optimized constants yet

### Fourier optimization bounds on the average of Montgomery's F
- statement: Assuming RH, the average value of Montgomery's function F(α,T) over α ∈ [0,1]-type windows, conjectured to be 1, is proven to lie between 0.9303 and 1.3208. Obtained via new averaging mechanisms plus Cohn-Elkies-class (non-bandlimited) test functions; analogous improvements for Dirichlet L-functions. This sharpens the 'tale of three integrals' program (Carneiro-Chandee-Chirre-Milinovich, Crelle 786 (2022), arXiv:2108.09258) linking ∫F, Selberg's short-interval variance integral, and the second moment of ζ'/ζ near the line.
- constant: 0.9303 ≤ avg F ≤ 1.3208 (conjectured value 1)
- status: RH-conditional | E. Carneiro, M. B. Milinovich, A. P. Ramos (2023)
- citation: arXiv:2310.01913, 'Fourier optimization and Montgomery's pair correlation conjecture'
- checked against: https://arxiv.org/abs/2310.01913 and https://arxiv.org/abs/2108.09258 (abstract + search)
- technique: Extremal problems in Fourier analysis (Beurling-Selberg lineage) with enlarged function classes and averaging over windows
- bottleneck: Both bounds are extremal-problem-limited, not arithmetic-limited: the exact extremal functions for the averaged problems are unknown
- tunable: Test-function pairs (majorant/minorant), averaging measure over windows, Hermite expansion coefficients
- gap: The averaged extremal problems have not been attacked with rigorous SDP (only hand-chosen families); numerically enclosure-checked extremal functions could tighten both ends

### Montgomery-Soundararajan variance moments (de la Bretèche-Fiorilli)
- statement: Lower bounds for all weighted even moments of primes in short intervals of the size predicted by the Montgomery-Soundararajan conjecture (Gaussian moments with variance ~ H log(X/H)): unconditionally for an unbounded set of X, and for all X under RH; with new unconditional Ω-results for ψ(x) - x as corollaries. Via the explicit formula these are lower-bound constraints on averages of the pair-correlation measure, the arithmetic dual of F(α) information beyond |α| ≤ 1.
- constant: Moments match the conjectured Gaussian main term μ_{2k}(H log(X/H))^k up to explicit factors
- status: unconditional (unbounded X-set) / RH-conditional (all X) | R. de la Bretèche, D. Fiorilli (2021)
- citation: arXiv:2009.05760; Math. Annalen (2021)
- checked against: https://arxiv.org/abs/2009.05760 (abstract fetched)
- technique: Positivity of a quadratic form in prime-counting errors; unconditional lower-bound extraction from mean values
- bottleneck: Upper bounds of matching strength are equivalent to strong pair-correlation information and remain open
- tunable: Interval length H, weight functions, moment order k
- gap: The corresponding lower-bound constraints have not been fed back into the zero-side optimization problems as additional SDP constraints on F(α)-averages

### Pair correlation of Dirichlet L-zeros as a route to Chowla / Elliott-Halberstam / Montgomery
- statement: Assuming GRH plus a pair correlation conjecture for zeros of Dirichlet L-functions: (i) Montgomery's conjecture on the error term in the PNT for arithmetic progressions holds in the corrected Friedlander-Granville form; (ii) consequently the Elliott-Halberstam conjecture holds; (iii) the number of χ (mod q) with L(1/2,χ) = 0 is O(q^{1/2+ε})-small (toward Chowla's nonvanishing conjecture).
- status: conditional on GRH + Dirichlet pair correlation conjecture | N. Kandhil, A. Languasco, P. Moree (2025)
- citation: arXiv:2411.19762 (v2, Nov 2025)
- checked against: https://arxiv.org/abs/2411.19762 (abstract fetched)
- technique: q-analogue pair correlation transferred through explicit formulas to progressions
- bottleneck: The q-aspect pair correlation conjecture is even less accessible than PCC; only |α| < 1-type supports are known (q-analogue via Fourier optimization: arXiv:2108.10238)
- tunable: Support of test functions in the q-aspect window; family averaging over moduli
- gap: Effective interpolation: what partial q-aspect support delivers what level of distribution in Elliott-Halberstam has not been tabulated

### de Bruijn-Newman constant pinched by zero statistics
- statement: 0 ≤ Λ ≤ 0.2. Lower bound Λ ≥ 0 (Rodgers-Tao 2018, published Forum Math. Pi 2020): if Λ < 0 the zeros would be locally uniformly spaced, contradicting GUE-consistent fluctuations forced by pair-correlation-type computations. Upper bound Λ ≤ 0.22 (Polymath 15, arXiv:1904.12438), improved to Λ ≤ 0.2 by the Platt-Trudgian rigorous verification of RH to height 3·10^12. RH is equivalent to Λ ≤ 0, i.e. Λ = 0 given RH.
- constant: Λ ∈ [0, 0.2]; verification height 3·10^12 (Platt-Trudgian state 3.0001753328·10^12)
- status: unconditional | B. Rodgers, T. Tao; D. H. J. Polymath; D. Platt, T. Trudgian (2021)
- citation: arXiv:1801.05914 (Λ ≥ 0); arXiv:1904.12438 (Λ ≤ 0.22); arXiv:2004.09765 (RH to 3·10^12, Λ ≤ 0.2)
- checked against: https://arxiv.org/abs/1904.12438 and search results including handwiki.org/wiki/De_Bruijn%E2%80%93Newman_constant
- technique: Backward heat flow rigidity vs. GUE fluctuations (lower); effective H_t approximation + barrier computations + rigorous zero verification (upper)
- bottleneck: Upper bound scales like ~ c / log(height of verification): each halving of Λ-0 costs a quadratic-exponential increase in verified height
- tunable: Barrier location/shape in the (x,t) plane; Euler-product mollifier in the H_t approximation
- gap: The lab's heatflow module can reproduce the H_t barrier computation; nobody has published an SDP-optimized barrier shape, only hand-tuned ones

### Numerical GUE agreement and rigorous verification data
- statement: All nontrivial zeros with 0 < γ ≤ 3·10^12 lie on the critical line and are simple (rigorous, interval-arithmetic verification of 12,363,153,437,138 zeros by Platt-Trudgian). Odlyzko's computations near zero #10^20 and beyond (10^23) show pair correlation and nearest-neighbor spacings matching GUE predictions to within ~10^-3 statistical accuracy, with systematic finite-T deviations matching the T^{-2α} log T term in Montgomery's F.
- constant: Height 3·10^12; 1.2×10^13 zeros, all simple and critical
- status: numerical | D. Platt, T. Trudgian; A. M. Odlyzko (2021)
- citation: arXiv:2004.09765, Bull. LMS 53 (2021); Odlyzko, 'The 10^20-th zero of the Riemann zeta function and 175 million of its neighbors' (unpublished, www.dtc.umn.edu/~odlyzko)
- checked against: search results (arXiv:2004.09765 confirmed); Odlyzko dataset citation memory-unverified
- technique: Riemann-Siegel with rigorous error bounds, interval arithmetic; Odlyzko: multi-precision FFT-based band evaluation
- bottleneck: Finite-T corrections to GUE are known heuristically (Bogomolny-Keating) but few are pinned against rigorous zero data with enclosure-checked error bars
- tunable: Window height, unfolding convention, binning; enclosure-checked enclosure width
- gap: No published ball-arithmetic-enclosure-checked pair correlation histogram exists at large height; lab's moments/statistics + rigor modules can produce one

### Small gaps and small spacings between zeta zeros (unconditional variants)
- statement: Unconditionally there exist gaps between zeros (not necessarily consecutive, and in spacing variants) smaller than a fraction of the average spacing; Goldston-Suriajaya-type results give unconditional small spacings below average, while all sub-0.6 consecutive-gap constants remain RH-conditional. (Constant landscape: unconditional consecutive-gap results remain weak; μ ≤ 0.5172 Conrey-Ghosh-Gonek 1984 on RH was the historical baseline before 0.5154 Feng-Wu, 0.515396 Preobrazhenskiĭ, 0.50895 Inoue.)
- status: unconditional (weak) / RH-conditional (all strong constants); historical chain partly memory-dated | D. A. Goldston, A. I. Suriajaya (2022); chain: Conrey-Ghosh-Gonek, Feng-Wu, Preobrazhenskiĭ, Inoue (2022)
- citation: arXiv:2208.02359, 'Small gaps and small spacings between zeta zeros'
- checked against: https://arxiv.org/pdf/2208.02359 (located via search; abstract not deep-read ,  treat details as lightly verified)
- technique: Pair correlation lower bounds on Σ over pairs in short windows, no RH needed for spacing (as opposed to consecutive-gap) statements
- bottleneck: Without RH, one cannot convert pair-in-window counts into consecutive-gap counts because multiplicity and off-line zeros contaminate the census
- tunable: Window length, test function, weighting
- gap: The narrow-box/unconditional-PC framework (entries above) should convert some spacing statements to consecutive-gap statements; not yet done


## Territory E: equivalent and near-equivalent criteria for RH (Weil positivity, Li coefficients, Nyman-Beurling/Baez-Duarte, Riesz/Hardy-Littlewood, Robin/Lagarias, Speiser, de Bruijn-Newman Lambda, new equivalences 2023-2026)

### Rodgers-Tao: de Bruijn-Newman constant is non-negative
- statement: Lambda >= 0, where Lambda is the de Bruijn-Newman constant: H_t(z) = integral of e^{tu^2} Phi(u) cos(zu) du has only real zeros iff t >= Lambda, and RH is equivalent to Lambda <= 0. Hence RH, if true, is 'barely true': Lambda = 0 exactly under RH.
- constant: Lambda >= 0
- status: unconditional | Brad Rodgers, Terence Tao (2020)
- citation: arXiv:1801.05914; Forum of Mathematics, Pi 8 (2020) e6
- checked against: https://arxiv.org/abs/1801.05914 (located via search); https://en.wikipedia.org/wiki/De_Bruijn%E2%80%93Newman_constant
- technique: Contradiction: if Lambda < 0, backward heat flow forces zeros of H_t toward a rigid, locally lattice-like equilibrium incompatible with unconditional results on the local distribution of zeta zeros (pair-correlation-type estimates on long intervals).
- bottleneck: The argument is purely qualitative at Lambda = 0; no quantitative lower bound Lambda >= f(statistics) exists, and none can exceed 0 without disproving RH.
- tunable: None for the theorem itself; for effective variants: the test statistics (pair correlation windows), the height T of verified data, the time window [t,0] of the backward flow.
- gap: A quantitative 'effective Rodgers-Tao' relating finite-height zero statistics to lower bounds on Lambda restricted to finite time windows has not been written down; the lab's heatflow.py tracks exactly the H_t zero dynamics used in the proof.

### Upper bound for the de Bruijn-Newman constant
- statement: Lambda <= 0.2. Chain: Polymath15 proved Lambda <= 0.22 by certifying that H_t has no zeros off the real axis in an explicit barrier region for t = 0.22, using RH verified to height ~6*10^10; Platt-Trudgian's rigorous interval-arithmetic verification that all zeros with 0 < gamma <= 3*10^12 have beta = 1/2 pushes the same pipeline to Lambda <= 0.2. Combined with Rodgers-Tao: 0 <= Lambda <= 0.2.
- constant: 0 <= Lambda <= 0.2
- status: unconditional | D.H.J. Polymath (Polymath15); Dave Platt, Tim Trudgian (2020)
- citation: arXiv:1904.12438 (Res. Math. Sci. 6 (2019) 31); arXiv:2004.09765 (Bull. LMS 53 (2021))
- checked against: https://en.wikipedia.org/wiki/De_Bruijn%E2%80%93Newman_constant and https://arxiv.org/abs/2004.09765 (abstract fetched; the 0.2 attribution to Platt-Trudgian April 2020 confirmed via Wikipedia, not the paper's abstract itself)
- technique: Effective approximation H_t ~ B_t (Riemann-Siegel-type effective asymptotics for the heat-flowed xi), a winding-number barrier enclosure-checked by interval arithmetic, plus the finite RH verification to convert 'zeros real below the barrier' into 'zeros real everywhere at time t'.
- bottleneck: Required verification height grows very rapidly as the target Lambda decreases (Polymath15's ninth-thread analysis: going well below 0.2 needs heights orders of magnitude beyond 3*10^12); the barrier certification cost also grows with the barrier location.
- tunable: Heat-flow time t, barrier abscissa X, strip height y_0, mesh resolution, Euler-product mollifier b_n in B_t, tail truncation bounds.
- gap: The 0.2 figure was a convenient round number, not an optimized one: the (t, y, barrier-x) parameter landscape at fixed height 3*10^12 was never exhaustively re-optimized, and no one has redone the pipeline with Arb throughout. A shave to ~0.19 may be available without new zero verification.

### Nyman-Beurling-Baez-Duarte criterion and the Burnol lower bound
- statement: Let d_N^2 = inf over Dirichlet polynomials A_N(s) = sum_{n<=N} a_n n^{-s} of (1/(2*pi)) * integral over R of |1 - zeta(1/2+it) A_N(1/2+it)|^2 dt/(1/4+t^2). RH iff d_N -> 0 (Nyman 1950, Beurling 1955; Baez-Duarte 2003 reduced to integer dilates). Burnol: unconditionally, liminf_{N->inf} d_N^2 log N >= sum over zeros rho with Re(rho)=1/2 of m(rho)^2/|rho|^2, where m is multiplicity. If RH holds and all zeros are simple, that sum equals 2 + gamma - log(4*pi) = 0.0461914179...
- constant: conjectured lim d_N^2 * log N = 2 + gamma - log(4*pi) = 0.0461914179...; e^gamma etc. exact
- status: unconditional | Jean-Francois Burnol (lower bound); Nyman, Beurling, Baez-Duarte (criterion) (2002)
- citation: arXiv:math/0103058 (Adv. Math. 170 (2002)); L. Baez-Duarte, Atti Accad. Naz. Lincei 14 (2003)
- checked against: https://arxiv.org/pdf/math/0103058 and search results confirming the Burnol bound and the constant 2+gamma-log(4pi)
- technique: Hilbert-space distance to the constant function in H^2 of the half-plane with the 1/(1/4+t^2) measure; reproducing-kernel evaluation at zeros gives the lower bound.
- bottleneck: Any unconditional upper bound d_N = o(1) IS RH; conditionally, matching the lower bound requires controlling sums of 1/|zeta'(rho)|^2 (discrete moments), which are far out of reach.
- tunable: The coefficient vector (a_n)_{n<=N} (a finite-dimensional least-squares problem: Gram matrix G_{m,n} with Vasyunin cotangent-sum entries); choice of dilation set; weight modifications.
- gap: The conjecture d_N^2 ~ (2+gamma-log 4pi)/log N is supported only by conditional work and small-N numerics (Landreau-Richard style, N in the low thousands, float grade). No enclosure-carrying values of d_N^2 exist at any N; the exact Gram matrix is computable via the Vasyunin cotangent-sum formula.

### Bettin-Conrey-Farmer: conditional optimality of mollified Dirichlet polynomials in NBBD
- statement: Assuming RH and the discrete moment bound sum over zeros rho with |Im rho| <= T of 1/|zeta'(rho)|^2 << T^{3/2-delta} for some delta > 0, the NBBD constant lim d_N^2 log N equals Burnol's lower bound 2 + gamma - log(4*pi), achieved by an explicit mollifier-type choice of coefficients a_n.
- constant: 2 + gamma - log(4*pi) = 0.0461914179... under the stated hypotheses
- status: RH-conditional (plus a discrete-moment hypothesis weaker than Gonek's conjecture) | Sandro Bettin, J. Brian Conrey, David W. Farmer (2012)
- citation: arXiv:1211.5191
- checked against: https://arxiv.org/abs/1211.5191 (abstract fetched)
- technique: Mollifier choice a_n = mu(n) * (smoothing factor), evaluation of the resulting quadratic form via zeta moment machinery, discrete moments over zeros.
- bottleneck: The hypothesis sum 1/|zeta'(rho)|^2 << T^{3/2-delta} is open (Gonek/Hejhal conjecture predicts ~ (3/pi^3) T, so the hypothesis is 'true with room' conjecturally but unproven).
- tunable: Mollifier shape (the smoothing factor multiplying mu(n)), truncation N, secondary-term corrections.
- gap: The finite-N gap between the BCF mollifier's quadratic-form value and the true optimum (linear-solve optimum) has never been measured; it quantifies how much of the conjecture is visible at computable N and which coefficient patterns close the gap.

### Pyvovarov: exponentially damped Mobius approximants in the Baez-Duarte criterion
- statement: For the strong Baez-Duarte criterion, Mobius coefficients are the unique choice giving pointwise convergence to the constant function; <1|f(u)> -> 1; the canonical third-order truncation satisfies F_(3)(x) << log^2(e/(1-x))/(1-x); the unresolved boundedness problem for the approximants is reduced to an explicit 'global bilinear cancellation' statement.
- constant: F_(3)(x) << log^2(e/(1-x))/(1-x)
- status: unconditional (partial results toward a criterion) | Alexandre Pyvovarov (2026)
- citation: arXiv:2607.12084 (submitted 2026-07-13, revised 2026-07-21)
- checked against: https://arxiv.org/abs/2607.12084 (abstract fetched)
- technique: Vasyunin-formula analysis of F(e^{-u}) = ||f(u)||_2^2 as an arithmetic cotangent sum; exact edge and residue-character cancellations; finite-scale formulas.
- bottleneck: The 'explicit global bilinear cancellation' is the whole remaining difficulty; it is a bilinear sum over Farey-type fractions with cotangent weights.
- tunable: Damping parameter in the exponential damping, truncation order (third-order vs higher), the bilinear-form test vectors.
- gap: Paper is one month old (July 2026): its finite-scale formulas have not been numerically stress-tested by anyone, and the conjectured bilinear cancellation is exactly the kind of statement a high-precision computation can support or kill at specific scales.

### Li's criterion and the Voros dichotomy
- statement: RH iff lambda_n >= 0 for all n >= 1, where lambda_n = sum over nontrivial zeros rho of [1 - (1 - 1/rho)^n] (Li 1997). Bombieri-Lagarias gave the arithmetic/archimedean decomposition via the explicit formula. Voros: RH iff lambda_n grows temperedly, lambda_n ~ (n/2) log n; specifically under RH lambda_n = (n/2)(log n + gamma - 1 - log(2*pi)) + lower order, while any zero off the line forces exponentially growing oscillations in n.
- constant: lambda_1 = 0.0230957089661210..., lambda_2 = 0.0923457352280475... (standard values); main term (n/2)(log n + gamma - 1 - log 2pi)
- status: unconditional criterion; the asymptotic main term is RH-conditional | Xian-Jin Li; Enrico Bombieri, Jeffrey Lagarias; Andre Voros (1997)
- citation: X.-J. Li, J. Number Theory 65 (1997) 325-333; Bombieri-Lagarias, J. Number Theory 77 (1999); Voros arXiv:math/0506326-adjacent (see Coffey, arXiv:math/0506326)
- checked against: https://arxiv.org/abs/math/0506326 (located via search; exact lambda_1, lambda_2 digits from memory-unverified)
- technique: Power-series coefficients of the logarithmic derivative of xi at s=1; explicit formula splits lambda_n into archimedean and prime terms; saddle-point analysis for asymptotics.
- bottleneck: Positivity for all n is equivalent to RH; partial positivity (n <= X) yields only zero-free regions near s=1 of strength comparable to classical ones, so the criterion has not produced new unconditional information.
- tunable: n-range, choice of route (zero-sum vs arithmetic formula), smoothing of the zero sum, Kreminski-style acceleration.
- gap: The size of the fluctuation lambda_n - (archimedean main term) under RH is conjecturally O(sqrt(n) log n) (GUE-consistent) but the best proven conditional error term and the numerics have not been pushed past n ~ a few thousand with rigor; the lab's li.py has two independent routes and exact Sturm machinery, unused at large n.

### Weil positivity: archimedean and semilocal cases (Connes-Consani(-Moscovici))
- statement: RH iff W(g * g~) >= 0 for all g in C_c^infty(R_+^*), where W is the Weil distribution (sum over zeros = archimedean term minus prime terms). Proven unconditionally: positivity of the archimedean part of the Weil functional expressed via the Sonin trace and prolate spheroidal wave functions (Connes-Consani, Selecta Math 2021); extension to a semilocal prolate wave operator handling finitely many places, with stability of the semilocal Sonin space as the set of places grows (Connes-Consani-Moscovici 2023-24). Test functions with support in [1/sqrt(2), sqrt(2)] (no prime enters) give positivity by Yoshida/Suzuki-type results.
- constant: positivity known for test support within [2^{-1/2}, 2^{1/2}] (exact interval memory-unverified); no prime contributes for lambda^2 <= 2
- status: unconditional partial positivity; full positivity is RH-equivalent | Alain Connes, Caterina Consani, Henri Moscovici (2024)
- citation: arXiv:2006.13771 (Selecta Math 27 (2021)); arXiv:2310.18423 (rev. 2024-05-04)
- checked against: https://arxiv.org/abs/2310.18423 and https://arxiv.org/abs/2006.13771 (abstracts fetched); support-interval detail memory-unverified
- technique: Trace formula on the adele class space; Sonin spaces; prolate spheroidal operators as sum of square of scaling operator and grading of orthogonal polynomials; metaplectic representation of the double cover of SL(2,R).
- bottleneck: Extending the support of test functions past the point where infinitely many primes contribute: each prime term enters with negative sign and destroys manifest positivity; no mechanism controls the full prime sum.
- tunable: Test function support length lambda, the finite set of places S in the semilocal case, Galerkin band dimension, choice of orthogonal basis (prolate functions).
- gap: Quantitative question wide open: for support [lambda^{-1}, lambda], what is the largest lambda for which positivity is provable? Yoshida-type results give small lambda; nobody has published the numerical positivity boundary as a function of lambda with enclosure-checked eigenvalue computations.

### Suzuki: Weil's quadratic form via screw functions
- statement: Weil's quadratic form for zeta is reformulated through a screw function g_zeta(t) (Krein theory), unifying Yoshida (1992), Bombieri (2001, 2003), and Connes-Consani(-Moscovici) (2023-2025+) positivity results with continuous functions instead of distributions, all without assuming RH. Central conjecture: a self-adjoint operator whose eigenvalues are the imaginary parts of the nontrivial zeros arises as the a -> infinity limit of self-adjoint realizations of a nonlocal differential operator on [-a, a] built from g_zeta.
- constant: none yet (conjecture-stage)
- status: unconditional reformulation; the operator-limit statement is a conjecture | Masatoshi Suzuki (2026)
- citation: arXiv:2606.09096 (submitted 2026-06-08)
- checked against: https://arxiv.org/abs/2606.09096 (abstract fetched)
- technique: Krein's theory of screw functions/strings; canonical systems; reduction of Weil positivity on interval-supported test functions to properties of g_zeta on [-2 log a, 2 log a].
- bottleneck: Passing from finite-interval self-adjoint realizations to the limit operator: no convergence theorem for the spectra as a -> infinity.
- tunable: Interval half-length a, discretization of the nonlocal operator, boundary conditions of the self-adjoint realization, truncation of the prime sum inside g_zeta.
- gap: Two months old and numerically untouched: the finite-interval operators are concretely computable, and their low eigenvalues vs the actual gamma_n as a function of a is a fresh falsifiable surface. Convergence rate data would inform whether the conjecture is plausible or dead.

### Truncated Weil form: finite-rank windows and provable critical-line ground states
- statement: For each prime cutoff c > 1 the truncated Weil quadratic form on L^2([0, log c]) admits a unique even-sector ground state whose Fourier-Mellin zeros provably lie on the critical line; high-precision numerics show these track actual Riemann zeros. A finite Guinand-Weil dictionary gives an explicit (2N+1)x(2N+1) Galerkin matrix per cutoff c and band N, with a stated archimedean tail order. Open: whether ground-state zeros converge to the actual zeta zeros as c -> infinity.
- constant: matrix dimension (2N+1)x(2N+1); tail order as stated in arXiv:2607.02828 (exact exponent not extracted)
- status: numerical plus partial theorems | authors not independently confirmed (recent arXiv postings; provenance and refereeing status unverified, possibly AI-assisted labs) (2026)
- citation: arXiv:2605.20224; arXiv:2607.02828
- checked against: https://arxiv.org/html/2605.20224 and https://arxiv.org/pdf/2607.02828 (titles/abstract snippets via search; full statements not independently re-derived)
- technique: Galerkin truncation of the Weil form in a Fourier basis on [0, log c]; explicit formula bookkeeping for the finite prime window; ground-state extraction.
- bottleneck: No convergence theorem in c; the archimedean tail estimate controls band truncation but not the prime-window limit.
- tunable: Cutoff c, band N, basis choice, weighting of the archimedean term.
- gap: Neither paper reports enclosure-carrying eigenvalue computations; the smallest-eigenvalue sign as a function of (c, N) is exactly the finite window on Weil positivity and is unmined with enclosure-checked arithmetic. Caution: these postings are weeks old, unrefereed, and should be independently re-derived before being built upon.

### Robin's criterion, Lagarias's criterion, and verified ranges
- statement: RH iff sigma(n) < e^gamma * n * log log n for all n > 5040, with e^gamma = 1.781072417990197985... (Robin 1984). Equivalent (Lagarias 2002): RH iff sigma(n) <= H_n + exp(H_n) log(H_n) for all n >= 1. Verified: Robin's inequality holds for all 5041 <= n <= 10^(10^13.11485) (Morrill-Platt) and for all colossally abundant n up to 10^(10^10) (Briggs). Unconditional structural results: any counterexample > 5040 implies a colossally abundant counterexample; the inequality holds for all odd n > 9 and for all 20-free integers > 5040. Zimov (2025): if RH is false, the least colossally abundant exception satisfies e^gamma < G(n) < e^gamma (1 + c/(log n)^b) with 0 < b < 1/2, excluding it from Robin's guaranteed infinite family of large violations.
- constant: threshold n > 5040; e^gamma = 1.7810724179901979852...; verified to 10^(10^13.11485)
- status: unconditional criterion; ranges numerical (exact-arithmetic); Zimov result unconditional-structural | Guy Robin; Jeffrey Lagarias; Keith Briggs; Thomas Morrill, Dave Platt; Bruce Zimov (2025)
- citation: Robin, J. Math. Pures Appl. 63 (1984); Lagarias, Amer. Math. Monthly 109 (2002); arXiv:2510.23889 (Zimov, 2025-10-27); Morrill-Platt arXiv:1809.10813 (Ramanujan J.)
- checked against: https://arxiv.org/abs/2510.23889 (abstract fetched); Morrill-Platt/Briggs ranges via search summary of arXiv:2110.13478-adjacent sources; Lagarias citation memory-unverified in exact form
- technique: Extremal analysis of sigma(n)/n on colossally abundant numbers (superabundant parameterization by prime-exponent vectors); explicit prime bounds; ratios of consecutive CA numbers (Zimov).
- bottleneck: The criterion concentrates RH into the CA sequence, but CA numbers grow doubly exponentially, and the gap between e^gamma and G(n) shrinks like c/(log n)^b only if RH fails; proving Robin unconditionally for CA numbers is equivalent to RH.
- tunable: CA exponent-vector enumeration depth, prime bounds used (Rosser-Schoenfeld vs newer), the exponent b and constant c in Zimov's band.
- gap: Briggs's CA verification (10^(10^10)) is 20 years old and float-grade in places; a enclosure-checked (rational/interval arithmetic on exponent vectors) extension to 10^(10^12) or beyond is mechanical. Zimov's band constants (c, b) are not pinned numerically. Lean has no formalized Robin criterion or finite verification.

### Riesz and Hardy-Littlewood criteria, extended to general L-functions
- statement: Riesz (1916): RH iff sum_{n>=1} (-1)^{n+1} x^n / ((n-1)! zeta(2n)) = O_epsilon(x^{1/4+epsilon}). Hardy-Littlewood (1918): RH iff sum_{n>=1} mu(n)/n * exp(-x/n^2) = O_epsilon(x^{-1/4+epsilon}). Garg-Maji (2024): one-variable generalized identities and equivalent Riesz/HL-type criteria for the Riemann hypothesis of a general class of L-functions including Dirichlet L-functions and L-functions of primitive Hecke cusp forms, settling a conjecture from the earlier Dirichlet case (arXiv:2208.07596, Monatsh. Math. 2023).
- constant: exponent 1/4 (equivalently -1/4) exact in both classical criteria
- status: unconditional criteria | Marcel Riesz; G.H. Hardy, J.E. Littlewood; Meghali Garg, Bibekananda Maji (2024)
- citation: arXiv:2409.17708; arXiv:2208.07596 (Monatsh. Math. 202 (2023))
- checked against: https://arxiv.org/abs/2409.17708 (search summary with exact HL bound); classical statements cross-checked against the same source
- technique: Mellin inversion of 1/zeta(2s) against exponential kernels; functional-equation symmetrization; one-variable interpolation between Riesz and Hardy-Littlewood kernels.
- bottleneck: The criterion repackages M(x) << x^{1/2+epsilon}-strength information; no unconditional exponent better than trivial is known for the Riesz sum, and improving the exponent at all is Mobius-cancellation-hard.
- tunable: The interpolation parameter in the one-variable kernel family, truncation of the mu-sum, choice of L-function.
- gap: The finite-x behavior of the generalized (cusp form) Riesz sums has never been computed; the kernels contain a free interpolation parameter whose optimal finite-x choice is unexplored. Numerics could also calibrate how early the conjectured x^{1/4+epsilon} regime is visible.

### Speiser's criterion and its quantitative Levinson-Montgomery form
- statement: Speiser (1935): RH iff zeta'(s) has no zeros in the open strip 0 < Re(s) < 1/2. Levinson-Montgomery (1974) quantitative form: N_1^-(T), the number of zeros of zeta' with Re(s) < 1/2 and 0 < Im(s) < T, equals N^-(T), the corresponding count for zeta, up to O(log T); hence zeta and zeta' have essentially the same number of zeros left of the critical line. This underlies Levinson's method. Active 2024-25 work extends the distribution theory to higher derivatives zeta^(k).
- constant: N_1^-(T) = N^-(T) + O(log T)
- status: unconditional | Andreas Speiser; Norman Levinson, Hugh Montgomery (1974)
- citation: Speiser, Math. Ann. 110 (1935); Levinson-Montgomery, Acta Math. 133 (1974); recent: J. Math. Anal. Appl. (2024), S0022247X24004530
- checked against: https://www.sciencedirect.com/science/article/abs/pii/S0022247X24004530 (located via search); Levinson-Montgomery statement memory-unverified in exact error-term form
- technique: Argument principle comparison of zeta and zeta' along the critical line; the functional equation forces pairing of left-strip zeros.
- bottleneck: The O(log T) slack means finite verifications for zeta do not automatically certify the Speiser region for zeta'; and no enclosure-checked computation of zeta' non-vanishing in 0 < sigma < 1/2 up to explicit heights exists in the literature (float computations of zeta' zeros exist).
- tunable: Height T, contour decomposition for the argument principle, precision schedule.
- gap: An enclosure-carrying verification 'zeta' has no zeros with 0 < Re s < 1/2, 0 < Im s <= T' for concrete T would be, to our knowledge after search, the first enclosure-checked finite Speiser statement; searches found no such certificate.

### Kuipers: dynamical contraction criterion equivalent to RH
- statement: RH iff the trajectory error functional of an explicit discrete dynamical system (composites m map forward to m + pi(m); primes p map backward to p - prevprime(p)) satisfies E(X) << X^{1/2} log X, i.e. integer trajectories remain uniformly contracted at scale X^{1/2} log X. Forward direction from von Koch's bound psi(x) = x + O(x^{1/2} log^2 x) under RH; converse via Landau-Littlewood Omega-results: off-critical zeros violate the contraction inequality. Unconditional contraction inequalities for the error terms are proved.
- constant: contraction scale X^{1/2} log X
- status: unconditional equivalence (new, unrefereed) | Hendrik Wladimir Albrecht Edwin Kuipers (2025)
- citation: arXiv:2509.10588 (submitted 2025-09-12)
- checked against: https://arxiv.org/abs/2509.10588 (abstract fetched)
- technique: Repackaging of psi(x) - x error bounds as trajectory displacement sums; explicit remainder bookkeeping.
- bottleneck: Depth: the equivalence is a reparameterization of von Koch's criterion, so it inherits, rather than bypasses, the difficulty of bounding psi(x) - x.
- tunable: The explicit constants in the unconditional inequalities; trajectory ensemble weighting.
- gap: The unconditional contraction inequalities carry explicit constants that have not been independently checked or optimized; a cheap numerical audit at X up to 10^9 would either validate the constants or find a defect (fresh unrefereed paper).

### Polya frequency order of the de Bruijn-Newman kernel
- statement: The de Bruijn-Newman kernel Phi(u) (whose cosine transform is H_0 = (1/8) Xi(z/2)) fails to be a Polya frequency function of order five, established by enclosure-checked computation, together with a 'Toeplitz threshold phenomenon' for the associated Toeplitz-minor positivity tests (title-level information; full statement not independently extracted).
- constant: failure at order 5 (per title)
- status: numerical (enclosure-checked-computation-assisted), unrefereed | not independently confirmed (February 2026 arXiv posting; possibly adjacent to or produced by an AI-operated lab; treat as unvetted and check for overlap with this lab's own heatflow work before citing) (2026)
- citation: arXiv:2602.20313
- checked against: https://arxiv.org/pdf/2602.20313 (title via search only; contents not fetched ,  treat details as unverified)
- technique: Toeplitz/Hankel minor positivity criteria for Polya frequency functions applied to Phi, with interval-arithmetic certification of a violating minor.
- bottleneck: Total positivity of all orders for Phi would relate to reality-preservation properties of the heat flow; a failure at finite order limits which totally-positive-kernel arguments can apply to Lambda.
- tunable: Minor order, node placement, scaling of the kernel argument.
- gap: The threshold phenomenon (at which order/scale minors change sign) is a one-paper subject as of Feb 2026: mapping the full (order, shift) sign diagram of Phi's minors with enclosures is days of work in this lab and would either confirm or correct the posting.


## Territory F: spectral and operator approaches to RH (Hilbert-Polya, Connes-Consani-Moscovici prolate/spectral-triple program, Connes-van Suijlekom truncated Weil form, Berry-Keating xp descendants, Bender-Brody-Muller, transfer operators, de Branges/canonical systems, Alcantara-Bode, Yang-Yang/statistical-mechanics analogies), state of the art as of August 2026

### Zeta Spectral Triples (finite self-adjoint operators whose spectra track low zeta zeros)
- statement: Connes, Consani and Moscovici construct self-adjoint operators as rank-one perturbations of the spectral triple associated with the scaling operator on the interval [lambda^{-1}, lambda], incorporating Euler products over primes p <= x = lambda^2. Numerically, the spectra align with the low nontrivial zeros of zeta(1/2+is) with striking accuracy even for small x, and suitably normalized regularized determinants appear to converge to the Riemann Xi function. The authors state explicitly that a rigorous proof of this convergence (as N, lambda -> infinity) would establish the Riemann Hypothesis; that proof is open.
- status: numerical (spectral match and determinant convergence) atop an unconditional operator construction; the convergence statement is a conjecture whose proof would imply RH | Alain Connes, Caterina Consani, Henri Moscovici (2025)
- citation: arXiv:2511.22755 (submitted 2025-11-27)
- checked against: https://arxiv.org/abs/2511.22755
- technique: rank-one perturbations of the scaling operator on [lambda^{-1},lambda]; finite Euler products; Galerkin/trigonometric basis computations; regularized determinants
- bottleneck: no convergence theorem: nothing controls the spectrum of the finite operator against the true zeros as lambda, N grow; the numerical match has no error term
- tunable: lambda (interval scale), N (basis dimension), prime cutoff x = lambda^2, choice of rank-one perturbation vector, determinant regularization
- gap: no published error-rate law for eigenvalue-vs-zero discrepancy as a function of (lambda, N, prime cutoff x); no counterexample control (has anyone run the analogous construction on a Davenport-Heilbronn-type function that violates RH?); determinant-to-Xi convergence unquantified

### UV prolate spectrum matches squares of zeta zeros
- statement: The prolate spheroidal differential operator W_lambda = -d/dx((lambda^2-x^2)d/dx) + (2*pi*lambda*x)^2, restricted to the complement of the interval [-lambda,lambda] and given a specific self-adjoint extension, admits (besides a replica of the positive prolate spectrum) negative eigenvalues whose ultraviolet (counting-function) behavior reproduces that of the squares of the zeros of the Riemann zeta function; the corresponding eigenfunctions lie in the Sonin space. This asymptotic match is proven; the identification of individual eigenvalues with individual zeros is numerical for low-lying ones.
- status: unconditional (UV/counting asymptotics theorem); numerical for low-lying eigenvalue-to-zero matching | Alain Connes, Henri Moscovici (2022)
- citation: arXiv:2112.05500; PNAS 119 (2022), e2123174119 ('The UV prolate spectrum matches the zeros of zeta')
- checked against: https://arxiv.org/abs/2112.05500
- technique: self-adjoint extensions of the prolate operator, Sonin space, compression of the scaling action, Dirac operator isospectral family, metaplectic representation
- bottleneck: the theorem is about the counting function (UV asymptotics), which any operator with the right Weyl law satisfies; pinning individual eigenvalues to individual zeros needs the full trace-formula machinery, which is where positivity is open
- tunable: lambda, the self-adjoint extension parameter, discretization basis for the Sonin-space computation
- gap: no published second-order term comparison between the negative-eigenvalue counting function and N(T) = (T/2pi)log(T/2pi e) + 7/8 + S(T); low-lying match only eyeballed in figures

### Semilocal prolate wave operators
- statement: A semilocal analogue of the prolate wave operator is defined within the semilocal trace formula framework (finitely many places including the archimedean one): in the archimedean case the prolate operator equals the sum of the square of the scaling operator and the grading of orthogonal polynomials, and this formulation extends to the semilocal case. The positive spectrum realizes low-lying zeta zeros; the negative spectrum (semilocal Sonin space) captures UV behavior, and the semilocal Sonin space is proven stable under enlargement of the finite set of places.
- status: unconditional (operator construction and Sonin-space stability); spectral realization of zeros remains asymptotic/numerical as in the archimedean case | Alain Connes, Caterina Consani, Henri Moscovici (2024)
- citation: arXiv:2310.18423; Annals of Functional Analysis 15, Paper No. 87 (2024), 38 pp.
- checked against: https://arxiv.org/abs/2310.18423
- technique: semilocal adelic trace formula, prolate wave operator as square-of-scaling plus grading, de Branges-style entire-function Hilbert spaces, metaplectic representation of the double cover of SL(2,R)
- bottleneck: extending from finitely many places to all places (the adelic limit) while keeping the operator's self-adjointness and the Sonin-space structure; the promised 'second candidate' semilocal prolate operator signals the first is not yet canonical
- tunable: the finite set of places S, lambda, choice among candidate semilocal prolate operators
- gap: no numerical study of the semilocal (p included) prolate spectrum against zeros exists in public code; the dependence of the low-lying match on the set of included primes is unmeasured

### Weil positivity at the archimedean place
- statement: Connes and Consani prove positivity of the Weil functional restricted to the single archimedean place: the root of the positivity is the trace of the scaling action compressed onto the orthogonal complement of the range of the phase-space cutoff projections at cutoff parameter 1; the difference between the Weil distribution and the Sonin trace is expressed via prolate spheroidal wave functions and controlled with hermitian Toeplitz matrices. All ingredients make sense in the general semilocal case, where full Weil positivity (for all test functions, all places) is equivalent to RH.
- status: unconditional theorem for the archimedean place; full (adelic) Weil positivity remains the open problem equivalent to RH | Alain Connes, Caterina Consani (2021)
- citation: arXiv:2006.13771; Selecta Mathematica (N.S.) 27, Article 77 (2021)
- checked against: https://arxiv.org/abs/2006.13771 (abstract) and https://arxiv.org/abs/2106.01715
- technique: semi-local trace formula Hilbert space, phase-space cutoff projections, prolate spheroidal wave functions, Toeplitz matrix estimates
- bottleneck: the Toeplitz/prolate estimates degrade when finite places are added; nobody has pushed the compression argument past the archimedean-only case to even a single prime
- tunable: test-function support parameter S, cutoff parameter, Toeplitz truncation size
- gap: a quantitative version (lower bound on the compressed trace as a function of the support parameter of the test function) is not extracted; the 2021 'Spectral triples and zeta-cycles' companion (arXiv:2106.01715) found very small eigenvalues of the restricted Weil quadratic form, whose decay rate in S is unquantified in print

### Connes-van Suijlekom truncated Weil quadratic form: finite-c critical-line theorem
- statement: For the truncated Weil quadratic form indexed by a prime cutoff c (primes p <= c enter the operator) and frequency band N, the ground state of the finite Galerkin matrix determines a function whose Fourier-Mellin zeros provably lie on the critical line for every finite c; whether these zeros converge to the actual Riemann zeros as c -> infinity is stated by Connes (Feb 2026, 'Past, Present and a Letter Through Time', Section 6) as an open question.
- constant: ground-state zeros on Re(s)=1/2 exactly, for every finite c
- status: unconditional finite-c theorem (critical-line location of ground-state zeros); the convergence to Riemann zeros is open/conjectural | Alain Connes, Walter van Suijlekom (2025)
- citation: Connes-van Suijlekom 2025 (cited as the source theorem in arXiv:2605.20224 and arXiv:2607.02828); framework in Connes-van Suijlekom, Comm. Math. Phys. 383 (2021), 2021-2067
- checked against: https://arxiv.org/html/2605.20224v1 (states the CvS 2025 theorem and the open convergence question); primary CvS 2025 arXiv ID not directly fetched
- technique: operator systems / spectral truncation of noncommutative geometry applied to the Weil quadratic form; Galerkin matrices in a trigonometric basis
- bottleneck: convergence of the ground-state zeros to the Riemann zeros as c -> infinity; no rate, no compactness argument
- tunable: prime cutoff c, band N, basis choice, sector (even/odd), which eigenvector (ground state vs excited)
- gap: the convergence question is explicitly posed and open as of Feb 2026; the finite-c objects are cheap matrices, so the empirical convergence law (error vs c and N) is an unmined surface only one author (Groskin) has touched

### High-precision computation of the truncated Weil form (Groskin)
- statement: First public implementation of the Connes-van Suijlekom Galerkin matrix at sixteen cutoffs (c = 13 through 67, and c = 100): the first-zero error shrinks monotonically from ~2e-55 (c=13) to ~1.5e-168 (c=67) at band N=100; at c=100 with N=250 the smallest positive even-sector eigenvalue reaches ~1e-334 and the ground eigenvector recovers the first ten Riemann zeros to 307-329 matching decimal digits. The author states 'we make no claim of proof'.
- constant: first-zero error ~2e-55 (c=13, N=100) down to ~1.5e-168 (c=67); smallest positive even-sector eigenvalue ~1e-334 at c=100, N=250
- status: numerical | Akiva Groskin (2026)
- citation: arXiv:2605.20224 (v4, 2026-08-14)
- checked against: https://arxiv.org/abs/2605.20224
- technique: variable-precision Galerkin discretization of the CvS truncated Weil form; eigen-decomposition; Fourier-Mellin zero extraction from the ground eigenvector
- bottleneck: single-author, single-implementation numerics with no interval-arithmetic certification; the observed convergence rate has no fitted law and no theoretical explanation
- tunable: c, N, precision, sector, eigenvector index
- gap: no independent replication; no ball-arithmetic enclosure of any eigenvalue; odd sector and excited states less explored; no fit of error ~ f(c,N) that would sharpen the open convergence conjecture into a falsifiable rate statement

### Finite Guinand-Weil dictionary and archimedean tail budget
- statement: Two exact finite theorems about the truncated Weil form: (1) every real even Galerkin coefficient vector v determines in closed form a band-limited Guinand-Weil test function g_v whose sum over the nontrivial zeros of zeta equals the quadratic value <v,Qv> exactly; (2) the omitted archimedean tail beyond the Galerkin band is a totally positive Cauchy-Stieltjes increment with explicit budget B_T ~ (2N+1) * rho * log(T) / (pi^2 * T) where rho = 2*pi/log(c), giving a two-sided certification rule: Galerkin eigenvalues below -B_T certify cutoff-free negativity, values in [-B_T, 0) are undetermined. Verified numerically over the first 512 zeros.
- constant: B_T ~ (2N+1) * (2pi/log c) * log(T) / (pi^2 * T)
- status: unconditional finite theorems plus numerical verification; explicitly disclaims any RH claim | Akiva Groskin (2026)
- citation: arXiv:2607.02828 (v3, 2026-08-14)
- checked against: https://arxiv.org/abs/2607.02828
- technique: closed-form band-limited test functions dual to Galerkin vectors; total positivity of the archimedean tail; explicit tail-order bound
- bottleneck: the tail budget B_T is an order statement, not a sharp constant; certification of negativity says nothing about positivity (which is the RH-relevant direction)
- tunable: T (archimedean cutoff), N, c, the choice of band-limited window in the closed-form dictionary
- gap: the constant in B_T looks improvable (the totally-positive structure suggests a sharp Cauchy-Stieltjes bound); the dictionary has not been cross-checked against an independent explicit-formula implementation; extension to odd vectors and to Dirichlet L-functions untouched

### Yakaboylu's Hilbert-Polya operator with positive intertwiner
- statement: A non-self-adjoint operator R_zeta on L^2([0,infinity)) is constructed whose point spectrum is {i(1/2 - lambda) : lambda in Z_Lambda} with Z_Lambda containing the nontrivial zeta zeros (plus prefactor zeros). It is rigorously proven that W R_zeta = R_zeta^dagger W for a positive semidefinite operator W >= 0. If W were strictly positive definite (which the author presents as an operator-theoretic form of Weil's criterion), R_zeta would be similar to a self-adjoint operator and all zeros would satisfy Re(rho) = 1/2; the argument also assumes simplicity of the zeros. Earlier version published as J. Phys. A 57 (2024) 235204 ('Hamiltonian for the Hilbert-Polya conjecture').
- status: unconditional (intertwining relation with W >= 0); the RH conclusion is conditional on strict positivity of W and on simplicity of zeros | Enderalp Yakaboylu (2026)
- citation: arXiv:2408.15135 (v16, 2026-07-29); J. Phys. A: Math. Theor. 57, 235204 (2024)
- checked against: https://arxiv.org/abs/2408.15135
- technique: quasi-Hermitian / metric-operator quantum mechanics; Mellin-space compression; intertwining operators
- bottleneck: strict positivity of W is exactly as hard as Weil positivity: the operator repackages the criterion rather than advancing it; kernel of W corresponds to hypothetical off-line or multiple zeros
- tunable: truncation basis and size for W, test-function class, the Lambda-regularization parameter
- gap: the finite-dimensional truncations of W have never been computed publicly: their smallest eigenvalues as a function of truncation size would measure how 'close to singular' W is, and running the same construction on the Davenport-Heilbronn function (where the analogue of W must fail strict positivity) is an obvious unperformed discriminating test

### Bender-Brody-Muller Hamiltonian and its breakdown
- statement: BBM (PRL 118, 130201 (2017)) proposed H = (1/(1-e^{-ip}))(xp+px)(1-e^{-ip}), formally non-Hermitian with iH PT-symmetric, whose eigenfunctions obeying a boundary condition have eigenvalues E_n with 1/2(1+iE_n) the nontrivial zeta zeros; self-adjointness with respect to a suitable metric would imply RH. Subsequent analysis (Bellissard's comment arXiv:1704.02644, 2017) showed the construction is not rigorous (domain/boundary-condition problems), and 2025-2026 work (Liu, Soochow University) showed that in the metric completion of the candidate inner-product space the eigenfunctions for n > 0 do not belong to the completed space, breaking the boundary-condition mechanism.
- status: heuristic/program; the specific self-adjointness route is refuted in the proposed metric completion | Carl Bender, Dorje Brody, Markus Muller; criticisms by Jean Bellissard et al., Kejun Liu (2017)
- citation: Phys. Rev. Lett. 118, 130201 (2017); arXiv:1608.03679; comment arXiv:1704.02644
- checked against: https://arxiv.org/abs/1608.03679 and search results including https://arxiv.org/pdf/1704.02644 and https://quantumzeitgeist.com/soochow-university-hilbertpolya-missing-eigenstates-bbm/
- technique: PT-symmetric quantum mechanics, biorthogonal systems, formal similarity transforms of the Berry-Keating operator
- bottleneck: no Hilbert space has been exhibited on which H is self-adjoint AND the eigenfunctions are elements; every candidate metric either loses the eigenfunctions or loses positivity
- tunable: choice of metric operator, boundary condition parameter
- gap: a clean published no-go theorem (for a natural class of metrics) does not exist; the lab-relevant lesson is that this family is a source of negative results rather than open constants

### Sierra program: xp variants and Dirac fermions in Rindler spacetime
- statement: A sequence of models refining Berry-Keating: H = x(p + l_p^2/p) reproduces the smooth (average) zero counting N(T) ~ (T/2pi)(log(T/2pi) - 1) semiclassically; a massless Dirac fermion in Rindler spacetime with delta-function potentials at the square-free integers (or moving mirrors with prime-related accelerations) admits a self-adjoint extension tuned to the phase theta(t) of zeta such that bound states sit at the Riemann zeros. The tuning inputs the zeta function's phase, so the construction realizes rather than predicts the zeros; no unconditional spectral theorem results.
- status: heuristic (physicist's models); the self-adjoint extensions are rigorous but the zero-realization requires inserting zeta data by hand | German Sierra, with Paul Townsend, Javier Rodriguez-Laguna, J. Mateos Guilarte et al. (2016)
- citation: review arXiv:1601.01797 ('The Riemann zeros as spectrum and the Riemann hypothesis', Symmetry 11 (2019) 494); J. Phys. A 47 (2014) 325204
- checked against: https://arxiv.org/pdf/1601.01797 and https://iopscience.iop.org/article/10.1088/1751-8113/47/32/325204 (search-level)
- technique: self-adjoint extensions, Rindler geometry, semiclassical quantization, moving mirrors
- bottleneck: circularity: the boundary condition that produces the zeros is defined using the zeta phase, so nothing is gained toward RH; removing the hand-tuning is the unsolved step
- tunable: boundary phase, potential strengths at square-free integers, mass/acceleration parameters
- gap: no one has quantified how the spectrum degrades when the boundary phase is perturbed away from theta(t): a measured sensitivity would say how much information the geometry itself carries versus the inserted phase

### Yang-Yang / statistical-mechanics realizations (LeClair, Mussardo)
- statement: The Riemann zeros arise as quantized energies of a relativistic scattering theory with impurities (LeClair-Mussardo, arXiv:2307.01254, JHEP 2023), via Bethe-ansatz-type quantization conditions built on the argument of zeta; LeClair's 'Spectral Flow for the Riemann zeros' (arXiv:2406.01828, Adv. Theor. Math. Phys., v3 2025-03-12) constructs a vector field from an entire function arising in the quantum statistical mechanics of relativistic gases (built from Gamma and zeta) and studies random-matrix statistics off the critical line. These give exact transcendental equations for zeros (in the spirit of the earlier LeClair-Franca equations) whose solvability for all n is equivalent to nontrivial statements about S(T), not proven.
- status: heuristic plus numerical; the underlying transcendental-equation counting statements are conjectural (equivalent to delta-type bounds on S(T)) | Andre LeClair, Giuseppe Mussardo (2024)
- citation: arXiv:2307.01254 (JHEP); arXiv:2406.01828 (Adv. Theor. Math. Phys. 2025)
- checked against: https://arxiv.org/abs/2406.01828 and https://arxiv.org/abs/2307.01254 (search-level)
- technique: Bethe ansatz / Yang-Yang thermodynamics, transcendental quantization conditions, spectral flow of vector fields
- bottleneck: the quantization condition's unique-solution property for every n is equivalent to a regularity statement about arg zeta on the critical line that is as open as ever
- tunable: impurity parameters, flow parameter (real part sigma), ensemble of zeros used
- gap: the spectral-flow picture off the critical line makes statistical predictions (random-matrix statistics off-line) that are numerically checkable against the lab's unfolding/GUE machinery and have not been independently tested

### Mayer transfer operator: Selberg zeta as a Fredholm determinant (theorem), with 2025 Holder extension
- statement: For PSL(2,Z), the Selberg zeta function satisfies Z(s) = det(1 - L_s) * det(1 + L_s), where L_s is the Mayer transfer operator of the Gauss continued-fraction map acting on a Banach space of holomorphic functions on a disc (Mayer 1991, reproved by Lewis-Zagier via period functions, Ann. of Math. 153 (2001) 191-258); eigenfunctions with eigenvalue 1 correspond to Maass forms and, through the scattering determinant, the Riemann zeta enters via zeta(2s). Baumgartner (arXiv:2511.06513, Nov 2025) extends the Ruelle-Mayer transfer operator to Holder continuous weight classes and shows the spectral data corresponding to Maass cusp forms and nontrivial zeta zeros persists.
- status: unconditional theorems (Mayer, Lewis-Zagier); the 2025 extension is a new unconditional structural result; no route from this to zero location is known | Dieter Mayer; John Lewis, Don Zagier; Alexander Baumgartner (2025)
- citation: arXiv:1008.4229 (survey of Mayer's theorem); Lewis-Zagier, Ann. of Math. 153 (2001); arXiv:2511.06513
- checked against: https://arxiv.org/abs/1008.4229 and https://arxiv.org/pdf/2511.06513 (search-level)
- technique: thermodynamic formalism, nuclear operators of order zero, period functions, three-term functional equation
- bottleneck: the transfer operator sees zeta only through zeta(2s) in the scattering/Eisenstein part; the critical line of zeta corresponds to Re(s) = 1/4 in the operator variable, and no positivity or self-adjointness structure is known there
- tunable: weight/observable class of the transfer operator, disc of holomorphy, truncation dimension of the matrix representation (known in terms of zeta and Gamma values)
- gap: high-precision computation of L_s spectra near Re(s)=1/4 to locate the zeta-induced spectral parameters is feasible and rarely done; the Holder-class extension opens new weight choices (an optimization variable) that nobody has tuned for conditioning

### Alcantara-Bode equivalence: RH iff injectivity of a Hilbert-Schmidt operator
- statement: RH holds if and only if the Hilbert-Schmidt integral operator A on L^2(0,1) with kernel A f(x) = integral_0^1 {y/x} f(y) dy (fractional part) is injective (Alcantara-Bode 1993, derived from the Beurling-Nyman criterion). The operator is compact, non-self-adjoint, with explicitly computable matrix elements; injectivity is equivalent to the statement that the closed span of {rho_theta(x) = {theta/x} : 0 < theta <= 1} together with the constant is dense, per Beurling-Nyman. Recent papers (2021-2025) propose numerical injectivity criteria via decay rates of inverse condition numbers o(n^{-s}) on approximating subspaces, none accepted as a proof.
- status: unconditional equivalence theorem (1993); the injectivity itself is open; recent numerical-injectivity programs are heuristic | Julio Alcantara-Bode (after Beurling, Nyman) (1993)
- citation: J. Alcantara-Bode, 'An integral formulation of the Riemann hypothesis', Integral Equations Operator Theory 17 (1993) 151-168
- checked against: memory-unverified for the exact 1993 journal reference; existence and statement confirmed via https://www.researchgate.net/publication/385983954_On_the_Method_for_Proving_the_RH_using_the_Alcantara-Bode_Equivalence and https://arxiv.org/pdf/math/0011254 (search-level)
- technique: Beurling-Nyman real-variable reformulation, Hilbert-Schmidt operators, Muntz-type approximation
- bottleneck: injectivity of a compact operator is a statement about the infinite tail of its singular values; any finite computation only bounds the finite section, and the passage to the limit is exactly RH
- tunable: approximation subspace family (simple functions, Muntz systems), section size n, weighting
- gap: enclosure-checked (interval-arithmetic) smallest singular values of the n x n finite sections have apparently never been published; their decay law sigma_min(n) vs n is a concrete measurable object that would calibrate all claimed numerical-injectivity arguments; the Hilbert-Schmidt norm of A is an exact constant computable in closed form and is a clean small formalization target

### de Branges / canonical-system route: Weil-distribution Hilbert space is a de Branges space
- statement: Under RH (and simplicity assumptions where stated), the Hilbert space obtained by completing C_c^infinity(R) with respect to the hermitian form derived from the Weil distribution is isomorphic, via composition with the Fourier transform, to a de Branges space of entire functions; this yields new equivalence conditions for RH (Suzuki). Companion work ('Weil's quadratic form via the screw function', arXiv:2606.09096, June 2026) re-expresses the Weil quadratic form through a continuous screw function in Krein's sense, replacing distributional pairings by integrals against a continuous function. Background: Lagarias (2006) proved RH holds iff E = A - iB built from xi is a Hermite-Biehler function.
- status: RH-conditional structure theorems (Suzuki); the screw-function reformulation is unconditional as a formula; Lagarias's Hermite-Biehler criterion is an unconditional equivalence | Masatoshi Suzuki; Jeffrey Lagarias (2025)
- citation: arXiv:2301.00421 (v3, 2025-11-07; Canad. J. Math., doi:10.4153/S0008414X25101739); arXiv:2606.09096; Lagarias, 'Hilbert spaces of entire functions and the Riemann zeta function' (2006)
- checked against: https://arxiv.org/abs/2301.00421; https://arxiv.org/abs/2606.09096 (search-level)
- technique: de Branges spaces, canonical systems, Krein screw functions, Hermite-Biehler class
- bottleneck: the canonical system whose Hamiltonian would generate xi is only known to exist conditionally; recovering its Hamiltonian H(t) explicitly (the inverse spectral problem) is the wall
- tunable: screw-function truncation, test measures in Krein's representation, canonical-system discretization
- gap: the screw-function formulation (2026) is new and gives a continuous, numerically tabulatable object g(t) whose positivity properties encode Weil positivity; nobody has published plots, monotonicity data, or truncated-positivity tests of the zeta screw function yet

### Suo's modular-form Hamiltonian with E_n = rho_n(1 - rho_n)
- statement: A Hamiltonian generalizing the Berry-Keating paradigm is constructed with formal eigenenergies E_n = rho_n(1 - rho_n), rho_n the n-th nontrivial zero, with number-theoretic input entering through modular forms; the paper states explicitly that it does not resolve Hilbert-Polya because the corresponding eigenstates are not normalizable. Published in Physical Review A 112 (2025).
- status: heuristic (published physics construction; non-normalizable eigenstates, no self-adjointness claim) | Xingpao Suo (2025)
- citation: arXiv:2505.21192 (v. 2025-12-25); Phys. Rev. A 112 (2025)
- checked against: https://arxiv.org/abs/2505.21192
- technique: Berry-Keating generalization; modular forms as potential data; rho(1-rho) spectral variable (which is real iff the zero is on the critical line or real)
- bottleneck: non-normalizable eigenstates mean the 'spectrum' is not a spectrum; making the states normalizable without destroying the eigenvalue identification is the same rigged-Hilbert-space obstruction as in all xp descendants
- tunable: choice of modular form, regularization of the eigenstates
- gap: the rho(1-rho) variable is the natural one for comparison with Connes-Moscovici's negative prolate eigenvalues (squares of zeros): a numerical dictionary between the two spectra has not been attempted


## Territory G: geometry of the Riemann xi function ,  de Bruijn-Newman flow, Jensen polynomial hyperbolicity, Laguerre-Polya class, higher-order Turan inequalities, zeros of xi^(n), Polya-type universality under differentiation, heat-flow zero dynamics

### Newman's conjecture: de Bruijn-Newman constant is non-negative
- statement: Let H_t(z) = integral of e^{tu^2} Phi(u) cos(zu) du with H_0 = (1/8) Xi(z/2). There exists Lambda (de Bruijn-Newman constant) such that H_t has all real zeros iff t >= Lambda; RH is equivalent to Lambda <= 0. Theorem (Rodgers-Tao): Lambda >= 0. Hence RH, if true, is equivalent to Lambda = 0.
- constant: Lambda >= 0 (exactly; previous best lower bound was Lambda > -1.15e-11, Saouter-Gourdon-Demichel 2011)
- status: unconditional | Brad Rodgers, Terence Tao (2020)
- citation: arXiv:1801.05914; Forum of Mathematics, Pi 8 (2020) e6
- checked against: https://arxiv.org/abs/1801.05914 and https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/de-bruijnnewman-constant-is-nonnegative/D4B85BA067E2D5A71D87E4FFB0D21E46
- technique: Contradiction from Lambda < 0: backward heat-flow dynamics of zeros (Csordas-Smith-Varga ODE system) forces zeros of H_0 into an over-rigid locally-equidistributed configuration incompatible with Montgomery pair-correlation-type estimates for zeta zeros.
- bottleneck: The result is sharp in the only improvable direction (Lambda > 0 would disprove RH), so the frontier moved to the upper bound and to quantitative versions of the relaxation mechanism.
- tunable: test functions in the pair-correlation input; time-window and mesoscopic scale parameters in the dynamics argument
- gap: Quantitative relaxation-to-equilibrium rates for the zero dynamics of H_t (t in (0, Lambda_upper)) are not pinned down; effective versions of the rigidity dichotomy remain unexplored numerically.

### Polymath15 upper bound for the de Bruijn-Newman constant
- statement: Unconditionally Lambda <= 0.22. Conditionally on the numerical verification of RH to height 3x10^12 (Platt-Trudgian, arXiv:2004.09765), the same pipeline yields Lambda <= 0.20 (stated on the Polymath wiki, not formally published). Method: prove H_t is zero-free in an explicit barrier region plus an effective A+B/B_0 approximation showing no zeros above the barrier for t = 0.22.
- constant: Lambda <= 0.22 unconditional; Lambda <= 0.2 modulo RH verified to 3x10^12 (wiki-level, unpublished)
- status: unconditional (0.22); numerical-verification-conditional (0.20) | D.H.J. Polymath (Polymath15 project, moderated by T. Tao) (2019)
- citation: arXiv:1904.12438; Research in the Mathematical Sciences 6 (2019)
- checked against: https://arxiv.org/abs/1904.12438 and https://michaelnielsen.org/polymath/index.php?title=De_Bruijn-Newman_constant
- technique: Effective error bounds for a Riemann-Siegel-type approximation of H_t; interval-arithmetic verification of a zero-free barrier; explicit control of zero motion under the heat flow.
- bottleneck: Cost of the barrier computation scales with the RH-verification height; each halving of the bound requires exponentially higher verified height (getting to 0.1 was estimated to need an enormous distributed computation).
- tunable: barrier location x_0, time t_0, mesh resolution, choice of effective approximant (A+B vs A+B-C), Euler-product tail parameters
- gap: The 0.20 improvement enabled by Platt-Trudgian 2020 was never formally written up or pushed further; the public code (github.com/km-git-acc/dbn_upper_bound) has not been rerun with post-2020 heights or with re-optimized barrier placement/mesh.

### Ki-Kim-Lee: Lambda < 1/2 and finiteness of non-real zeros for t > 0
- statement: Lambda < 1/2 (strict improvement of de Bruijn's 1950 bound Lambda <= 1/2). Moreover for every t > 0, H_t has at most finitely many non-real zeros, and all but finitely many zeros of H_t are real and simple.
- constant: Lambda < 1/2 (no explicit numerical gap below 1/2 given)
- status: unconditional | Haseo Ki, Young-One Kim, Jungseob Lee (2009)
- citation: Advances in Mathematics 222 (2009) 281-306, 'On the de Bruijn-Newman constant'
- checked against: https://michaelnielsen.org/polymath/index.php?title=De_Bruijn-Newman_constant (attribution and statement); https://www.sciencedirect.com/science/article/pii/S0001870809001133
- technique: Saddle point analysis of the integral representation of H_t; classical entire-function theory (Laguerre-Polya class stability under the backward heat operator).
- bottleneck: The qualitative 'finitely many non-real zeros' has no effective bound on the count or the height containing them, for given t > 0.
- tunable: saddle-point contour choices; effective constants in the asymptotic expansion of H_t
- gap: An explicit function N(t) bounding the number (or maximal height) of non-real zeros of H_t for each t in (0, 0.22) has never been extracted; Polymath15 methods make this finitely checkable for specific t.

### Dobner: Newman's conjecture for the extended Selberg class
- statement: Every L-function in the extended Selberg class has an associated de Bruijn-Newman constant Lambda_L, and Lambda_L >= 0 for all of them. The proof avoids all information about zeros of the underlying L-function (unlike Rodgers-Tao, which needs pair-correlation input).
- status: unconditional | Alexander Dobner (2020)
- citation: arXiv:2005.05142, 'A New Proof of Newman's Conjecture and a Generalization'
- checked against: https://arxiv.org/abs/2005.05142
- technique: Direct construction: exploits the Euler-product/Dirichlet-series structure to build test points where reality of zeros fails for t < 0, bypassing zero-dynamics entirely.
- bottleneck: Method gives non-negativity only; it does not localize where non-real zeros of H_t appear for t < 0, so it contributes nothing to upper bounds.
- tunable: choice of test points / Dirichlet coefficients exploited in the construction
- gap: Quantitative version (how fast do non-real zeros appear as t decreases through 0, for a given L-function) is untouched; comparison of Dobner vs Rodgers-Tao mechanisms on Davenport-Heilbronn-type functions (which are in the extended class and violate RH) is unexplored numerically.

### Griffin-Ono-Rolen-Zagier: eventual hyperbolicity of all Jensen polynomials of xi
- statement: Let J^{d,n}(X) be the degree-d Jensen polynomial attached to the Taylor coefficients gamma(n) of (-1+4z^2) Lambda(1/2+z) = sum gamma(n) z^{2n}/n! (8 xi normalization). Polya (1927): RH is equivalent to hyperbolicity of J^{d,n} for all d, n >= 0. Theorem: for each fixed d >= 1, J^{d,n}(X) is hyperbolic for all sufficiently large n; moreover suitably renormalized J^{d,n} converge uniformly to the Hermite polynomial H_d(X), and this Hermite universality holds for a large class of sequences (settling the Chen-Jia-Wang conjecture for partitions).
- status: unconditional | Michael Griffin, Ken Ono, Larry Rolen, Don Zagier (2019)
- citation: arXiv:1902.07321; PNAS 116 (2019) 11103-11110
- checked against: https://arxiv.org/abs/1902.07321
- technique: Asymptotics of the derivative sequence gamma(n) (via theta-integral moments) feeding a general Hermite-approximation lemma for Jensen polynomials of admissible sequences.
- bottleneck: Fixed-d hyperbolicity for large n is exponentially far from RH (RH needs all d simultaneously; Farmer 2020 argues the d-aspect is the whole difficulty).
- tunable: renormalization sequences A(n), delta(n); admissible-growth class definition; choice of expansion basis (Hermite vs Meixner-Pollaczek per Romik)
- gap: Rates: uniformity in d of the Hermite approximation is poor (n >> e^{d/2} in the effective version); closing the d-uniformity gap is the entire remaining problem.

### Griffin-Ono-Rolen-Thorner-Tripp-Wagner: effective hyperbolicity, d <= 9.36x10^20
- statement: Theorem 1.1: there is c > 0 with J^{d,n}(X) hyperbolic for all d >= 1 and n >= c e^{d/2}. Theorem 1.2: let RH_m(T) assert every zero rho of xi^{(m)}(s) with |Im rho| <= T has Re rho = 1/2; if RH_m(T) holds and d <= floor(T)^2, then J^{d,n}(X) is hyperbolic for all n >= m. Corollary 1.3: since RH_0(3.06x10^10) is known (Platt 2017), J^{d,n} is hyperbolic for all n >= 0 whenever d <= 9.36x10^20.
- constant: d <= 9.36x10^20 (all n >= 0); threshold n >= c e^{d/2} with c effective but astronomically applied
- status: unconditional (Corollary 1.3 rests on a rigorous computation) | Michael Griffin, Ken Ono, Larry Rolen, Jesse Thorner, Zachary Tripp, Ian Wagner (2022)
- citation: arXiv:1910.01227; Advances in Mathematics 397 (2022), Paper 108186
- checked against: https://ar5iv.labs.arxiv.org/html/1910.01227 (exact theorem statements extracted)
- technique: Low-lying zeros of the derivatives xi^{(n)}(s) control hyperbolicity of J^{d,n}; partial RH verification for xi^{(m)} to height T buys degree d <= floor(T)^2 wholesale.
- bottleneck: e^{d/2} growth in the unconditional threshold; the conditional route needs enclosure-checked zero verification for derivatives of xi, which nobody has produced.
- tunable: verification height T per derivative order m; the exponent in d <= floor(T)^2 (is T^2 optimal?); effective constant c
- gap: Corollary 1.3 (arXiv v3, Dec 2020) still uses Platt's 3.06x10^10; inserting Platt-Trudgian's 3x10^12 (arXiv:2004.09765) immediately gives d <= 9x10^24, an unharvested free update. More substantively: RH_m(T) for m >= 1 (zeros of xi', xi'' verified to height T) has apparently never been rigorously computed, so the m >= 1 arm of Theorem 1.2 has never been fed.

### Farmer's critique: Jensen polynomials are not a plausible route to RH
- statement: The Hermite universality of GORZ is a 'new type of universal law' but carries no information about RH: hyperbolicity of J^{d,n} for fixed d and large n concerns only a bounded region of the critical strip, and the suggested connections to GUE statistics are unjustified. Farmer proposes criteria for when an RH-equivalence is useful (roughly: it must not become trivially true 'in the limit' for reasons disjoint from RH).
- status: heuristic | David W. Farmer (2020)
- citation: arXiv:2008.07206
- checked against: https://arxiv.org/abs/2008.07206
- technique: Analysis of what fixed-degree hyperbolicity actually constrains about zero locations; comparison with functions violating RH that satisfy the same asymptotic laws.
- bottleneck: Not a theorem but a decisive framing constraint: any Territory-G project claiming RH-relevance must survive the Farmer criteria and the Davenport-Heilbronn battery.
- gap: Farmer's criteria have not been systematically run against the newer bases (Romik's Meixner-Pollaczek / continuous Hahn expansions), where Romik conjectures more natural structure; whether those expansions also satisfy an RH-independent universal law is open and testable.

### Unconditional Turan (d=2) and higher-order Turan (d=3) inequalities for xi
- statement: Write 8 xi(1/2 + sqrt(z))-style moment coefficients b_n (Csordas-Norfolk-Varga normalization). Csordas-Norfolk-Varga (1986): the Turan inequalities b_n^2 - b_{n-1} b_{n+1} >= 0 hold for all n >= 1 (equivalently J^{2,n} hyperbolic for all n). Dimitrov-Lucas (2011): the higher-order (cubic) Turan inequalities 4(b_n^2 - b_{n-1}b_{n+1})(b_{n+1}^2 - b_n b_{n+2}) - (b_n b_{n+1} - b_{n-1}b_{n+2})^2 >= 0 hold for all n >= 1, unconditionally (equivalently J^{3,n} hyperbolic for all n). These are the only two degrees with purely analytic (computation-free) proofs for all n.
- status: unconditional | George Csordas, Timothy Norfolk, Richard Varga (d=2); Dimitar Dimitrov, Fabio Lucas (d=3) (2011)
- citation: Trans. AMS 296 (1986) 521-541; Proc. AMS 139 (2011) 1013-1022, 'Higher order Turan inequalities for the Riemann xi-function'
- checked against: https://bv.fapesp.br/en/publicacao/29040/higher-order-turan-inequalities-for-the-riemann-xi-function (search-level confirmation of Dimitrov-Lucas statement); details memory-unverified
- technique: Explicit integral inequalities for the moments of the kernel Phi(t) (log-concavity plus refined convexity estimates of Phi).
- bottleneck: The kernel-moment method has not been pushed past d=3; each degree requires a bespoke sharp inequality for Phi.
- tunable: auxiliary kernel inequalities for Phi; SOS certificates for polynomial inequalities in the moment ratios
- gap: No analytic proof of J^{4,n} hyperbolicity for all n exists (only the computation-backed d <= 9.36x10^20 result). Whether the Dimitrov-Lucas approach extends to d=4 with modern computer-assisted inequality certification (SOS / interval methods on Phi's moment quotients) is open.

### Conrey 1983: proportions of zeros of xi^(m) on the critical line, and simple
- statement: Let alpha_m be the proportion of zeros of xi^{(m)}(s) with Re = 1/2, and beta_m the proportion on Re = 1/2 that are simple. Paper I: alpha_1 >= 0.8137 and alpha_m = 1 + O(m^{-2}) as m -> infinity. Paper II theorem: beta_m > 1 - log F_m(R) / R for any R > 0, with F_m built from phi(x) = 1 - x; Corollary 1: beta_0 > 0.3485, beta_1 > 0.7869, beta_2 > 0.9314, beta_3 > 0.9666, beta_4 > 0.9799, beta_5 > 0.9863, and beta_m = 1 + O(m^{-2}). Corollary 2: the proportion delta_m of zeta zeros of multiplicity > m satisfies delta_m < 1/m^2 (from the simple-zero counts).
- constant: alpha_1 >= 0.8137; beta_1 > 0.7869; beta_2 > 0.9314; beta_3 > 0.9666; beta_4 > 0.9799; beta_5 > 0.9863
- status: unconditional | J. Brian Conrey (1983)
- citation: J. Number Theory 16 (1983) 49-74 (I) and J. Number Theory 17 (1983) 71-75 (II)
- checked against: https://aimath.org/~kaur/publications/4.pdf (PDF fetched; theorem, corollaries and exact decimals extracted from the text streams)
- technique: Levinson's method applied to xi^{(m)} via a new identity expressing xi^{(m)}(1/2+it) through G_m(s); mollified mean values with the linear mollifier phi(x) = 1 - x and one free parameter R.
- bottleneck: The entire 40-year-old machinery uses Levinson's original mollifier phi(x) = 1-x and short mollifier length; none of the modern mollifier technology (Conrey 1989 theta=4/7, Bui-Conrey-Young, Pratt-Robles-Zaharescu-Zeindler multi-piece mollifiers, 2025 short-mollifier derivative combinations) has ever been transplanted back into the xi^{(m)} problem.
- tunable: mollifier polynomial phi (coefficients), mollifier length theta, parameter R, linear combinations of derivatives in the detector
- gap: alpha_1 and all beta_m are almost certainly improvable by several points with a modern mollifier; the optimization is a well-posed quadratic-form problem the literature has left unharvested since 1983.

### Campbell-O'Rourke-Renfrew: Cosine and Hermite universality under repeated differentiation
- statement: For a class of even entire functions, real on the real line, with only real zeros (containing the rescalings relevant to Xi under RH), the zeros of the n-th derivative, suitably rescaled, converge to an arithmetic progression (zeros of cosine) as n -> infinity: this proves the Cosine Universality conjecture of Farmer-Rhoades (2005). They also prove Hermite universality and finite-free-probability analogues of the LLN, CLT and Poisson limit theorem for deterministic polynomial sequences.
- status: unconditional for the stated class; application to Xi itself is RH-conditional (needs all-real zeros) | Andrew Campbell, Sean O'Rourke, David Renfrew (2024)
- citation: arXiv:2410.06403
- checked against: https://arxiv.org/abs/2410.06403
- technique: Finite free probability: repeated differentiation as finite free convolution powers; free-probabilistic limit theorems transferred to root distributions.
- bottleneck: The real-rootedness hypothesis: for Xi unconditionally one only knows a proportion >= 2/3 of zeros on the line, and the finite-free machinery has no version tolerating a sparse set of non-real zeros.
- tunable: rescaling windows; coupling between differentiation count n and height T
- gap: Unconditional cosine universality for Xi^{(n)} (using Ki-Kim-Lee-type 'finitely many non-real zeros after smoothing' or Conrey's alpha_m -> 1) is open; quantitative convergence rates (in n, at fixed height) are not established; behavior for the Davenport-Heilbronn function (real coefficients, off-line zeros) is untested.

### Michalowski 2026: de Bruijn-Newman kernel is not a Polya frequency function of order 5
- statement: The kernel K(u) = Phi(|u|) (Phi the super-exponentially decaying heat kernel with H_0(z) = integral Phi(u) cos(zu) du) is not PF_5: at (u_0, h) = (0.01, 0.05) an explicit 5x5 Toeplitz minor has determinant rigorously enclosed in [-1.8472496e-9, -1.8472225e-9]. The minors D_2, D_3, D_4 are positive at that configuration; global PF_4 status is left open. Version 2 withdrew v1's asymptotic-threshold claims because of unsound derivative-tail enclosures; the central counterexample stands.
- constant: 5x5 Toeplitz minor determinant in [-1.8472496e-9, -1.8472225e-9] at (u_0,h)=(0.01,0.05)
- status: numerical (enclosure-checked interval computation) | Wojciech Michalowski (2026)
- citation: arXiv:2602.20313 (v2)
- checked against: https://arxiv.org/abs/2602.20313 and https://arxiv.org/html/2602.20313v2
- technique: 80-digit outward-rounded interval arithmetic with proved truncation bounds for theta series; independent cross-check via explicit Leibniz expansions of the minors.
- bottleneck: The withdrawn v1 asymptotics mean the field currently lacks any correct account of where PF_k fails as a function of (u_0, h, k); only one enclosure-checked point exists.
- tunable: configuration (u_0, h), minor order k, node placement in the Toeplitz matrix, theta-series truncation depth
- gap: Global PF_4 status of K is explicitly open; the 'Toeplitz threshold phenomenon' (v1) is unproven; nobody has mapped the sign of D_4 and D_5 minors over the (u_0, h) plane with enclosure-checked arithmetic. This is a fresh (Feb 2026) surface with essentially one paper on it.

### Romik: orthogonal polynomial expansions of Xi
- statement: Expansions of Xi(t) in three bases: Hermite polynomials (Turan's program), symmetric Meixner-Pollaczek polynomials P_n^{(3/4)}(x; pi/2), and continuous Hahn polynomials p_n(x; 3/4, 3/4, 3/4, 3/4). In each basis the coefficients alternate in sign, and Romik proves asymptotic formulas for them, plus a new asymptotic formula for the Taylor coefficients of xi. He argues the Meixner-Pollaczek and Hahn expansions may be more natural than Hermite for approaching RH.
- status: unconditional | Dan Romik (2019)
- citation: arXiv:1902.06330; Acta Arithmetica (published version)
- checked against: https://arxiv.org/abs/1902.06330
- technique: Mellin/theta manipulations of the Phi kernel; classical orthogonal polynomial asymptotics; saddle point analysis.
- bottleneck: No hyperbolicity/Turan theory has been developed in the new bases: the analogue of the Jensen-Polya criterion for Meixner-Pollaczek or Hahn coefficient sequences is not even formulated precisely in the literature.
- tunable: choice of orthogonality parameters (the 3/4's), which coefficient functionals to test, degree/shift ranges
- gap: Whether Turan-type or higher-order inequalities hold for Romik's Meixner-Pollaczek/Hahn coefficients (and whether they are RH-discriminating, i.e. fail for Davenport-Heilbronn) is open and finitely testable.

### Platt-Trudgian: RH verified to height 3x10^12
- statement: All non-trivial zeros rho of zeta with 0 < Im rho <= 3x10^12 satisfy Re rho = 1/2; verified rigorously using interval arithmetic (12,363,153,437,138 zeros). This is the current rigorous input feeding both the conditional Lambda <= 0.20 and the Jensen degree bound d <= floor(3x10^12)^2 = 9x10^24.
- constant: T = 3x10^12 (rigorous; Gourdon-Demichel's 10^13 is not interval-enclosure-checked)
- status: numerical (rigorous interval arithmetic) | Dave Platt, Tim Trudgian (2021)
- citation: arXiv:2004.09765; Bull. LMS 53 (2021) 792-797
- checked against: https://arxiv.org/abs/2004.09765
- technique: Turing's method with enclosure-checked evaluation of Z(t) via interval arithmetic.
- bottleneck: Compute cost; and crucially no analogous rigorous verification exists for zeros of xi' or higher derivatives (RH_m(T), m >= 1).
- tunable: height T, derivative order m, verification algorithm (Turing method adapted to Xi^{(m)})
- gap: RH_1(T) for any nontrivial T is absent from the literature; even T ~ 10^6 would be new and would activate the n >= 1 arm of GORTTW Theorem 1.2.

### O'Sullivan: Hermite-combination criterion and sharp asymptotics for xi Taylor coefficients
- statement: A reformulation of Polya's Jensen-polynomial criterion for RH using linear combinations of Hermite polynomials, shown to hold 'in many cases'; plus detailed asymptotic expansions (to arbitrary order) for the Taylor coefficients of xi at 1/2 and related quantities, sharpening the asymptotics underlying Griffin-Ono-Rolen-Zagier.
- status: unconditional | Cormac O'Sullivan (2021)
- citation: arXiv:2007.13582; Research in the Mathematical Sciences 8 (2021)
- checked against: https://arxiv.org/abs/2007.13582
- technique: Saddle-point asymptotic expansions of the theta-kernel moments; Hermite polynomial recombination of the Jensen criterion.
- bottleneck: Same d-uniformity wall as GORZ; the improved asymptotics have not been fed back into the effective threshold n >= c e^{d/2} to shrink c or the exponent.
- tunable: order of asymptotic expansion; Hermite combination coefficients
- gap: Recomputing the GORTTW effective constant c using O'Sullivan's higher-order expansions is an unharvested improvement; nobody has checked how far the 'many cases' of the new criterion extend computationally.

### Heat-flow and finite-free differentiation dynamics (2024-2026 activity)
- statement: Active adjacent work: Hall-Ho 'heat flow conjecture' for polynomials and random matrices (Lett. Math. Phys. 115 (2025) 60); Hall-Ho-Jalowy-Kabluchko on roots under repeated differentiation and fractional differential operators (arXiv:2312.14883); 'The Rectangular Finite Free Heat Flow' (arXiv:2606.06859, June 2026); 'Zeros of polynomial powers under the heat flow' (arXiv:2512.17808, Dec 2025); Galligo-Najnudel-Vu on rotationally invariant root sets under iterated differentiation (arXiv:2506.06263, 2025). Collectively: heat flow and differentiation act as free convolution semigroups on root measures, with universal local limits.
- status: unconditional (for polynomial/random-matrix models) | Brian Hall, Ching-Wei Ho, Jonas Jalowy, Zakhar Kabluchko, Andre Galligo, Joseph Najnudel, Truong Vu, and others (2026)
- citation: arXiv:2312.14883; arXiv:2512.17808; arXiv:2606.06859; Lett. Math. Phys. 115 (2025) 60
- checked against: https://arxiv.org/pdf/2512.17808 and https://arxiv.org/pdf/2606.06859 (titles/abstract-level); Hall-Ho citation memory-unverified in detail
- technique: Finite free probability, free convolution semigroups, PDE for log-potential of root measures.
- bottleneck: All results are for polynomials or random models; transfer to the single deterministic transcendental object Xi (order-1 entire, log-concave kernel) is not done, and the H_t flow on Xi zeros is exactly the t-parametrized version these papers study abstractly.
- tunable: flow time t, height window, rescaling; choice of free-probability observable (Cauchy transform vs spacings)
- gap: A dictionary between the Polymath15 effective H_t dynamics and the finite-free heat flow limit theorems has not been written; measured spacing statistics of H_t zeros for t in (0, 0.2] against the free-convolution prediction is an open numerical test.


## Territory H: explicit and computer-assisted results ,  RH verification height records, explicit prime-counting inequalities (psi, theta, pi), explicit zero-free regions and zero-density estimates feeding them, Turing-method/argument bounds, explicit critical-line subconvexity, Mertens-function bounds, partial-RH transfer theorems, and Skewes-region computations. State of the art as of August 2026.

### RH verification height record
- statement: All 12,363,153,437,138 nontrivial zeros beta+i*gamma of zeta with 0 < gamma <= 3,000,175,332,800 (i.e. height 3*10^12) have beta = 1/2, verified rigorously with interval arithmetic (isolated via Turing's method). This independently confirms and exceeds by 22% the non-rigorous Gourdon-Demichel 10^13-zeros computation's rigorous predecessors (Wedeniwski, Franke et al.).
- constant: T0 = 3,000,175,332,800; N = 12,363,153,437,138 zeros
- status: unconditional | David J. Platt, Timothy S. Trudgian (2021)
- citation: arXiv:2004.09765; Bull. LMS 53(3) (2021) 792-797
- checked against: https://arxiv.org/abs/2004.09765
- technique: Rigorous Riemann-Siegel/Booker-Platt band-limited zeta evaluation with interval arithmetic, Gram-point bracketing, Turing's method for completeness
- bottleneck: Pure compute cost scales roughly linearly in T with a t^{1/2}-ish per-evaluation cost; no one has funded/coordinated a rigorous push past 3e12 since 2020. Turing-method constants (now improved by Bellotti-Wong 2024) and per-point evaluation cost are the levers.
- tunable: Turing-method constants, band-limited interpolation parameters, interval evaluation precision schedule, gram-block partitioning
- gap: Six years old and unextended. Modern Arb + improved Turing constants + cheaper hardware make a rigorous extension (or an independent re-verification of a large-height window) a pure pipeline-optimization problem. Also: no kernel-checked formalization of the Turing criterion exists anywhere.

### Classical zero-free region record (March 2026)
- statement: zeta(sigma+it) != 0 whenever t >= 3 and sigma >= 1 - 1/(4.896 log t). Improves the Mossinghoff-Trudgian-Yang 2022/2024 constant 5.558691 by about 12%, adapting Heath-Brown's Linnik-constant machinery.
- constant: 1/(4.896 log t) for t >= 3; previous record 1/(5.558691 log t) for |t| >= 2 (MTY, arXiv:2212.06867)
- status: unconditional | Chiara Bellotti, Tim Trudgian, Andrew Yang (2026)
- citation: arXiv:2603.21490
- checked against: https://arxiv.org/abs/2603.21490
- technique: Heath-Brown-style trigonometric-polynomial / smoothed sum machinery made explicit, plus the RH verification height 3e12 for small t
- bottleneck: Choice of non-negative trigonometric polynomial and smoothing weights; every explicit prime-counting bound downstream (psi, theta, primes between powers, Mertens) was computed against the OLD 5.558691 constant and has not yet been re-propagated.
- tunable: Trigonometric polynomial coefficients, mollifier/smoothing kernel, split-point between classical and Korobov-Vinogradov regions
- gap: Five months old: essentially none of the downstream explicit literature (Fiori-Kadiri-Swidinsky psi bounds, Lee's kth-powers tables of Feb 2026, Lee-Leong Mertens constant) has been recomputed with 4.896. This is an unharvested propagation cascade.

### Korobov-Vinogradov explicit zero-free region
- statement: zeta has no zeros for sigma >= 1 - 1/(48.0718 (log|t|)^{2/3} (log log|t|)^{1/3}) asymptotically (Bellotti 2024, improving MTY's 55.241 and their asymptotic 48.1588); MTY 2022: no zeros for sigma >= 1 - 1/(55.241 (log|t|)^{2/3}(log log|t|)^{1/3}), |t| >= 3.
- constant: 48.0718 (Bellotti asymptotic); 55.241 explicit all |t|>=3 (MTY); nonexplicit benchmark 1/49.13 (Ford)
- status: unconditional | Chiara Bellotti; Michael J. Mossinghoff, Timothy S. Trudgian, Andrew Yang (2024)
- citation: Bellotti, 'Explicit bounds for the Riemann zeta function and a new zero-free region', J. Math. Anal. Appl. (2024), S0022247X24001719; MTY arXiv:2212.06867, Res. Number Theory (2024)
- checked against: https://www.sciencedirect.com/science/article/pii/S0022247X24001719 (located via search; constants cross-checked against search summaries)
- technique: Explicit Vinogradov integral / exponential-sum bounds (Ford-style) with careful explicit constants in the van der Corput ranges
- bottleneck: Explicit exponential-sum constants are far from Ford's asymptotic quality in the transition range exp(64) <= t <= exp(1000); the crossover ordinate where KV beats classical is astronomically large.
- tunable: Exponent pairs, Vinogradov mean-value parameter choices, range-splitting ordinates
- gap: The explicit KV region only bites for |t| > e^481958 in Bellotti's version; shrinking the ordinate where KV-type beats classical-type is wide open and is mostly a finite optimization over exponent-pair/van der Corput parameters.

### Sharpest unconditional psi(x) error bounds
- statement: For all x > 2: |psi(x) - x| < 9.22106 * x * (log x)^{3/2} * exp(-0.8476836 sqrt(log x)); and for log x >= 3000: |psi(x) - x| < 4.47e-15 * x. Refines Pintz's method as applied by Platt-Trudgian, splitting zeros into extra regions with heavy computation.
- constant: 9.22106, exponent constant 0.8476836; asymptotic-regime constant 4.47e-15 for log x >= 3000
- status: unconditional | Andrew Fiori, Habiba Kadiri, Joshua Swidinsky (2023)
- citation: arXiv:2204.02588; J. Math. Anal. Appl. 527 (2023)
- checked against: https://arxiv.org/abs/2204.02588 (constants from search-result summary of abstract)
- technique: Pintz-style zero-splitting: contributions partitioned by zero height and distance from the 1-line, each region estimated with the best available zero-free region + zero density + verified zeros to 3e12
- bottleneck: Inputs frozen at 2022 values: MTY 5.558691 classical region, KLN zero density, 3e12 verification height. Every input has since improved (BTY 4.896, Bellotti log-free density 2025, explicit Ingham 2025).
- tunable: Zero-region partition boundaries, per-region estimate choices, the smoothing parameter in Pintz's method, verification-height/zero-density trade-off
- gap: A straight re-run of the FKS optimization with the 2025-2026 inputs (4.896 zero-free region, Bellotti log-free zero density, Bellotti-Wong N(T)) should mechanically improve both constants; nobody has published it as of Aug 2026.

### PNT error terms for pi(x), theta(x), psi(x) (Johnston-Yang)
- statement: For all x >= 2: |psi(x) - x| <= 9.39 * x * (log x)^{1.515} * exp(-0.8274 sqrt(log x)), with analogous explicit bounds for |theta(x)-x| and |pi(x)-li(x)|; best known for large x in its era, relying on explicit zero-free regions and zero-density estimates.
- constant: 9.39, log-power 1.515, exponential constant 0.8274
- status: unconditional | Daniel R. Johnston, Andrew Yang (2023)
- citation: arXiv:2204.01980; J. Math. Anal. Appl. (2023)
- checked against: https://arxiv.org/abs/2204.01980
- technique: Combines Pintz zero-splitting with explicit zero-density (KLN) and the 3e12 verification, optimizing the interplay
- bottleneck: Same frozen 2022 inputs as FKS; also the (log x)^{1.515} power is an artifact of the density-estimate shape, itself improvable via Bellotti's log-free density
- tunable: Region split points, density-estimate selection per region, smoothing kernel
- gap: Re-optimization against 2025-2026 inputs unpublished; additionally the medium-x range (x between ~e^60 and e^3000) is governed by crude region-splitting that authors acknowledge is lossy

### All-range explicit theta(x) bounds
- statement: Explicit bounds |theta(x) - x| <= eps * x (tabulated eps by range) and |theta(x)-x| <= c_k * x/(log x)^k for k = 1..5 with full tables of c_k over all x-ranges; the standard reference tables used by essentially every explicit application since 2021.
- constant: Tabulated (e.g. c_1-type constants by range; exact values in ancillary tables, not a single closed form)
- status: unconditional | Samuel Broadbent, Habiba Kadiri, Allysa Lumley, Nathan Ng, Kirsten Wilk (2021)
- citation: arXiv:2002.11068 (41-page ancillary table file)
- checked against: https://arxiv.org/abs/2002.11068
- technique: Explicit formula with verified zeros to 3e12 + zero-free regions + smoothing, optimized per range
- bottleneck: Tables computed against 2020-era inputs; each improvement in zero-free region or verification height stales them
- tunable: Smoothing function per range, range endpoints, k-dependent trade-offs
- gap: A regenerated table set using BTY 4.896 and Bellotti densities would improve many entries; also the tables are exactly the kind of enclosure-checked-computation artifact that Arb enclosures could carry end-to-end (currently they are careful floats)

### Explicit zero-counting / argument bound (Turing-method backbone)
- statement: |N(T) - (T/(2*pi)) log(T/(2*pi*e))| <= 0.10076 log T + 0.24460 log log T + 8.08344 for all T >= e. Improves Hasanalizade-Shen-Wong; main gain from new subconvexity bounds for zeta(sigma_k + it) on interior lines.
- constant: 0.10076, 0.24460, 8.08344
- status: unconditional | Chiara Bellotti, Peng-Jie Wong (appendix by Andrew Fiori) (2025)
- citation: arXiv:2412.15470 (v2 July 2025)
- checked against: https://arxiv.org/abs/2412.15470
- technique: Backlund/Rosser argument-bound method with optimized convexity interpolation between explicit sigma-line bounds
- bottleneck: The sigma_k-line subconvexity constants; the Feb 2026 Revers improvement of the critical-line estimate postdates this paper and is not incorporated
- tunable: Choice of sigma_k lines, convexity interpolation weights, subconvexity constants fed in
- gap: Plugging Revers (arXiv:2602.05614) and Patel-Yang sub-Weyl (66.7 t^{27/164}) constants into the Bellotti-Wong optimization is an unharvested mechanical improvement; the leading constant 0.10076 directly tightens Turing's method for all future verification computations

### Explicit critical-line subconvexity records
- statement: van der Corput regime: |zeta(1/2+it)| <= 0.618 t^{1/6} log t class bounds (Hiary-Patel-Yang 2022/2024, correcting the flawed Kusmin-Landau constant used by earlier records), newly improved by Revers (Feb 2026) via a refined explicit van der Corput method plus computation. Sub-Weyl regime: |zeta(1/2+it)| <= 66.7 t^{27/164} for t >= 3, sharpest known for t >= exp(61) (Patel-Yang 2023). Note 27/164 = 0.16463... < 1/6.
- constant: 66.7 t^{27/164} (t >= 3, best for t >= e^61); HPY t^{1/6}-class constant improved again Feb 2026 (exact new constant in 2602.05614 full text)
- status: unconditional | Ghaith A. Hiary, Dhir Patel, Andrew Yang; Michael Revers (2026)
- citation: arXiv:2207.02366; arXiv:2302.13444; arXiv:2602.05614
- checked against: https://arxiv.org/abs/2302.13444 and https://arxiv.org/abs/2602.05614
- technique: Explicit van der Corput second/third derivative tests with corrected Kusmin-Landau lemma; explicit Bombieri-Iwaniec-style machinery for sub-Weyl
- bottleneck: Explicit exponent-pair constants; the crossover height e^61 where sub-Weyl wins is huge because the 66.7 prefactor is crude
- tunable: Exponent pairs, Farey-dissection parameters, prefactor vs range trade-offs
- gap: Lowering the sub-Weyl prefactor 66.7 (or the crossover e^61) is an explicit finite optimization; these bounds feed Bellotti-Wong N(T) and all zero-free regions, so gains cascade

### Partial-RH transfer theorems (verification height to conditional bounds)
- statement: Büthe: Schoenfeld's RH-conditional bounds, e.g. |pi(x) - li(x)| <= sqrt(x) log(x)/(8*pi) for 2657 < x, hold unconditionally whenever 4.92 sqrt(x/log x) <= T0, where T0 is a height of verified RH. Johnston: condition weakened to (9.06/log log x) sqrt(x/log x) <= T0, extending the Schoenfeld-bound range to roughly x <= 1.101 * 10^26 given T0 = 3e12.
- constant: 4.92 (Büthe), 9.06/log log x (Johnston); with T0 = 3.0001753328e12
- status: unconditional | Jan Büthe; Daniel R. Johnston (2021)
- citation: arXiv:1410.7015 (Büthe); arXiv:2109.02249 (Johnston)
- checked against: https://arxiv.org/abs/1410.7015 and https://arxiv.org/pdf/2109.02249
- technique: Weil-Barner explicit formula with Logan's extremal band-limited test functions; Johnston adds an iterative bootstrap
- bottleneck: The test-function choice: Logan functions are extremal for one specific tail criterion, not for the actual composite objective; the constant 4.92/9.06 encodes that mismatch
- tunable: Band-limited test function (infinite-dimensional, discretizable), truncation height, iteration schedule
- gap: The kernel is an explicit optimization surface that has been touched exactly twice (Büthe 2016, Johnston 2021); a numerically optimized kernel (linear programming over band-limited functions, as in bounded-gap-prime and sphere-packing work) plausibly lowers the constant and extends the unconditional Schoenfeld range beyond 10^26 with zero new zero computations

### Explicit Mertens function bounds
- statement: M(x) <= x * exp(-0.209 (log x)^{3/5} (log log x)^{-1/5}) for x >= 3 (first explicit bound of Korobov-Vinogradov shape), plus explicit M(x) << x exp(-eta_1 sqrt(log x)) versions; computationally, |M(x)|/sqrt(x) verified < 0.571 for x <= 10^16 (Hurst).
- constant: 0.209 in the (log x)^{3/5}(log log x)^{-1/5} exponent; Hurst: M(x) computed exactly to x = 10^16
- status: unconditional | Ethan S. Lee (and Leong for the 0.209 refinement); Greg Hurst (computation) (2024)
- citation: arXiv:2208.06141 (v4); Hurst arXiv:1610.08551
- checked against: https://arxiv.org/abs/2208.06141 and https://arxiv.org/abs/1610.08551
- technique: Comparison of M(x) with a short sum over zeta zeros, using explicit bounds for 1/zeta and the verified-zeros database
- bottleneck: Explicit 1/zeta(s) bounds near the 1-line and the zero-free region constant (derived from the now-superseded KV constants)
- tunable: Truncation height of the zero sum, 1/zeta bound selection, sieve computation range
- gap: 0.209 was computed before BTY 4.896 and before Bellotti's 2025 log-free density; re-propagation should improve it. Hurst's 10^16 computation is 8 years old and a modern segmented-sieve + Helfgott-Thompson mu-computation could push the exact-computation frontier and the 0.571 empirical constant

### Primes between consecutive kth powers
- statement: There is a prime between n^155 and (n+1)^155 for all n >= 1 (Cully-Hugill, via a new explicit Goldston-type truncated explicit-formula error). Primes between consecutive cubes for all n >= exp(exp(32.537)). Lee (Feb 2026): a prime between consecutive 86th powers for all n >= 1, with tables covering k >= 65, computed from minimal Littlewood-shape zero-free regions.
- constant: k = 86 (all n), k = 70 (subsequence), cubes threshold exp(exp(32.537))
- status: unconditional | Michaela Cully-Hugill; Ethan Simpson Lee (2026)
- citation: arXiv:2107.14468 (J. Number Theory 2023); arXiv:2602.14340
- checked against: https://arxiv.org/abs/2602.14340
- technique: Truncated Riemann-von Mangoldt explicit formula with explicit Goldston error (arXiv:2402.04272 gives the O(x/T) version), fed by zero-free regions + verification height
- bottleneck: Lee's Feb 2026 tables use pre-March-2026 zero-free regions; the BTY 4.896 constant arrived three weeks after his revision. Also the Goldston-error smoothing is a tunable kernel
- tunable: Zero-free region constant, explicit-formula truncation T, smoothing weight in Goldston error, interval asymmetry
- gap: Recomputing Lee's five tables with 4.896 (and with Bellotti-Wong N(T)) should lower k = 86; the author explicitly solicits improvements. Legendre-conjecture-adjacent record-chasing with fully mechanical inputs

### Explicit error for the truncated Riemann-von Mangoldt explicit formula
- statement: psi(x) = x - sum_{|gamma|<=T} x^rho/rho + explicit error, with the error made fully explicit with an O(x log^2(xT)/T)-shaped bound and, in the 2024 version, an explicit O(x/T) error term (improving constants for applications to primes between powers).
- constant: Explicit constants in the x/T term (tabulated in paper; shape c * x/T for stated ranges)
- status: unconditional | Michaela Cully-Hugill, Daniel R. Johnston (2024)
- citation: arXiv:2402.04272 (v2 Nov 2024)
- checked against: https://arxiv.org/abs/2402.04272
- technique: Goldston's 1983 method made explicit: counting primes in short windows around x paired with zero-density input
- bottleneck: The smoothing window and the treatment of the log^2 factor; measured slack between the bound and the true error is unquantified
- tunable: Window width h, weight function, zero-density input, T-range case splits
- gap: Nobody has published a numerical map of actual-error/bound ratio across (x, T); large measured slack in a specific regime would pinpoint which lemma to sharpen. The lab's explicit.py computes both sides directly

### Explicit zero-density estimates
- statement: KLN 2022: N(sigma,T) <= C1(sigma) T^{8(1-sigma)/3} (log T)^{5-2sigma} + C2(sigma) log^2 T for sigma >= 0.60 (explicit C1, C2 tabulated). Bellotti 2025: first explicit LOG-FREE zero-density estimate (J. Number Theory 269 (2025) 37-77, arXiv:2405.12545), strong enough for a log-free KV zero-free region. Also explicit Ingham-type N(sigma,T) (arXiv:2507.15184, July 2025).
- constant: Tabulated C1(sigma), C2(sigma); e.g. KLN improves Ramare's earlier explicit density constants
- status: unconditional | Habiba Kadiri, Allysa Lumley, Nathan Ng; Chiara Bellotti; (Ingham-explicit authors, 2025) (2025)
- citation: arXiv:2101.12263 (KLN); arXiv:2405.12545 (Bellotti); arXiv:2507.15184
- checked against: https://arxiv.org/abs/2405.12545 (located via search; KLN and Ingham-explicit located via search listings)
- technique: Mollified second-moment method with explicit mollifier coefficients (KLN); Turan-power-sum/log-free machinery (Bellotti)
- bottleneck: Mollifier length and coefficients are chosen for tractability, not optimality; explicit densities remain far above what is known asymptotically (Guth-Maynard 2024 exponent 30/13 has NO explicit version)
- tunable: Mollifier coefficients and length, moment-method smoothing, sigma-range case splits
- gap: An explicit version of even a weakened Guth-Maynard-type estimate would be transformative for every entry above; more modestly, re-optimizing KLN mollifier coefficients numerically for the specific sigma-ranges used by FKS/Johnston-Yang is unmined

### Skewes region: first sign change of pi(x) - li(x)
- statement: There exists x in [1.39792136e316, 1.39847567e316] with pi(x) > li(x) (Saouter-Demichel-style localization); Revers (2025, J. Number Theory) improved the error terms in Lehman's classical method and re-examined crossover regions near 10^316. Lower bound: pi(x) < li(x) for all x <= 10^19 (and up to ~1.39e17 exhaustively by computation).
- constant: Crossover interval [1.39792136e316, 1.39847567e316]; verified pi(x) < li(x) up to at least 10^19
- status: numerical | Yannick Saouter, Patrick Demichel; Michael Revers (2025)
- citation: Saouter-Demichel, Int. J. Number Theory (2010), doi 10.1142/S1793042110003125; Revers, J. Number Theory (2025), arXiv Jan 2025
- checked against: https://www.worldscientific.com/doi/abs/10.1142/S1793042110003125 plus search-result summary of Revers 2025
- technique: Lehman's integral over verified zeros with explicit error terms; high-precision floating-point zero sums
- bottleneck: Lehman-method error terms (partially improved by Revers) and the fact that all published crossover computations are careful floats, not enclosure-checked enclosures
- tunable: Lehman kernel parameter (alpha, eta), truncation height, number of zeros used, enclosure precision schedule
- gap: No ball-arithmetic-enclosure-checked version of the crossover localization exists; Revers's improved error terms have not been combined with the 3e12 zero database under enclosure arithmetic to give a hardened (in this lab's sense) crossover interval, possibly narrower

### de Bruijn-Newman constant enclosure
- statement: 0 <= Lambda <= 0.2. Lower bound Lambda >= 0 by Rodgers-Tao (2018, unconditional; RH is equivalent to Lambda = 0). Upper bound Lambda <= 0.22 by Polymath15 (2019), refined to Lambda <= 0.2 (Polymath15 final version / subsequent slight improvement noted April 2020 by Platt-Trudgian).
- constant: Lambda in [0, 0.2]
- status: unconditional | Brad Rodgers, Terence Tao; Polymath15 (Tao et al.); D. Platt, T. Trudgian (2020)
- citation: arXiv:1801.05914 (Rodgers-Tao); Polymath15, Res. Math. Sci. (2019) 'Effective approximation of heat flow evolution of the Riemann xi function'
- checked against: https://handwiki.org/wiki/De_Bruijn%E2%80%93Newman_constant and https://arxiv.org/pdf/1801.05914
- technique: Upper bound: rigorous numerics on H_t zeros (heat-flow evolution) up to a height, plus a zero-repulsion barrier argument; lower bound: pseudospectra/GUE-statistics argument
- bottleneck: Upper bound needs rigorous H_t zero tracking to larger heights plus barrier certificates; cost grows steeply with target Lambda
- tunable: Barrier location, t-mesh for zero tracking, Euler-product approximation order, verification height used
- gap: Untouched since 2020. The lab's heatflow.py (H_t, zero tracking, Lambda machinery) plus Arb could attempt Lambda <= 0.15: the Polymath15 write-up documents the exact computation that would be needed; nobody has redone it with modern Arb and the 3e12 database

### Verified-zeros infrastructure and rigorous evaluation methods
- statement: Platt's database of the 1.2e13 verified zeros (to height 3e12) is available via LMFDB; Arb (Johansson) provides rigorous ball-arithmetic zeta/Riemann-Siegel evaluation used by essentially all post-2017 enclosure-checked computations; a 2024 method paper extends rigorous verification methodology to GRH for other L-functions (arXiv:2408.00187).
- constant: Zero database to height 3,000,175,332,800
- status: unconditional | David Platt; Fredrik Johansson; (GRH-method authors 2024) (2024)
- citation: arXiv:2408.00187; Johansson, 'Arb: efficient arbitrary-precision midpoint-radius interval arithmetic', IEEE Trans. Computers (2017)
- checked against: https://arxiv.org/pdf/2408.00187 (located via search); Arb citation memory-unverified as to exact journal details
- technique: Band-limited function evaluation, rigorous FFT-based multi-evaluation, Turing/Backlund completeness checks
- bottleneck: Per-evaluation cost of rigorous zeta at large height; database access bandwidth for downstream enclosure-checked computations
- tunable: Precision schedules, band-limited interpolation parameters
- gap: Most downstream explicit papers still use the database through float summaries rather than end-to-end enclosures; wiring the database into enclosure-carrying recomputations (Skewes, Mertens, psi bounds) is systematically unharvested


## Territory I: neighboring L-function problems ,  Dirichlet critical-line proportions, Landau-Siegel zeros, moments in families, central-point non-vanishing records, function-field analogues, elliptic curve L-functions, random-matrix predictions in families (state of the art, August 2026)

### Critical-line proportion for Dirichlet L-functions, averaged over conductors (Sono)
- statement: Averaged over primitive characters chi mod q and conductors q <= Q, at least 61.07% of the nontrivial zeros of Dirichlet L-functions L(s,chi) lie on the critical line Re(s)=1/2, and at least 60.44% are simple and on the critical line, as Q -> infinity.
- constant: 0.6107 (on-line), 0.6044 (simple and on-line)
- status: unconditional | Keiju Sono (2024)
- citation: arXiv:2105.07422 (v. revised 2024-06-12)
- checked against: https://arxiv.org/abs/2105.07422
- technique: Levinson's method with Feng's two-piece mollifier, powered by the Conrey-Iwaniec-Soundararajan asymptotic-large-sieve mean-square formula for Dirichlet L-functions times Dirichlet polynomials
- bottleneck: Mollifier length is capped by the range of the asymptotic large sieve; Feng-mollifier coefficient optimization was done for the zeta-analogue shape, not re-optimized for the q-aspect kernel
- tunable: Feng mollifier polynomial coefficients, mollifier length theta, Levinson shift R, smoothing weights in the mean-square
- gap: The August 2026 zeta framework that pushed the t-aspect constant from 5/12-type records to 0.67250 (two papers combined; Lean-formalized) has no written q-aspect analogue. Sono's 61.07% predates it; transplanting the new kernel/mollifier combination into the CIS large-sieve setting is unharvested.

### Fixed-modulus critical-line proportion (Dickinson)
- statement: For every sufficiently large modulus q, at least 38.2% of the nontrivial zeros of primitive Dirichlet L-functions of modulus q lie on (per the journal version, near/on) the critical line (reported figure from search snippet; the Mathematika title says 'near the critical line', so the precise on-line vs near-line scope needs the paper).
- constant: 0.382 (reported)
- status: unconditional | M. Dickinson (per Mathematika listing) (2024)
- citation: Mathematika (2024), doi:10.1112/mtk.12239
- checked against: https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/mtk.12239 (title/venue verified via search; exact statement from search snippet, not fetched ,  treat the 38.2% scope as to-be-confirmed)
- technique: Levinson-type method at fixed modulus without conductor averaging
- bottleneck: Without the conductor average the mean-square input is much weaker, so the mollifier is far shorter than in Sono's averaged result
- tunable: mollifier coefficients and length at fixed q
- gap: The 22.8-point gap between fixed-q (38.2%) and conductor-averaged (61.07%) proportions is a measure of what the asymptotic large sieve buys; any improvement to the fixed-q mean square directly moves this constant

### Critical zeros of twisted PGL(2) and PGL(3) L-functions (July 2026)
- statement: For a fixed self-dual PGL(3) automorphic representation Pi_0, at least 1/9 of the zeros of the twisted L-functions L(s, Pi_0 x chi), averaged over primitive Dirichlet characters chi of conductor up to Q, lie on the critical line as Q -> infinity; unconditional (no GRC). For PGL(2) twists the result is fully unconditional and quantitatively stronger. Underlying tool: new asymptotic formula with power-saving error for the mean square of L(1/2+it, Pi_0 x chi) times Dirichlet polynomials, uniformly for Q^eps <= T <= Q^(1/3-eps), with error O_eps(Q^(7/4+eps)) at T=Q^eps.
- constant: 1/9 = 0.111... (PGL(3), self-dual)
- status: unconditional | Brian Conrey, Chung-Hang Kwan, Yongxiao Lin, Caroline L. Turnage-Butterbaugh (2026)
- citation: arXiv:2607.00282
- checked against: https://arxiv.org/abs/2607.00282
- technique: Levinson's method plus a refined, flexible, uniform Asymptotic Large Sieve for higher-degree L-functions, avoiding the Generalized Ramanujan Conjecture; Hecke-algebra computations done in Mathematica
- bottleneck: Degree-3 mollifier length allowed by their mean-square theorem is short; the 1/9 constant is one month old and the Levinson optimization (mollifier shape, shift R) is essentially virgin
- tunable: mollifier polynomial coefficients (degree-3 arithmetic factors), mollifier length, Levinson shift, T-averaging window in [Q^eps, Q^(1/3-eps)]
- gap: First-generation constant in a brand-new framework: Feng-type multi-piece mollifiers, optimized shifts, and Sono-style coefficient tuning have not been applied. This is the freshest optimization surface in the territory.

### Non-vanishing at the central point, general modulus record (Qin-Wu)
- statement: For at least 7/19 (~= 36.84%) of the primitive Dirichlet characters chi of large general modulus q, L(1/2, chi) != 0.
- constant: 7/19 = 0.368421...
- status: unconditional | Xinhua Qin, Xiaosheng Wu (2025)
- citation: arXiv:2504.11916
- checked against: https://arxiv.org/abs/2504.11916
- technique: Mollified first and second moments with an enlarged mollifier for general (not necessarily prime) moduli
- bottleneck: One-mollifier second-moment methods cannot exceed 50% (Iwaniec-Sarnak barrier); each increment comes from mollifier length and shape
- tunable: mollifier coefficients, mollifier length exponent, character-sum decompositions by divisor structure of q
- gap: General-modulus record 7/19 still trails the prime-modulus record 5/13 (~38.46%, Khan-Milicevic-Ngo); closing that gap, or feeding in the new mollified fourth moment (arXiv:2509.24690), is open

### Prime-modulus non-vanishing record 5/13 (Khan-Milicevic-Ngo lineage)
- statement: For prime moduli q, L(1/2,chi) != 0 for at least 5/13 (~= 38.46%) of primitive chi mod q. Lineage: >= 1/3 (Iwaniec-Sarnak), 34.11% (Bui), 3/8 (Khan-Ngo), 5/13 (Khan-Milicevic-Ngo).
- constant: 5/13 = 0.384615...
- status: unconditional | Rizwanur Khan, Djordje Milicevic, Hieu T. Ngo (2022)
- citation: Khan-Milicevic-Ngo, 'Nonvanishing of Dirichlet L-functions II' (lineage recounted in arXiv:2504.11916 introduction)
- checked against: https://arxiv.org/html/2504.11916 (lineage paragraph)
- technique: Mollified moments with longer mollifiers exploiting primality of q; delta-method/spectral input
- bottleneck: Same 50% ceiling for the two-moment method; mollifier length is the only dial
- tunable: mollifier coefficients and lengths; moment-mixing weights
- gap: No one has yet combined the 2025 mollified fourth moment (length q^(1/22)) with the second-moment method in a two-moment optimization for a fixed modulus; the optimal mixture is an unexplored finite-dimensional problem

### Mollified fourth moment of Dirichlet L-functions with power saving (Gao-Wu-Zhao)
- statement: Asymptotic formula with power-saving error term for the fourth moment of Dirichlet L-functions to modulus q, mollified by a Dirichlet polynomial of length q^(1/22-eps), valid for all moduli q not congruent to 2 mod 4; improves X. Wu's asymptotic for the unmollified fourth moment at the central point.
- constant: mollifier length exponent 1/22
- status: unconditional | Peng Gao, Xiaosheng Wu, Liangyi Zhao (2025)
- citation: arXiv:2509.24690
- checked against: https://arxiv.org/abs/2509.24690
- technique: Fourth-moment machinery (shifted convolutions, spectral theory) extended to carry a mollifier with power saving
- bottleneck: Mollifier length 1/22 is short; the error-term budget in the shifted-convolution analysis is what limits it
- tunable: mollifier coefficients, moment-mixing ratio between mollified second and fourth moments, Cauchy vs one-sided Chebyshev inequalities
- gap: A mollified fourth moment is exactly the input that historically breaks second-moment non-vanishing barriers (cf. Soundararajan's 7/8 in the quadratic family via higher moments); no published non-vanishing consequence has yet been extracted from this theorem

### Unconditional sixth moment of Dirichlet L-functions at the central point (no t-averaging)
- statement: Asymptotic formula for the sixth moment of L(1/2,chi), summed over primitive chi mod q and averaged over all moduli q <= Q, WITHOUT the extraneous short t-averaging that Conrey-Iwaniec-Soundararajan (2007) required; resolves the moment problem Huxley bounded in 1970. Leading constant consistent with the CFKRS/random-matrix prediction (g_3 factor 42 analogue for the family).
- constant: sixth moment, q <= Q average, power-saving quality per paper
- status: unconditional | Vorrapan Chandee, Xiannan Li, Kaisa Matomaki, Maksym Radziwill (2024)
- citation: arXiv:2409.01457
- checked against: https://arxiv.org/abs/2409.01457
- technique: Asymptotic large sieve plus new treatment of 'unbalanced' sums that appear when the t-average is removed
- bottleneck: The eighth moment in this family is still only known with extra averaging/conditionally; the unbalanced-sum technique's reach is the frontier
- tunable: unbalanced-sum decomposition parameters; potential mollifier insertion
- gap: A mollified version of this sixth moment (analogous to arXiv:2509.24690 for the fourth) would feed three-moment non-vanishing and proportion-of-critical-zeros schemes; not yet written. Also: no numerical verification of their secondary terms exists in the literature.

### Zhang's Landau-Siegel zero claim: status as of August 2026
- statement: Claimed: L(1,chi) >> (log D)^(-2022) for real primitive chi mod D, with absolute effectively computable constant; equivalently no Landau-Siegel zero within c(log D)^(-2024) of s=1 (vs the conjectured c/log D). Status: the November 2022 preprint (111 pages) remains unpublished as of August 2026; Tao and others forwarded numerical/technical problems, at least one reported mistake in numerics with unclear criticality; Zhang stated in a 2025 interview (PKU/PMC profile) that a revised paper is nearly complete at Sun Yat-sen University. No community consensus of correctness; no refereed acceptance.
- constant: exponent 2022 in L(1,chi) >> (log D)^(-2022)
- status: conjecture (claimed proof, unverified; community status: open) | Yitang Zhang (2022)
- citation: arXiv:2211.02515
- checked against: https://www.math.columbia.edu/~woit/wordpress/?p=13137 and https://arxiv.org/abs/2211.02515 and https://pmc.ncbi.nlm.nih.gov/articles/PMC12527331/
- technique: Discrete mean estimates for products of L-functions against carefully chosen coefficient sequences (a variant of the Goldfeld/Iwaniec-Sarnak non-positivity framework)
- bottleneck: Verification: the argument's numerics and several technical lemmas have not survived expert scrutiny publicly; nobody has published either a repair or a refutation
- tunable: coefficient sequences in the discrete mean; the exponent 2022 itself (artifact of choices, not intrinsic)
- gap: The paper's discrete mean estimates are checkable numerically at finite level: the claimed inequalities between the main terms are explicit. A computational audit of the key numerical inequality (the reported locus of the 'meaningful mistake in numerics') has never been published.

### CFKRS moment conjectures proved over function fields (all moments, large q)
- statement: For the family of quadratic Dirichlet L-functions over F_q(t): the Conrey-Farmer-Keating-Rubinstein-Snaith predictions for ALL moments hold for all sufficiently large odd prime powers q. Achieved by computing the stable homology of braid groups with coefficients in Schur functors of the Burau representation (Bergstrom-Diaconu-Petersen-Westerland, a twisted-coefficients hyperelliptic Madsen-Weiss theorem) combined with the uniform twisted homological stability theorem of Miller-Patzt-Petersen-Randal-Williams.
- constant: all moments E prod L(1/2,chi_d)^k match CFKRS polynomials for q >= q_0(k), q_0 ineffective
- status: unconditional | Jonas Bergstrom, Adrian Diaconu, Dan Petersen, Craig Westerland; Jeremy Miller, Peter Patzt, Dan Petersen, Oscar Randal-Williams (2024)
- citation: arXiv:2302.07664 and arXiv:2402.00354
- checked against: https://arxiv.org/abs/2302.07664 and https://arxiv.org/abs/2402.00354
- technique: Stable homology of braid/Hurwitz-type moduli, scanning maps, uniform twisted homological stability; moments become point counts on stable cohomology via Grothendieck-Lefschetz
- bottleneck: 'Sufficiently large q' is ineffective (stability ranges vs error terms); fixed small q (q=3,5) and the number-field transfer are untouched
- tunable: moment order k, genus/conductor degree, prime power q; on the topology side, stability ranges
- gap: Nobody has published (a) an effective q threshold, (b) numerical moments at small q locating where CFKRS fails or holds, or (c) a translation of the identified stable-homology secondary structure into a number-field secondary-term conjecture. All three are open surfaces.

### Failure of the Chowla non-vanishing analogue over function fields (Wanlin Li)
- statement: There are infinitely many quadratic Dirichlet characters chi over F_q(t) with L(1/2,chi)=0, with an explicit lower bound on their count; over Q, Chowla's conjecture predicts none exist, and Soundararajan proved >= 7/8 of L(1/2, chi_8d) are nonzero. The function-field vanishing count is 0% density and the constructed proportion decreases as q grows.
- constant: explicit lower bound ~ X^c on vanishing characters of conductor degree <= X (see paper for c)
- status: unconditional | Wanlin Li (2018)
- citation: arXiv:1801.02873
- checked against: https://arxiv.org/abs/1801.02873
- technique: Geometric: L(1/2,chi)=0 is forced by maps from the associated hyperelliptic curve to a fixed abelian variety (central vanishing = extra Frobenius eigenvalue structure on the Jacobian)
- bottleneck: The construction gives sparse families; whether vanishing occurs beyond geometric constructions (i.e., 'random' vanishing) is open in both directions
- tunable: base field size q, conductor degree, choice of target abelian variety
- gap: Recent extensions to fixed-order characters (e.g. arXiv:2506.07815 on non-vanishing for fixed-order families) leave a live boundary: exhaustive small-q censuses of central vanishing beyond Li's construction have not been published. Any non-geometric vanishing instance would be a new phenomenon.

### Quadratic family non-vanishing benchmark (Soundararajan 7/8) and 2026 root-number-restricted variant
- statement: At least 7/8 of odd squarefree d have L(1/2, chi_8d) != 0 (Soundararajan, mollifier of length (sqrt X)^a giving proportion 1-(1+a)^(-3), a<1 admissible; 15/16 under GRH per subsequent literature). New in March 2026: for even primitive characters of prime conductor with shrinking angular restrictions on the root number, mollified first and second moments give a positive (unspecified) non-vanishing proportion within each root-number sector (Earnst).
- constant: 7/8 = 0.875; conjectured truth 100% (Chowla)
- status: unconditional (7/8); unconditional, positive-proportion-only (2026 sectors) | Kannan Soundararajan (2000); Adam Earnst (2026) (2000)
- citation: Soundararajan, Ann. of Math. 152 (2000) 447-488; arXiv:2603.22124
- checked against: https://arxiv.org/abs/2603.22124 (fetched) ; 7/8 corroborated via search snippets (query: quadratic Dirichlet non-vanishing Soundararajan 7/8) ,  Annals citation from memory
- technique: Mollified first and second moments; for the quadratic family the first moment with long mollifier does disproportionate work; the 2026 paper adds angular sectors of the root number as a new family-slicing variable
- bottleneck: Quadratic family: mollifier length a<1 barrier; sector version: no explicit constant extracted yet
- tunable: mollifier length a, mollifier coefficients, angular sector width
- gap: The sectorized-root-number technique has no quadratic-family or zeta analogue written down; extracting an explicit constant from Earnst's positive proportion is a straightforward optimization nobody has published

### Distribution of ell^infinity-Selmer groups in twist families (Smith), published 2026
- statement: The distribution of 2^k-Selmer groups (all k) in quadratic twist families of elliptic curves E/Q with full rational 2-torsion and no rational cyclic 4-isogeny matches the Markov-chain prediction; consequences: 100% of such twists have rank <= 1 in the Selmer sense, and Goldfeld's conjecture (average twist rank 1/2; 50% rank 0, 50% rank 1) holds for such E conditionally on BSD for the family. Published as JAMS 39 (2026), no.1, 1-72 and no.2, 453-514.
- constant: rank distribution: density 1/2 rank 0, 1/2 rank 1 among twists (under BSD); unconditional Selmer version exact
- status: unconditional (Selmer statements); BSD-conditional (Goldfeld consequence) | Alexander Smith (2026)
- citation: A. Smith, 'The distribution of ell^infinity-Selmer groups in degree ell twist families I, II', J. Amer. Math. Soc. 39 (2026)
- checked against: https://www.asmith-math.org/papers.html and https://arxiv.org/pdf/2606.06024 (survey citing Smi26a, Smi26b)
- technique: Additive-combinatorial / equidistribution analysis of Cassels-Tate pairings across twist families; Markov chain on Selmer ranks
- bottleneck: Removing the full 2-torsion hypothesis, and converting 2^infinity-Selmer control into analytic-rank (L-function) statements without BSD
- tunable: family slicing (torsion structure, isogeny classes); moment functionals on Selmer distributions
- gap: The L-function side is behind the algebraic side: no one has proved the matching non-vanishing statement 'L(1/2, E_d) != 0 for 50% of twists' for a single curve; the best analytic results are positive proportions. The transfer of Smith's distributional structure to central-value moments (a Katz-Sarnak-consistent refinement) is unwritten.

### Proportion of elliptic curves satisfying rank-part BSD (Bhargava-Skinner-Zhang)
- statement: At least 66.48% of elliptic curves over Q, ordered by naive height, satisfy the rank part of the Birch-Swinnerton-Dyer conjecture and have finite Tate-Shafarevich group. As of this survey no published improvement of the 66.48% constant was located (searches returned the 2014 paper as the standing record).
- constant: 0.6648
- status: unconditional | Manjul Bhargava, Christopher Skinner, Wei Zhang (2014)
- citation: arXiv:1407.1826
- checked against: https://mattbaker.blog/2014/03/10/the-bsd-conjecture-is-true-for-most-elliptic-curves/ (constant corroborated via search; arXiv ID from search results)
- technique: Combination of average n-Selmer sizes (Bhargava-Shankar geometry-of-numbers), Iwasawa main conjecture (Skinner-Urban), p-converse theorems (Skinner, Zhang), and a squarefree-sieve style inclusion across primes p=2,3,5
- bottleneck: The loss comes from curves not covered by any p-converse theorem at the sieved primes; each new p-converse theorem or improved Selmer average moves the constant
- tunable: choice of primes p, combination weights of Selmer averages, newer converse-theorem hypotheses
- gap: The constant 66.48% is the output of an explicit finite optimization over which primes and which Selmer conditions to combine; post-2014 p-converse theorems (Burungale-Skinner-Tian et al.) have never been fed back into the original optimization in print

### One-level density for Dirichlet L-functions with support beyond the trivial range (Drappeau-Pratt-Radziwill)
- statement: For the family of primitive Dirichlet characters (suitably averaged over moduli), the 1-level density of low-lying zeros agrees with the Katz-Sarnak (unitary) prediction for test functions whose Fourier transform is supported in [-2 - 50/1093, 2 + 50/1093]. This is the first unconditional extension past support [-2,2] in any family; previously any extension required hypotheses beyond GRH (e.g. Montgomery's conjecture on primes in progressions).
- constant: support radius 2 + 50/1093 = 2.04574...
- status: unconditional | Sary Drappeau, Kyle Pratt, Maksym Radziwill (2020)
- citation: arXiv:2002.11968
- checked against: https://arxiv.org/pdf/2002.11968 (abstract via search snippet)
- technique: Sums of Kloosterman sums / Deshouillers-Iwaniec spectral estimates applied to primes in arithmetic progressions on average beyond the large-sieve barrier
- bottleneck: The delta = 50/1093 is inherited from specific Deshouillers-Iwaniec-type exponents in the bilinear Kloosterman-sum estimates
- tunable: exponent-pair inputs from Kloosterman estimates, sieve decomposition parameters, the final linear program over bilinear ranges
- gap: Improved bounds for sums of Kloosterman sums (notably Pascadi's 2023-2025 refinements of Deshouillers-Iwaniec exponents) have not, in any publication located, been propagated through the DPR linear optimization to enlarge 50/1093; the constant looks mechanically improvable

### Ratios conjecture for real Dirichlet characters proved in restricted shift ranges (Cech); Maass-family density extension (2025)
- statement: The Conrey-Farmer-Zirnbauer ratios conjecture for the family of real (quadratic) Dirichlet characters holds, under GRH, with one shift in the numerator and one in the denominator, for shifts in an explicit range, via multiple Dirichlet series; the range improves when non-primitive characters are included. Separately (2025): unconditional one-level density for Maass form L-functions with support extended to (-15/8, 15/8) (arXiv:2505.18712).
- constant: one shift over one shift; explicit shift-range inequalities in the paper
- status: RH-conditional (GRH) for the ratios result; unconditional for the Maass density extension | Martin Cech; (Maass paper authors per arXiv:2505.18712) (2024)
- citation: arXiv:2110.04409 (Cech); arXiv:2505.18712
- checked against: https://arxiv.org/abs/2110.04409 (abstract via search snippet)
- technique: Meromorphic continuation of multiple Dirichlet series beyond the region of absolute convergence; spectral/trace-formula input for the Maass family
- bottleneck: MDS continuation currently reaches only limited shift ranges; the full ratios conjecture (uniform shifts, arbitrary numerator/denominator counts) is far off
- tunable: shift parameters alpha, gamma; family enlargement (primitive vs all characters); test-function support
- gap: Nobody has published a numerical map of where the one-shift ratios asymptotic actually starts failing (if it does) beyond the proved range; the predicted-vs-computed divergence boundary is measurable and unmeasured

### Infinitely many rank-1 elliptic curves over every number field (Zywina 2025)
- statement: For any quadratic extension L/K of number fields, there are infinitely many elliptic curves E/K with rank E(K) = rank E(L) = 1; in particular infinitely many elliptic curves of rank 1 over any number field. Unconditional; proof by specializing a nonisotrivial rank-1 family and computing all ranks involved (distinct from the Koymans-Pagano and Alpoge-Bhargava-Ho-Shnidman approaches).
- constant: infinitude (no density)
- status: unconditional | David Zywina (2025)
- citation: arXiv:2505.16960
- checked against: https://arxiv.org/abs/2505.16960
- technique: Explicit rank-1 family with controlled specialization (height/root-number engineering), avoiding Selmer statistics entirely
- bottleneck: Gives infinitude, not positive proportion; positive-proportion rank-1 over general number fields remains open (and the naive Goldfeld analogue over number fields is known to fail in some formulations, cf. arXiv:2602.21985)
- tunable: family parametrization, specialization heights
- gap: The interplay between Zywina's explicit families and central-value non-vanishing of the corresponding L-functions (analytic rank 1 via Gross-Zagier style inputs) is not written; also the February 2026 'Goldfeld conjecture for non-hyperelliptic direction' (arXiv:2602.21985) opens a genus-2/non-hyperelliptic direction unmined analytically


## Territory J: forgotten, abandoned, or obscure RH approaches whose limiting factor was historical computation ,  Riesz/Hardy-Littlewood quantitative criteria, Baez-Duarte sequential numerics that stopped mid-2000s, Turan partial-sum program killed by Montgomery 1983, Matiyasevich determinant/Hankel observations, de Bruijn-Newman precursors, Redheffer spectra, Franel-Landau, Speiser, and Weil-positivity truncations

### Riesz criterion (1916), modern equivalent form
- statement: RH is equivalent to: sum_{n>=1} mu(n)/n^2 * exp(-x/n^2) = O_eps(x^{-3/4+eps}) as x -> infinity, for every eps > 0 (Agarwal-Garg-Maji 2022 restatement); equivalently Riesz's original R(x) = sum_{k>=1} (-1)^{k+1} x^k / ((k-1)! zeta(2k)) = O(x^{1/4+eps}).
- status: conjecture | M. Riesz; modern one-variable generalization by A. Agarwal, M. Garg, B. Maji (2022)
- citation: arXiv:2202.00637, Proc. Amer. Math. Soc. 2022; Riesz, Acta Math. 40 (1916)
- checked against: https://arxiv.org/abs/2202.00637
- technique: Mobius-weighted exponential sums, Hardy-Littlewood identity generalized in one extra parameter, Mellin inversion
- bottleneck: The alternating series defining R(x) suffers catastrophic cancellation for large x (terms grow like x^k/(k-1)! before collapsing), so pre-modern numerics never reached x large enough to see the conjectured envelope cleanly
- tunable: choice of generalized-Riesz parameters (alpha, beta); truncation point and precision of the alternating sum; saddle-point contour for large-x evaluation; which zero terms to include in the envelope model
- gap: No enclosure-checked (ball-arithmetic) computation of R(x) or of the Mobius-exponential form at large x exists; the amplitude of the oscillatory envelope (contribution of the first zero pair through 1/(rho zeta'(rho)) factors) has never been pinned numerically, and the (alpha, beta) family of generalized criteria in 2202.00637 and arXiv:2409.17708 is numerically unexplored

### Hardy-Littlewood criterion (1918)
- statement: RH is equivalent to: sum_{k>=1} (-x)^k / (k! zeta(2k+1)) = O(x^{-1/4}) as x -> infinity. Paris (2021) computed both this and the Riesz case numerically and observed the required x^{-1/4} and x^{-3/4} decay with superimposed oscillation.
- status: conjecture | G. H. Hardy, J. E. Littlewood; numerics R. B. Paris (2021)
- citation: arXiv:2107.02800 (Paris, The numerical evaluation of the Riesz function); Hardy-Littlewood, Acta Math. 41 (1918)
- checked against: https://arxiv.org/abs/2107.02800
- technique: asymptotics of generalized hypergeometric-type series; numerical scheme for large positive x (Paris)
- bottleneck: Same cancellation problem as Riesz; Paris's 2021 scheme is floating-point, not enclosure-checked, and stops at moderate x with only 5 illustrative figures
- tunable: asymptotic-expansion truncation order; working precision; range of x; choice of L-function (zeta vs DH counterexample)
- gap: Paris's numerics are the ONLY modern computation and carry no error bounds; nobody has fit the oscillation phase against gamma_1 = 14.134725141734694 with enclosure-checked enclosures, and nobody has run the same scheme on a Davenport-Heilbronn analogue to see what failure of RH looks like in this observable

### Baez-Duarte sequential Riesz criterion and the abandoned c_k numerics
- statement: With c_k := sum_{j=0}^{k} (-1)^j binom(k,j) / zeta(2j+2), RH is equivalent to c_k = O(k^{-3/4+eps}). Maslanka evaluated c_k via Norlund-Rice integrals to k = 4*10^8; Wolf presented plots for k in (1, 10^9) and gave formulae for arbitrary large k. Observed: c_k ~ k^{-3/4} times an oscillation whose wavelength in log k corresponds to the first zero gamma_1 = 14.134725141734694, plus a trend from trivial zeros.
- status: conjecture | L. Baez-Duarte (criterion, 2005); K. Maslanka, M. Wolf (numerics, 2006) (2006)
- citation: arXiv:math/0605485 (Wolf); arXiv:math/0603713 (Maslanka, Rice's integrals); arXiv:math-ph/0608050
- checked against: https://arxiv.org/pdf/math/0605485
- technique: alternating binomial sums, Norlund-Rice contour integrals, saddle-point evaluation
- bottleneck: In 2006 the saddle-point evaluation at k ~ 10^9 exhausted available multiprecision compute; the series stopped there and no one has enclosure-checked a single c_k with rigorous enclosures at large k
- tunable: Norlund-Rice contour and saddle location; number of zeta zeros in the model envelope; precision schedule; k-grid spacing (logarithmic)
- gap: Twenty years of hardware and Arb ball arithmetic make k = 10^11-10^12 reachable; the envelope constant (amplitude of the k^{-3/4} oscillation, expressible through 1/(rho(1-rho) zeta'(rho)) at rho = 1/2 + i*14.1347...) has never been measured against theory, and the criterion has never been run on a function that violates RH to calibrate its detection power

### Wolf's two-route consistency falsification experiment
- statement: Wolf (2009) computed c_{100000} to 1000 decimal digits by two independent formulas (binomial sum vs zero-expansion) intending to disprove RH if they disagreed; they agreed to 10^{-996}. The paper explicitly discusses the Davenport-Heilbronn function as the model where the analogous hypothesis fails.
- status: numerical | M. Wolf (2009)
- citation: arXiv:0910.1534 (Failed attempt to disproof the Riemann Hypothesis)
- checked against: https://arxiv.org/abs/0910.1534
- technique: multiprecision evaluation of one c_k by two analytically independent routes; discrepancy would witness an off-line zero
- bottleneck: One value of k, one function (zeta), 2009-era multiprecision; the experiment was run once and abandoned
- tunable: k values; digit count; which zeros enter the zero-expansion route; target function (zeta vs DH)
- gap: The experiment was never scaled (many k, higher digits) and, critically, never run on Davenport-Heilbronn where it MUST show a discrepancy pattern from the off-line zero near s = 0.808517 + 85.699348i; that positive control has never been published and would quantify exactly what sensitivity the test has

### Turan's partial-sum program and Montgomery's quantitative kill
- statement: Turan (1948) showed RH follows if zeta_N(s) = sum_{n<=N} n^{-s} is nonzero in sigma > 1 for all large N. Montgomery (1983) proved sup{Re s : zeta_N(s) = 0} = 1 + (4/pi - 1 - o(1)) * log log N / log N, with 4/pi - 1 = 0.2732395447351628, so zeta_N has zeros with sigma > 1 for all large N. Platt-Trudgian (2016) determined exactly: zeta_N has no zeros with Re s > 1 precisely for N in {1,...,18, 20, 21, 28}; every other N gives infinitely many.
- status: unconditional | P. Turan; H. L. Montgomery; D. J. Platt, T. S. Trudgian (2016)
- citation: arXiv:1507.01340, LMS J. Comput. Math. 19 (2016) 37-41; Montgomery, in Studies in Pure Mathematics (Turan memorial), 1983
- checked against: https://arxiv.org/abs/1507.01340
- technique: Turan power-sum method; Montgomery's use of extreme values of Dirichlet polynomials; rigorous computation for small N
- bottleneck: Montgomery's constant 4/pi - 1 comes with a non-effective o(1); nobody knows the actual rate of approach, and the borderline-N census (which N first produce zeros above sigma = 1 + delta for concrete delta) was only ever done for the sigma > 1 threshold
- tunable: N range; zero-locating contour rectangles; the power-sum auxiliary polynomial in any effectivization; delta thresholds in the census
- gap: An effective version of Montgomery's theorem (explicit o(1)) is open, and the empirical convergence of (sigma_N - 1) log N / log log N toward 0.27324 has never been measured; a mismatch at computable N would sharpen or falsify the natural effective conjecture. Related: Gonek-Ledoan (arXiv:0807.0019) and the Spira-era computations were never redone with enclosure-checked arithmetic

### Matiyasevich's interpolating-determinant / finite Dirichlet series observations
- statement: A finite Dirichlet series of length 2N chosen to vanish at the first N nontrivial zeros reproduces further zeros and zeta values inside the critical strip to spectacular accuracy (errors dropping like a power of N far beyond interpolation heuristics), and its coefficients approximate Mobius-like data; documented at multiprecision for N up to a few thousand on 2013-2016 supercomputers.
- status: numerical | Y. Matiyasevich; S. Beltraminelli, D. Merlini (multiprecision study) (2014)
- citation: arXiv:1402.5295 (Approximation of Riemann's zeta function by finite Dirichlet series: multiprecision numerical approach); Matiyasevich, MPIM preprint 2013-18
- checked against: https://arxiv.org/abs/1402.5295
- technique: interpolating determinants on zero data; very high precision linear algebra (thousands of digits)
- bottleneck: Dense structured linear algebra at thousands of digits was supercomputer-bound in 2013; the observed coefficient regularities were left as unexplained conjectures and essentially no one followed up
- tunable: N; precision; choice of interpolation nodes (zeros vs Gram points, cf. arXiv:2412.13438); regularization of the determinant solve
- gap: The conjectured relations between the interpolation coefficients and the alternating-zeta zeros were never tested at larger N, never given error models, and never run against the DH counterexample (does the phenomenon require RH-type zero structure or not?); modern flint/Arb makes N ~ 10^4 with enclosure-checked residuals feasible on a workstation

### Matiyasevich's Hankel-matrix eigenvalue reformulation of RH
- statement: RH is restated in terms of eigenvalues of special almost-triangular Hankel matrices whose entries come from Taylor coefficients of zeta; supercomputer runs revealed structured eigenvalue/eigenvector patterns and led Matiyasevich to conjectures formally STRONGER than RH, published with limited numerical range.
- status: conjecture | Y. Matiyasevich (2017)
- citation: Proc. Steklov Inst. Math. 296 (2017), Riemann's hypothesis in terms of the eigenvalues of special Hankel matrices; preprint The Riemann Hypothesis and eigenvalues of related Hankel matrices I (2014)
- checked against: https://link.springer.com/content/pdf/10.1134/S0081543817030099.pdf
- technique: Hankel matrices from zeta Taylor coefficients; multiprecision Lanczos (fast Lanczos with multiprecision arithmetic, per companion paper)
- bottleneck: 2014-2017 eigenvalue computations at the needed precision were expensive; the stronger-than-RH conjectures were stated from small matrix sizes and never independently reproduced
- tunable: matrix dimension; precision; which coefficient normalization; spectral algorithm (Lanczos restarts); the comparison function fed to the same pipeline
- gap: No independent replication exists, no negative control has ever been run (the identical Hankel construction applied to Davenport-Heilbronn would test whether the eigenvalue patterns actually encode RH-type structure or are generic to functional-equation functions), and matrix sizes 10x beyond Matiyasevich's are now cheap

### de Bruijn-Newman constant: 0 <= Lambda <= 0.2
- statement: Rodgers-Tao (2018) proved Lambda >= 0 unconditionally. Polymath15 (2019) proved Lambda <= 0.22 unconditionally and Lambda <= 0.2 using the Platt-Trudgian numerical verification of RH to height 3*10^12 (arXiv 2020); mechanism: Lambda <= t + sigma_max(t)^2/2 via enclosure-checked barrier computations for the heat-flow evolution H_t. Precursors: de Bruijn 1950 (Lambda <= 1/2), Newman 1976 (constant defined, conjectured Lambda >= 0); Csordas-Smith-Varga Lehmer-pair lower bounds are now superseded.
- status: unconditional | B. Rodgers, T. Tao; D.H.J. Polymath; precursors N.G. de Bruijn, C.M. Newman (2019)
- citation: arXiv:1904.12438 (Polymath 15), Res. Math. Sci. 6 (2019); Rodgers-Tao, Forum Math. Pi 8 (2020)
- checked against: https://michaelnielsen.org/polymath/index.php?title=De_Bruijn-Newman_constant
- technique: heat-flow evolution of xi, effective approximation A + B - C, barrier certification, zero dynamics
- bottleneck: Pushing below 0.2 needs either a higher rigorous RH verification height than 3*10^12 or a substantially cheaper enclosure-checked barrier at smaller t; both are raw-compute problems, exactly what stalled the Polymath effort
- tunable: t; barrier location x; verification height T_0; mollifier/Euler-product bounds in the A+B-C approximation; enclosure precision
- gap: No improvement since 2019/2020; the wiki explicitly frames the next step as a parameter trade (verification height vs t vs barrier location) that nobody has re-run with 2026 hardware and Arb-native code. The lab's heatflow.py implements H_t and zero tracking already

### Keiper-Li coefficients: rigorous values to n = 10^5, asymptotics as RH observable
- statement: Li's criterion: RH iff lambda_n >= 0 for all n >= 1. Keiper (1992) computed to n = 7000 and observed lambda_n approx (1/2)(log n - log(2*pi) + gamma - 1) under RH. Johansson's Arb rigorously computed the first 10^5 Keiper-Li coefficients (lambda_{100000} took ~71051 s wall time and ~48700 MiB RAM). Voros proved RH is equivalent to tempered growth ~ (1/2) n log n of the Li form, with RH-falsity forcing exponentially growing oscillations.
- status: unconditional | J. B. Keiper; X.-J. Li; A. Voros; F. Johansson (computation) (2016)
- citation: arXiv:1611.02831 (Johansson, Arb paper, sec. on Keiper-Li); arXiv:1403.4558 (Voros); McPhedran arXiv:2311.06294 (2023 numerics)
- checked against: https://arxiv.org/pdf/1611.02831
- technique: rigorous series manipulation of log xi in ball arithmetic; asymptotic analysis by saddle point (Voros)
- bottleneck: Cost grows superlinearly in n (the n = 10^5 record needed 48 GB); the interesting regime where a putative off-line zero at height T first bends lambda_n is n ~ T^2, far beyond direct reach
- tunable: algorithm (power series vs zero-sum route); n range; precision schedule; the height-T exclusion trade-off
- gap: n = 10^5 has stood since 2016; no one has combined the two independent routes (lab's li.py) with the Voros oscillation model to give a enclosure-checked statement of the form 'any zero off the line below height T would force lambda_n < 0 for some computed n', which would convert the existing table into an exclusion statement

### Turan inequalities for xi (Csordas-Norfolk-Varga) and effective Jensen hyperbolicity
- statement: Csordas-Norfolk-Varga (1986) proved the Turan inequalities b_m^2 > b_{m-1} b_{m+1} (m >= 1) for the Taylor coefficients of the Riemann xi-function, settling a 58-year-old problem of Polya. Polya: RH iff ALL Jensen polynomials J_{d,n} of xi are hyperbolic. Griffin-Ono-Rolen-Zagier (PNAS 2019, arXiv:1902.07321): for each d, J_{d,n} is hyperbolic for all sufficiently large n; effective threshold of shape n >= c*e^{d/2}. Griffin-Ono-Rolen-Thorner-Tripp-Wagner (Adv. Math. 2022, arXiv:1910.01227) made the low-lying-zero mechanism explicit via zeros of xi^{(n)}.
- status: unconditional | G. Csordas, T. Norfolk, R. Varga; M. Griffin, K. Ono, L. Rolen, D. Zagier, J. Thorner, Z. Tripp, I. Wagner (2022)
- citation: arXiv:1910.01227 (Adv. Math. 397, 2022); arXiv:1902.07321 (PNAS 116, 2019); Csordas-Norfolk-Varga, Trans. AMS 296 (1986) 521-541
- checked against: https://arxiv.org/abs/1910.01227
- technique: moment inequalities for Fourier transforms in the Laguerre-Polya class; asymptotics of xi Taylor coefficients; Hermite-distribution limits
- bottleneck: The full determinantal hierarchy (the doubly-infinite positivity conditions behind Polya's program, Grommer-type determinants) beyond the order-2 Turan case is computationally untouched: higher-order Turan inequalities for the b_m and the (d,n) region NOT covered by the effective theorem have no enclosure-checked computation
- tunable: degree d, shift n ranges; precision of the xi Taylor coefficients; Sturm vs discriminant certificates; higher-order Turan determinant order
- gap: The finite exceptional set of (d,n) pairs left by GORZ has, for zeta, only float-grade exploration; a enclosure-checked sweep (Sturm sequences in ball arithmetic, exactly the lab's li.py exact-Sturm machinery) over d up to a few hundred and n up to the effective threshold is feasible and unpublished; the same sweep on DH would show what hyperbolicity failure looks like

### Nyman-Beurling/Baez-Duarte distance: Burnol lower bound and the BCF conditional asymptotic
- statement: Let d_N^2 = inf_{A_N} (1/2pi) int |1 - zeta*A_N(1/2+it)|^2 dt/(1/4+t^2) over Dirichlet polynomials of length N. Burnol: liminf d_N^2 log N >= sum over distinct zeros of 1/|rho|^2, which under RH + simplicity equals 2 + gamma - log(4*pi) = 0.0461914179...; Bettin-Conrey-Farmer: assuming RH and sum_rho 1/|zeta'(rho)|^2 << T^{3/2-delta}, d_N^2 ~ (2 + gamma - log 4pi)/log N. Recent Gram-matrix structure work: arXiv:2405.06349 (2024); related inequality reformulations arXiv:2310.03972 (2023).
- status: RH-conditional | L. Baez-Duarte; J.-F. Burnol; S. Bettin, J. B. Conrey, D. W. Farmer (2013)
- citation: arXiv:1211.5191 (Proc. Steklov Inst. Math. 2013); arXiv:2405.06349; Burnol, Adv. Math. 170 (2002)
- checked against: https://arxiv.org/pdf/1211.5191
- technique: Hilbert-space distance minimization; Gram matrix of dilations of the fractional part; Vasyunin-sum evaluation of Gram entries
- bottleneck: The Gram matrix is dense and ill-conditioned; mid-2000s numerics (Landreau-Richard era) stopped near N ~ 10^3-10^4 in float arithmetic and the convergence of d_N^2 log N to 0.0461914 was never observed convincingly because the approach to the limit is logarithmically slow
- tunable: Dirichlet polynomial coefficients (the whole point: a length-N vector minimizing a quadratic form); Gram solver preconditioner; regularization; N schedule
- gap: No enclosure-checked computation of d_N^2 exists at any N; with Arb-enclosed Vasyunin sums and a preconditioner exploiting the 2024 Gram-structure results, N ~ 10^5 is plausible, and the measured second-order term in d_N^2 log N would test the BCF conditional hypothesis sum_rho 1/|zeta'(rho)|^2 << T^{3/2-delta} from the numerical side

### Weil positivity: Yoshida's finite-rank numerics and the 2026 truncation revival
- statement: Weil positivity (positivity of the Weil quadratic form on autocorrelations g = f * f~) is equivalent to RH. Yoshida (1990) proved positivity results for finite-rank restrictions using numerical analysis on test functions supported in (1/2, 2). In 2026: Groskin (arXiv:2607.02828, v3 Aug 14 2026) gives a finite Guinand-Weil dictionary with an archimedean tail that is a totally positive Cauchy-Stieltjes increment, with worked parameters c = 100, N = 200, T = 800, budget B_T ~ (2N+1) rho log T/(pi^2 T), rho = 2pi/log c, verified against the first 512 zeros; arXiv:2607.24830 numerically realizes Suzuki's Weil-quadratic-form operator; Connes-van Suijlekom and Connes-Consani-Moscovici give explicit (2N+1)x(2N+1) Galerkin matrices whose deep spectrum windows Weil positivity.
- status: numerical | H. Yoshida; A. Connes, C. Consani, W. van Suijlekom, H. Moscovici; A. Groskin (2026)
- citation: arXiv:2607.02828; arXiv:2607.24830; Yoshida, Hermitian forms attached to zeta functions (1990); survey arXiv:2602.04022 (Connes, Feb 2026)
- checked against: https://arxiv.org/abs/2607.02828
- technique: Galerkin truncation of the Weil form; total positivity of the archimedean tail; band-limited test function dictionaries
- bottleneck: The finite windows certify positivity only on explicit finite-dimensional subspaces; growing (c, N) blows up conditioning, and the archimedean tail bounds are new enough (July 2026) that nobody has stress-tested or independently reproduced them
- tunable: prime cutoff c; band N; test-function dictionary; window T; Galerkin basis; which eigenvalue of the truncated form to track
- gap: This is a weeks-old optimization surface: the Groskin tail-order claims and budget formula have no independent verification, no ball-arithmetic implementation, and no negative control (the same truncation run on DH, where positivity MUST fail at some finite rank, would both validate the machinery and measure at what (c, N) the off-line zero at 0.808517 + 85.699348i becomes visible)

### Redheffer matrix spectrum and det R_n = M(n)
- statement: Redheffer (1977): det R_n = M(n), the Mertens function, so RH iff det R_n = O(n^{1/2+eps}). Barrett-Forcade-Pollington (1988): R_n has n - floor(log_2 n) - 1 eigenvalues equal to 1, a dominant eigenvalue ~ sqrt(n), and a negative eigenvalue ~ -sqrt(n). The spectral route to bounding M(n) via the nontrivial eigenvalue cluster was never pushed with serious computation; a Nov 2025 paper (arXiv:2511.13627) generalizes to Fibonacci-Redheffer matrices and gives a new RH-related expression.
- status: unconditional | R. Redheffer; W. Barrett, R. Forcade, A. Pollington (1988)
- citation: arXiv:2511.13627 (2025, with references); Barrett-Forcade-Pollington, Congr. Numer. / Linear Algebra appl. line of work (1988)
- checked against: https://arxiv.org/abs/2511.13627
- technique: sparse 0-1 matrix spectral analysis; determinant identity via divisibility poset
- bottleneck: The 'spectral radius vs determinant' tension was never quantified: the small eigenvalue cluster (the ~2 log_2 n eigenvalues not equal to 1) determines M(n) growth, and 1980s-2000s hardware could not track this cluster to large n with precision
- tunable: n schedule; which spectral slice; sparse eigensolver; weighting generalizations (Fibonacci-Redheffer family parameters)
- gap: enclosure-checked computation of the full nontrivial spectrum of R_n to n ~ 10^7 (sparse structure, ~n log n nonzeros) is now routine and unpublished; the empirical distribution of the nontrivial eigenvalue cluster and its n-scaling is an open phenomenological question directly tied to Mertens growth, and the 2025 Fibonacci generalization shows the area is stirring again

### Franel-Landau Farey discrepancy criterion
- statement: RH is equivalent to sum_{nu=1}^{Phi(x)} |delta_nu| = O(x^{1/2+eps}) where delta_nu is the deviation of the nu-th Farey fraction of order x from nu/Phi(x) (Franel-Landau 1924). A July 2026 paper proves an explicit logarithmic-order lower bound for the average local discrepancy of the Farey sequence, a new constraint on the Franel-Landau quantity.
- status: unconditional | J. Franel, E. Landau; recent lower bound: MDPI Mathematics 14(14):2543 authors (2026)
- citation: https://www.mdpi.com/2227-7390/14/14/2543 (2026); Franel-Landau, Gott. Nachr. (1924); Kanemitsu-Yoshimoto, Acta Arith. 75 (1996)
- checked against: https://www.mdpi.com/2227-7390/14/14/2543
- technique: Farey fraction discrepancy sums, Mobius inversion to Mertens-type sums
- bottleneck: Computing sum |delta_nu| needs the full Farey sequence of order Q (length ~ 3Q^2/pi^2), so historical numerics stopped at tiny Q; nobody has published the empirical exponent of the Franel-Landau sum against x^{1/2}
- tunable: order Q; discrepancy weighting (L1 vs L2 vs local average); streaming algorithm; comparison exponents
- gap: Streaming generation of Farey fractions (Stern-Brocot recurrence) makes Q ~ 10^6-10^7 (10^12-10^13 fractions) feasible with integer-exact arithmetic; the measured local-discrepancy profile could be compared against the brand-new 2026 logarithmic lower bound, which appears numerically untested

### Speiser's criterion: no enclosure-checked strip verification exists
- statement: Speiser (1935): RH is equivalent to zeta'(s) having no non-real zeros with Re s < 1/2. Levinson-Montgomery (1974) quantitative extension: zeta and zeta' have approximately the same number of zeros left of the critical line. Numerical studies (Arias-de-Reyna X-ray; extended Selberg class checks in arXiv:1904.03123) verified small regions in float arithmetic only.
- status: unconditional | A. Speiser; N. Levinson, H. L. Montgomery (1935)
- citation: Speiser, Math. Ann. 110 (1935) 514-521; arXiv:1904.03123 (numerical verification in small regions); Springer Eur. J. Math. (2015) On the Speiser equivalent
- checked against: https://arxiv.org/abs/1904.03123
- technique: argument principle for zeta' on rectangles left of the critical line
- bottleneck: Every published check of Speiser's condition is floating-point; a enclosure-checked (interval/ball) verification that zeta' is nonvanishing in 0 < Re s < 1/2 up to a concrete height has never been done, largely because pre-Arb quadrature of zeta'/zeta'' contour integrals was too slow
- tunable: rectangle decomposition; contour quadrature order; precision; height ceiling; derivative order (zeta' vs higher, cf. Levinson-Montgomery)
- gap: A ball-arithmetic argument-principle sweep of the rectangle 0 < sigma < 1/2, 0 < t <= 10^4 is now a workstation computation; it would be the first enclosure-checked Speiser-side companion to RH zero verifications, and the same code run on DH exhibits the Speiser-failure signature (lab's criteria.py already has a Speiser face)


## Territory K: systematic sweep of mid-2025 through August 2026 arXiv math.NT/math.SP for RH-adjacent movement ,  new claimed results and their verification status, new bounds, equivalences, withdrawn claims, computational records, and formalization efforts (Lean/Mathlib, PNT+, FLT side-effects)

### Anthropic/Claude 'more than two thirds' critical-line proportion
- statement: At least 67.250% (kappa >= 0.6725007037) of nontrivial zeros of zeta are simple zeros lying on the critical line, and at least 83.625% of all nontrivial zeros are distinct; unconditional. Method: Weil explicit formula information compressed into a Hermitian quadratic form, Sylvester's law of inertia to separate on-line from off-line contributions, and a rank-trace inequality converting matrix statistics into zero-proportion lower bounds. Previous record for on-line simple zeros: > 5/12 = 41.666...% (Pratt-Robles-Zaharescu-Zeindler 2020, kappa >= 0.4172).
- status: unconditional (claimed); preprint, NOT peer-reviewed; formal Lean statements published with proofs claimed sorry-free, but semantic fidelity of formal statements to mathematical intent still requires human verification | Claude (Anthropic), with internal validation by Levent Alpöge and Ralph Furman; preliminary external reading by J. Brian Conrey and Daniel Goldston (2026)
- citation: Anthropic manuscript (www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf) + github.com/anthropics/zeta-23-lean
- checked against: https://kingy.ai/blog/claude-riemann-hypothesis-67-percent-result/ and WebSearch hits including the Anthropic PDF and github.com/anthropics/zeta-23-lean
- technique: Weil explicit formula, Hermitian quadratic forms, Sylvester inertia, rank-trace inequality; Lean 4 + Mathlib formalization
- bottleneck: Independent community review only beginning as of 2026-08-10; not reproducible end-to-end (unidentified research model); the rank-trace inequality step and the choice of test-function family in the quadratic form are the levers determining the constant
- tunable: test functions in the explicit-formula quadratic form; truncation/cutoff parameters; the rank-trace inequality slack
- gap: The framework is brand new and its optimization surface (test functions entering the Hermitian form, truncation parameters, the inertia bookkeeping) is essentially unmined by anyone outside the paper's authors; also nobody has yet run structure-matched counterexample controls (Davenport-Heilbronn) against the method's discriminating steps

### Pair correlation without RH: narrow-box hypothesis (Baluyot-Goldston-Suriajaya-Turnage-Butterbaugh)
- statement: Assume only that all zeros rho = beta + i*gamma with T < gamma <= 2T lie in a vertical box centered on the critical line of width b/log T with b = b(T) -> 0 as T -> infinity. Then asymptotically at least 2/3 of zeros are simple, at least 2/3 lie on the critical line, and at least 1/3 are simultaneously simple and on the line; the companion 2026 note sharpens this to: at least 2/3 are both simple and on the critical line under the same hypothesis.
- status: conditional on a hypothesis strictly weaker than RH (narrow-box / 'width b/log T' hypothesis); v2 Nov 2025; companion notes Nov 2025 and Mar 2026 | Siegfred Alan C. Baluyot, Daniel A. Goldston, Ade Irma Suriajaya, Caroline L. Turnage-Butterbaugh; notes by Goldston-Suriajaya (2025)
- citation: arXiv:2501.14545 (v2 2025-11-21); arXiv:2511.20059 (v2 2026-02-05); arXiv:2603.28104 (2026-03-30)
- checked against: https://arxiv.org/abs/2501.14545 and https://arxiv.org/abs/2603.28104 (abstracts fetched)
- technique: Montgomery pair correlation with explicit-formula input, Fejér-type test functions, removing RH by controlling horizontal displacement
- bottleneck: The b -> 0 requirement: for fixed b > 0 the proportions degrade, and the degradation rate is governed by the chosen pair-correlation test function
- tunable: pair-correlation test function (currently Fejér kernel), box width parameter b, weighting in the explicit formula
- gap: The dependence of the proportions on fixed b is an explicit extremal problem over admissible test functions that the authors flag but do not optimize; nobody has published the optimal kernel for the fixed-b version

### Short mollifiers and optimal linear combinations of zeta derivatives (Conrey-Farmer-Kwan-Lin-Turnage-Butterbaugh)
- statement: Calculus of variations constructs a sequence of linear combinations of derivatives of zeta adapted to Levinson's method that yield a positive proportion of zeros on the critical line regardless of how short the mollifier is; for degree-2 L-functions the same arithmetic inputs more than double the critical-line proportions previously obtained by Bernard and by Kühn-Robles-Zeindler. Key structural finding: optimizing the linear combination is more impactful than lengthening/refining the mollifier; the combinations also give smooth approximations of Siegel's f-function in the Riemann-Siegel formula.
- status: unconditional | J. Brian Conrey, David W. Farmer, Chung-Hang Kwan, Yongxiao Lin, Caroline L. Turnage-Butterbaugh (2025)
- citation: arXiv:2508.11108 (2025-08-14)
- checked against: https://arxiv.org/abs/2508.11108 (abstract fetched)
- technique: Levinson's method, calculus of variations over linear combinations of derivatives, short mollifiers
- bottleneck: For zeta itself the binding constraint is still mollifier length theta (currently theta = 4/7 via Conrey/Bettin-Chandee-Radziwill-type bounds); the variational gain has not yet been pushed through the full-length zeta optimization
- tunable: coefficients of the linear combination of zeta derivatives (a measure, via Euler-Lagrange), mollifier coefficients and length theta
- gap: The paper's variational principle has not been combined with the longest admissible zeta mollifiers nor with the new two-thirds framework; the interaction of optimal derivative combinations with existing kappa-optimization pipelines is open

### Guth-Maynard zero-density theorem (final revision) and its aftermath
- statement: N(sigma,T) <= T^{30(1-sigma)/13 + o(1)} uniformly, improving Ingham/Huxley's exponent 12/5 for the first time in over 80 years at sigma near 3/4; consequently primes in all short intervals of length x^{17/30+o(1)}, and Ingham's exponent 5/8 for gaps improved. Final arXiv revision 2026-04-07; expository synthesis by Turnage-Butterbaugh, arXiv:2607.04632 (2026-07-06).
- status: unconditional; published/accepted (Annals-track), community-verified | Larry Guth, James Maynard (2024)
- citation: arXiv:2405.20552 (v. revised 2026-04-07); expository: arXiv:2607.04632
- checked against: https://arxiv.org/abs/2405.20552 (search result with revision date) and https://arxiv.org/abs/2607.04632
- technique: New large-value estimates for Dirichlet polynomials of length N taking values near N^{3/4}; energy/incidence arguments on frequency sets
- bottleneck: The o(1) terms are ineffective/inexplicit; the large-value estimate is only known at the critical exponent-3/4 regime and does not yet interpolate optimally elsewhere
- tunable: large-value energy parameters, choice of raising power k, case decomposition thresholds in the incidence argument
- gap: No explicit-in-T version of any Guth-Maynard-type density bound exists (Turnage-Butterbaugh flags this); q-aspect and hybrid analogues only partially done (see 2507.08296); the density hypothesis exponent 2 remains open at sigma = 3/4 where GM gives 30/13 = 2.3077

### Large-value estimates transferred to Dirichlet L-functions (q-aspect zero density)
- statement: Guth-Maynard-type large-value estimates for Dirichlet polynomials extended to give improved zero-density estimates for the family of Dirichlet L-functions modulo q (q-aspect / hybrid analogue of N(sigma,T) <= (qT)^{30(1-sigma)/13+o(1)}-type bounds in suitable ranges).
- status: unconditional; recent preprint, under review | (authors as listed on arXiv:2507.08296) (2025)
- citation: arXiv:2507.08296 (July 2025)
- checked against: https://arxiv.org/html/2507.08296 (search result; abstract not fully fetched)
- technique: Guth-Maynard large-value machinery adapted to character sums
- bottleneck: Character-sum analogues of the critical N^{3/4} regime are weaker; uniformity in q costs exponents
- tunable: raising powers, ranges of moduli, decomposition into q-smooth/rough cases
- gap: Applications downstream (primes in short APs, Linnik-type constants) not yet reharvested with the new density input; explicit versions absent

### Best explicit Korobov-Vinogradov zero-free region (Bellotti) and improved argument/zero-counting bounds (Bellotti-Wong)
- statement: zeta(sigma+it) != 0 for sigma >= 1 - 1/(55.241 (log|t|)^{2/3} (log log|t|)^{1/3}), |t| >= 3 (Bellotti, J. Math. Anal. Appl. 2024; constant digits memory-recalled, order and shape verified); companion explicit log-free zero-density estimate (J. Number Theory 269 (2025) 37-77); Bellotti-Wong give improved explicit bounds for S(t) and the zero-counting function N(T) (Math. Comp. 2025, appendix by Fiori). These are the current inputs to every explicit PNT-error-term and prime-gap pipeline.
- status: unconditional, published | Chiara Bellotti; Chiara Bellotti and Peng-Jie Wong (2025)
- citation: Bellotti, JMAA 2024 (arXiv:2306.10680); Bellotti, J. Number Theory 269 (2025) 37-77 (arXiv:2405.12545); Bellotti-Wong, Math. Comp. 2025
- checked against: WebSearch confirming Bellotti JMAA 2024, JNT 269 (2025) 37-77, and Bellotti-Wong Math. Comp. 2025 exist; exact constant digits: memory-unverified
- technique: Explicit Vinogradov-Korobov exponential-sum bounds, explicit Ford-style machinery, computation-assisted optimization of constants
- bottleneck: The constant 55.241-ish is driven by explicit Vinogradov integral bounds; every improvement upstream (explicit exponential sums) propagates but requires re-running long constant-chasing chains
- tunable: exponential-sum parameters, smoothing kernels, interval subdivisions in the explicit computation
- gap: The chains are long enough that intermediate lemmas are individually suboptimal; a systematic interval-arithmetic re-optimization of the constant chain has not been published; digits above are memory-level and should be re-pinned from the paper before use

### New explicit sub-Weyl bound for |zeta(1/2+it)| (Revers 2026)
- statement: An improved explicit estimate for zeta(1/2+it) along the critical line, sharpening Hiary-Patel-Yang (2024)-type explicit bounds (of the shape |zeta(1/2+it)| <= a * t^{27/164} and Weyl-type |zeta(1/2+it)| <= b * t^{1/6} log t with explicit a, b) via a refined explicit van der Corput method plus computational parameter searches. Context: earlier explicit constants (Hiary; Platt-Trudgian dependents) were affected by a flaw in a Cheng-Graham lemma, forcing repairs. Asymptotically the best exponent remains Bourgain's 13/84 (2017), which is NOT explicit.
- status: unconditional; preprint Feb 2026 | Michael Revers (2026)
- citation: arXiv:2602.05614 (2026-02-05)
- checked against: https://arxiv.org/abs/2602.05614 via WebSearch (papers.cool and arXiv html hits)
- technique: Explicit van der Corput / exponent-pair method with computer-assisted optimization
- bottleneck: Explicit exponent stuck near 27/164 = 0.16463 vs Bourgain's inexplicit 13/84 = 0.15476; the leading constants come from finite parameter searches that are not provably optimal
- tunable: van der Corput subdivision parameters, exponent-pair choices, interval cutoffs, explicit constants per range of t
- gap: No explicit version of any decoupling-based (Bourgain-Watt) bound exists; the van der Corput parameter space in Revers' proof is a finite search a rigorous optimizer could re-run and likely shave

### Moment bounds for zeta: state of the art surveyed (Florea 2025)
- statement: Survey from Heath-Brown's 1981 upper/lower bounds to the present: sharp-order unconditional bounds M_k(T) asymptotic-order T (log T)^{k^2} now known unconditionally for 0 <= k <= 2 (Heap-Radziwill-Soundararajan for k<=2 upper; Radziwill-Soundararajan lower for all k>=1), and for all k > 2 conditionally on RH (Harper's sharp upper bound M_k(T) << T (log T)^{k^2}); recent work essentially recovers expected growth rates for all moments.
- status: survey of unconditional (k <= 2) and RH-conditional (k > 2) results | Alexandra Florea (2025)
- citation: arXiv:2509.20335 (2025-09-24)
- checked against: https://arxiv.org/abs/2509.20335 (abstract fetched; detailed exponents from survey body not fetched, partially memory)
- technique: Mollified moments, Soundararajan-Harper large-deviation method for log|zeta|
- bottleneck: Unconditional sharp upper bounds for any k > 2 remain open; the 4th moment constant chain (Ingham-Motohashi) is fully explicit but the 6th and 8th moment asymptotics are conjectural (CFKRS constants)
- tunable: mollifier/resonator coefficients in lower-bound arguments; shifts in CFKRS polynomials
- gap: Numerical scorecards of CFKRS-conjectured lower-order moment polynomials at large T are thin in the literature; the lab's moments.py + Odlyzko data can score them at heights others have not

### PrimeNumberTheorem+ (PNT+) Lean formalization status
- statement: PNT formalized in Lean 4 via Wiener-Ikehara (Kontorovich-Tao project); current in-progress goals: explicit/strong PNT error term (psi(x) = x + O(x exp(-c sqrt(log x)))) and PNT in arithmetic progressions. In January 2026 Math Inc. announced its 'Gauss' autoformalization system completed the strong PNT challenge (set January 2024) in about three weeks after 18+ months of stalled human effort. Separately, 'Formalizing zeta and L-functions in Lean' documents Mathlib's zeta/L-function coverage, and a crowdsourced project is formalizing inter-related explicit analytic number theory results (explicit PNT among them) with AI autoformalization tools.
- status: formalization record; kernel-checked components merged or pending Mathlib merge; the Gauss claim is a company announcement, independently examinable via the artifact but not conventional peer review | Alex Kontorovich, Terence Tao, PNT+ contributors; Math Inc. (Gauss); Loeffler-Stoll-et-al. for zeta/L-function Mathlib coverage (2026)
- citation: github PrimeNumberTheorem+; afm.episciences.org/15954 ('Formalizing zeta and L-functions in Lean'); Math Inc. Gauss announcement (Jan 2026)
- checked against: https://mathstodon.xyz/@tao and https://afm.episciences.org/15954/pdf via WebSearch; Gauss claim via cs.virginia.edu summary page (secondary source)
- technique: Lean 4 + Mathlib, Wiener-Ikehara Tauberian route, AI-assisted autoformalization
- bottleneck: Explicit-constant analytic lemmas (zero-free regions, explicit formula with error terms) are the thinnest part of Mathlib; each explicit paper formalized requires re-deriving classical explicit inequalities not yet in the library
- gap: No formalized zero-density estimate, no formalized Montgomery pair-correlation result, no formalized explicit zero-free region of Korobov-Vinogradov shape exists anywhere; the strong-PNT artifact makes previously blocked downstream formalizations (Mertens-type sums with error terms, explicit psi bounds) suddenly cheap

### Fermat's Last Theorem Lean project (Buzzard-Taylor): Mathlib side-effects
- statement: EPSRC-funded to September 2029; formalizing the modern (Khare-Wintenberger/Kisin) route; as of the Dec 2024 public update the definitions of R and T in R=T were still incomplete, with Andrew Yang's abstract patching-criterion commutative algebra done; the project continuously PRs foundational number theory (adeles, class field theory groundwork, quaternion algebras, automorphic forms scaffolding) into Mathlib. Side-effect for analytic NT: adelic and L-function infrastructure grows, but the FLT route deliberately avoids analytic estimates, so explicit analytic coverage gains come from PNT+ rather than FLT.
- status: formalization effort, ongoing; no completed headline theorem yet | Kevin Buzzard, Richard Taylor, Andrew Yang, FLT project contributors (2026)
- citation: github.com/ImperialCollegeLondon/FLT; blueprint at imperialcollegelondon.github.io/FLT
- checked against: https://github.com/ImperialCollegeLondon/FLT and lean-lang.org/use-cases/flt via WebSearch (2026-specific status page not found; Dec 2024 update is latest confirmed)
- technique: Lean 4 blueprint-driven formalization
- bottleneck: R=T definitional work; the analytic-NT spillover is limited by design
- gap: The adelic infrastructure being merged (adeles of number fields, Haar measure work) is exactly what a future formalization of Tate's thesis / explicit formula needs and nobody has claimed that target yet

### Claimed proofs/disproofs and withdrawals in the window
- statement: (a) Davlatov, 'A Proof of the truth of the Riemann hypothesis' (arXiv:1603.09665), withdrawn by author at v17 on 2026-01-14 (Salem-integral-equation route). (b) Unterberger, 'A pseudodifferential proof of the Riemann hypothesis' (arXiv:2111.02792), withdrawn by author. (c) Liu, 'Disproof of the Riemann Hypothesis' (arXiv:2404.06306, latest version 2025-01-20), claims contradiction via reciprocal sums over xi-zeros; not accepted, not withdrawn, no community endorsement. (d) Blinovsky (arXiv:1703.03827) still updating through August 2026, unaccepted. None of these has any verified standing; the only 2025-26 claimed advance with expert engagement is the Anthropic 67.25% proportion result (entry 1), which claims a proportion, not RH.
- status: claimed/withdrawn; none verified | Davlatov; Unterberger; Liu; Blinovsky (2026)
- citation: arXiv:1603.09665v17; arXiv:2111.02792; arXiv:2404.06306; arXiv:1703.03827
- checked against: https://arxiv.org/abs/1603.09665v9, https://arxiv.org/abs/2111.02792, https://arxiv.org/abs/2404.06306 via WebSearch
- technique: various (Salem equation, pseudodifferential calculus, xi-zero sum identities)
- bottleneck: n/a
- gap: Liu's 'disproof' hinges on a computable identity about reciprocal sums over zeros; a enclosure-checked Arb computation of both sides would close it publicly as a refutation-with-witness, which apparently nobody has bothered to publish

### Spectral/Weil-positivity front: Connes and the truncated Weil quadratic form
- statement: (a) Connes, 'The Riemann Hypothesis: Past, Present and a Letter Through Time' (arXiv:2602.04022, Feb 2026) revisits the spectral interpretation program. (b) Connes-Consani-Moscovici, 'Zeta Spectral Triples' (CIRM proceedings, April 2025). (c) 'Weil's quadratic form via the screw function' (arXiv:2606.09096, June 2026) unifies Yoshida (1992), Bombieri (2001,2003), Connes-Consani (2023) and Connes-Consani-Moscovici (2025+) positivity results through Krein's screw-function theory. (d) 'High-Precision Approximation of Riemann Zeros via the Truncated Weil Form' (arXiv:2605.20224, May 2026) and 'A finite Guinand-Weil dictionary and archimedean tail order for the truncated Weil quadratic form' (arXiv:2607.02828, July 2026) make the truncated Weil form a concrete numerical object: ground-state eigenvalue of a truncated Weil operator measures proximity to Weil positivity (Connes-van Suijlekom route).
- status: mixture: published theory (a-c) and numerical preprints (d); no positivity criterion proved beyond known archimedean/finite-truncation cases | Alain Connes, Caterina Consani, Henri Moscovici, Walter van Suijlekom, and (screw function / truncated-form papers) authors as listed on arXiv (2026)
- citation: arXiv:2602.04022; arXiv:2606.09096; arXiv:2605.20224; arXiv:2607.02828
- checked against: WebSearch results listing arXiv:2602.04022, 2606.09096, 2605.20224, 2607.02828 and alainconnes.org/publications
- technique: Noncommutative geometry, semilocal trace formula, Krein screw functions, truncated Toeplitz-type operators, numerical spectra
- bottleneck: Weil positivity is proved only for restricted test-function classes / truncations; the archimedean tail order of the truncated form (2607.02828) is exactly the quantitative object controlling how far the truncation can be pushed
- tunable: truncation cutoff, test-function bases for the Weil form, archimedean weight
- gap: The predicted tail order and the decay rate of the minimal eigenvalue of the truncated Weil Gram matrix have not been independently verified with enclosure-checked (interval) arithmetic; the papers use floating-point spectra

### Computational verification record for RH: unchanged at 3*10^12
- statement: All zeros beta + i*gamma with 0 < gamma <= 3,000,175,332,800 have beta = 1/2 and are simple (Platt-Trudgian, Bull. LMS 2021, rigorous interval arithmetic). No newer rigorous record within mid-2025 to Aug 2026 was found in searches; the older nonrigorous 10^13 (Gourdon 2004) still stands apart as unverified. The Anthropic 67.25% paper and explicit-constant papers all still cite 3*10^12 as the rigorous height.
- status: unconditional (finite range, modulo correctness of enclosure-checked floating-point sign evaluations); record confirmed still standing | David J. Platt, Timothy S. Trudgian (2021)
- citation: arXiv:2004.09765; Bull. London Math. Soc. 53 (2021)
- checked against: https://arxiv.org/abs/2004.09765 via WebSearch; absence of newer record checked via WebSearch (no hit)
- technique: Interval-arithmetic Turing-method zero counting via rigorous FFT-based Z evaluation
- bottleneck: Compute cost scales roughly linearly in height with large constants; nobody has funded the next order of magnitude
- gap: A modern Arb-based redo could likely reach 10^13 rigorously with commodity GPU/cluster budgets; also the 3*10^12 record has never been independently replicated end-to-end by a second team, which matters because Polymath15-style results condition on it

### de Bruijn-Newman constant: 0 <= Lambda <= 0.2, plus new structural work on the kernel
- statement: Lower bound Lambda >= 0 (Rodgers-Tao 2018, Forum Math. Pi 2020); upper bound Lambda <= 0.2 (Polymath 15, 2019, via effective approximation of the heat-flow evolution H_t and a barrier computation conditioned on RH verification height ~3*10^10 at the time). No improvement to either bound found in mid-2025-Aug 2026; new adjacent work: 'On the Pólya Frequency Order of the de Bruijn Newman Kernel' (arXiv:2602.20313, 2026-02-21) studies structural positivity properties of the kernel.
- status: unconditional; bounds unchanged in window | Brad Rodgers, Terence Tao; D.H.J. Polymath; (2602.20313 authors as listed) (2026)
- citation: arXiv:1801.05914; arXiv:1904.12438; arXiv:2602.20313
- checked against: https://arxiv.org/abs/1801.05914, https://arxiv.org/abs/1904.12438, arXiv:2602.20313 via WebSearch (Polymath exact bound 0.2 vs 0.22: search snippet said 0.22, standard published value is 0.2; digits flagged memory-vs-snippet, re-pin before use)
- technique: Heat flow H_t, effective error bounds on approximations to H_t, barrier certificates, Pólya frequency functions
- bottleneck: Polymath15's Lambda <= 0.2 was limited by the RH-verification height and barrier computation budget available in 2019; the write-up notes Lambda <= 0.1 was plausibly reachable with more compute
- tunable: barrier location/shape, mesh for enclosure-checked evaluation of H_t, Euler-product surrogate parameters, verification height
- gap: Re-running the Polymath15 barrier with the now-available 3*10^12 verification height and Arb-enclosure-checked barrier evaluation is an unharvested, essentially mechanical improvement path to Lambda <= ~0.15 or better; nobody has published it in 7 years

### Explicit Carlson-type zero-density and short-interval prime refinements (window activity)
- statement: Ongoing 2024-2026 explicit-density activity around the Guth-Maynard shift: 'An explicit version of Carlson's theorem' (arXiv:2412.02068) gives fully explicit N(sigma,T) bounds of Carlson shape; 'Refinements for primes in short arithmetic progressions' (arXiv:2507.15334, July 2025) reharvests short-AP prime results; 'Minimal zero-free regions for results on primes between consecutive k-th powers' (arXiv:2602.14340, Feb 2026) inverts the pipeline, asking what zero-free region suffices for a target prime statement.
- status: unconditional, explicit; preprints and recent journal versions | various (as listed per arXiv ID) (2026)
- citation: arXiv:2412.02068; arXiv:2507.15334; arXiv:2602.14340
- checked against: arXiv IDs surfaced via WebSearch; abstracts not individually fetched (titles and dates from listings)
- technique: Explicit density theorems, explicit zero-free regions, careful constant propagation
- bottleneck: Explicit density exponents remain far from the inexplicit records (no explicit analogue of 30/13 exists); each paper's constants are near-optimal only for its own lemma chain
- gap: The 'minimal zero-free region for target X' inversion (2602.14340) defines a clean optimization problem the lab's enclosure-checked machinery could systematically map: for each target prime statement, the Pareto frontier of (zero-free-region constant, verification height) pairs
