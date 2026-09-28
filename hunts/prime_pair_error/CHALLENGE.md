# Section 8: independent challenge to CANDIDATE_ENERGY.md

2026-09-10. Target: [CANDIDATE_ENERGY.md](CANDIDATE_ENERGY.md) as it stands
on this branch, which claims not just the requested domination
\(E_{\rm corr}(N)\le\mathrm{Energy}(N)\) but the exact identity
\[
 E_{\rm corr}(N)=\mathrm{Energy}(N)\qquad\text{for every }N. \tag{$\star$}
\]
Three attacks, all run independently of the candidate's own code, results in
`results_s8_challenge.json` (`s8_challenge.py`).

**Verdict, up front.** \((\star)\) survives attack 1: no violation exists,
because none can. Attack 2 shows why that survival is worthless as evidence
about primes: the identical construction, applied to a real, functional-
equation sequence with a documented zero off the critical line, produces the
identical identity, to the same floating-point precision. Attack 3 explains
the mechanism: every step of the domination proof is linear algebra on an
arbitrary finite real vector, and uses no property of \(\Lambda\), \(\mathfrak
S\), or \(C_N\) beyond their being some fixed real numbers. This is not a
new discovery -- CANDIDATE_ENERGY.md's own "What this is not" paragraph and
Section 5 point 2 already say the identity "carries no arithmetic content at
all" -- but it was asserted there, not tested. This document tests it.
None of the three attacks contradicts CANDIDATE_ENERGY.md; together they
independently confirm its own stated limitation and rule out the reading
that \((\star)\), because it is exact and unconditional, is progress toward
bounding \(E_{\rm corr}(N)\) or toward RH.

## Attack 1: independent numerical search, \(N\le10^5\)

**Method, built from scratch, no import of `s8_candidate_energy.py`.**
`s8_challenge.py` reimplements, in its own code:

- `sieve_primes` / `von_mangoldt`: smallest-set-of-primes sieve, proper prime
  powers included, coded independently of `probe.py`'s smallest-prime-factor
  sieve.
- `singular_series`: \(S(k)=2C_2\prod_{p\mid k,\,p>2}(p-1)/(p-2)\) for even
  \(k\), 0 for odd \(k\) (CORRECTED_RH_BRIDGE.md eq 4), from the same quoted
  reference constant \(C_2\) `probe.py` uses (an input, not something either
  script fits).
- `autocorr_fft`: \(\psi_2(N,h)\) as an FFT autocorrelation, independently
  coded, cross-checked at \(N=2000\) against a fresh \(O(N^2)\) direct pair
  sum (`autocorr_direct`): max\(|\)diff\(|=1.8\times10^{-12}\).
- `multiscale_energy`: the dyadic block-average telescoping of
  CANDIDATE_ENERGY.md Section 2/3, re-derived from the boxed definition and
  coded as a bottom-up pairwise-averaging recursion, not copied from
  `s8_candidate_energy.py`'s vectorized reshape loop.

Sanity checks against fixed external references: the \(E(N)/(N^2\log^2N)\)
ratio at \(N=10^5\) computed here is 0.16857, matching CHHL's own published
Table 1 value (`probe.py`'s independent cross-check target) to 5 digits; and
at \(N=2000\), this script's \(E_{\rm corr}\) and \(\mathrm{Energy}\) match
`results_s8_candidate_energy.json`'s row (produced by
`s8_candidate_energy.py`, never imported here) to relative error \(0\) and
\(1.5\times10^{-16}\) respectively.

**Grid.** 116 values of \(N\) in \([1,10^5]\): every \(N\le20\); steps of 25
to 200; steps of 100 to 2000; steps of 1000 to 20000; steps of 5000 to
\(10^5\); \(2^k\), \(2^k\pm1\) for \(k=1,\dots,17\) (the padding boundary,
where a scale is dropped or added); and the candidate's own five \(N\).

**Result.** `all_dominate = True` at every one of the 116 points; the largest
\(|\)relative gap\(|\) between \(\mathrm{Energy}\) and \(E_{\rm corr}\) found
anywhere in the grid is \(4.3\times10^{-16}\), i.e. floating-point roundoff,
not a mathematical gap. No violation of the domination exists at any tested
\(N\le10^5\), and none is expected to: Attack 3 shows the identity is an
exact Pythagorean decomposition of \(\|x\|_2^2\), true for every real vector
\(x\), so a violation at any \(N\) would mean a bug in the floating-point
implementation, not a counterexample to the mathematics.

**Verdict: attack 1 does not refute the candidate.** The domination (in fact
the stronger equality) holds, exactly, everywhere tested.

## Attack 2: the Davenport-Heilbronn battery

**Why this attack, and what it is for.** `AGENTS.md`'s standing
counterexample-battery rule (`zeta/epstein.py`'s module docstring; also
`NULLCONTROLS.md` and `REDTEAM.md` attack A3) requires that any claimed
structural pattern be run against the Davenport-Heilbronn function \(f\): a
function with a Riemann-type functional equation \(F(s)=F(1-s)\), real
Dirichlet coefficients, and a proven, located zero off the critical line at
\(\rho\approx0.808517+85.699348i\). If a pattern also holds for \(f\), the
repository's own gate says it is dead on arrival as evidence about zeta,
because \(f\)'s off-line zero means whatever mechanism produced the pattern
cannot be "RH is true," since it is false for \(f\).

**Construction.** Using `zeta.epstein.dh_coefficient` (never reimplemented;
this is the one place the attack is required to use the repository's own
counterexample object, not a substitute), build the real, exactly period-5
sequence \(a(n)\), \(a(1),\dots,a(5)=1,\kappa,-\kappa,-1,0\) with
\(\kappa=0.284079\ldots\) the Davenport-Heilbronn constant. Define the exact
analogue of the singular series for a periodic sequence, its period average
\[
 \rho(h):=\frac15\sum_{j=1}^5a(j)\,a(j+h)\qquad(\rho\text{ depends only on }h\bmod5),
\]
which plays exactly \(\mathfrak S(h)\)'s role: it is the exact main term of
\(\sum_{n=1}^{N-h}a(n)a(n+h)\), because \(a\) is periodic with no arithmetic
irregularity to correct for (unlike \(\mathfrak S\), \(\rho\) needs no error
term at all). Then, verbatim in the same construction as
CANDIDATE_ENERGY.md Section 1-2 with \(a\) in place of \(\Lambda\) and
\(\rho\) in place of \(\mathfrak S\):
\[
 x_h^{\rm DH}:=\Big(\sum_{n=1}^{N-h}a(n)a(n+h)\Big)-(N-h)\rho(h),\qquad
 E_{\rm corr}^{\rm DH}(N):=2\sum_{h=1}^Nx_h^{{\rm DH}\,2},
\]
and \(\mathrm{Energy}^{\rm DH}(N)\) from the identical dyadic block-average
telescoping, same code (`multiscale_energy`, `e_corr_and_energy`), no
branch on which sequence it is fed.

**Result.** Tested at 33 values of \(N\) up to \(10^5\) (powers of two and
their neighbours, plus \(10^2,10^3,\dots,10^5\)):
\(\mathrm{Energy}^{\rm DH}(N)=E_{\rm corr}^{\rm DH}(N)\) exactly, to
floating-point precision, at every one (largest \(|\)relative gap\(|\)
\(8.2\times10^{-16}\), again pure roundoff). The identity holds for the
Davenport-Heilbronn sequence exactly as it holds for the corrected prime-pair
residual, with no exception and no weaker constant.

**Verdict: attack 2 confirms the candidate has distinguished nothing about
zeta.** The domination inequality \((\star)\) requested by Section 8 --
indeed the stronger equality CANDIDATE_ENERGY.md actually proves -- holds
for a sequence that is real, satisfies a genuine functional equation, and
provably violates RH. Nothing about \((\star)\) can therefore be evidence
toward RH, toward the open target \(E_{\rm corr}(N)\ll_\epsilon N^{2+\epsilon}\)
being reachable through this decomposition, or toward any RH-specific
mechanism. This is exactly the outcome CANDIDATE_ENERGY.md's own "What this
is not" section already anticipates; attack 2 is the check that makes it
more than an assertion.

## Attack 3: reading the domination proof line by line

CANDIDATE_ENERGY.md Section 3 has three numbered results: the Lemma
(projection algebra, \(P_aP_b=P_{\max(a,b)}\)), the Corollary (\(D_k\) is an
orthogonal projection, and \(D_k\), \(D_{k'}\), \(P_K\) are pairwise
orthogonal), and the Theorem (the Pythagorean identity
\(\sum x_h^2=M\mu^2+\sum_k\|D_kx\|_2^2\)).

- **The Lemma's proof** uses only: \(P_k\) is symmetric (an averaging
  operator has a symmetric matrix), \(P_k\) is idempotent (averaging a
  block-constant vector again is a no-op), and the nesting
  \(V_b\subseteq V_a\) for \(a\le b\) (a coarser block is a union of finer
  blocks). All three are facts about the block structure of
  \(\{1,\dots,M\}\) under dyadic subdivision. None mentions \(x\), let alone
  \(\Lambda\), \(\mathfrak S\), or \(C_N\).
- **The Corollary's proof** is pure algebra on the Lemma's identity
  (\(D_k^2=D_k\), \(D_kD_{k'}=0\), \(P_KD_k=0\)). Same conclusion: no
  arithmetic input, not even the existence of \(x\).
- **The Theorem's proof** telescopes \(\sum_kD_k=P_0-P_K\) (true for any
  finite sum of these operators) and expands \(\|x\|_2^2\) by bilinearity,
  using the Corollary's orthogonality to kill every cross term. The one
  place \(x\) enters is as a generic vector in \(\mathbb R^M\); the proof
  never uses that \(x_h=r_N(h)-C_N(h)\), never uses that \(N-h\) is the
  correlation endpoint, never uses positivity, boundedness, or any growth
  property of \(\Lambda\) or \(\mathfrak S\), and never uses the value of
  \(C_N\) (whether zero, as in every numerical run, or an actual
  exceptional correction).

**The only place arithmetic content enters at all** is Section 1's
definition \(x_h:=r_N(h)-C_N(h)\) -- but that is *setup*, external to the
proof of \((\star)\), not a step inside it. Substituting a completely
different real vector there, with a different arithmetic origin and a
different (in fact false) relationship to RH, changes nothing about the
proof's validity, and attack 2 exhibits exactly that substitution
numerically.

**Verdict: zero steps of the domination proof use the structure of the
primes.** The proof is a special case of the general fact that dyadic
block-averaging is an orthogonal decomposition of \(\mathbb R^M\) (an
instance of a Haar/martingale telescoping), applicable to any finite real
sequence. This matches, independently, CANDIDATE_ENERGY.md's own grading of
Section 3 ("It is exact for every finite \(N\)... assumes nothing about the
arithmetic content of \(x_h\)") and Section 5 point 2 ("carries no
arithmetic content at all"); attack 3 is the outside confirmation of that
self-assessment rather than a new finding.

## Overall verdict

CANDIDATE_ENERGY.md's equality \((\star)\) is not refuted by attack 1: it
holds everywhere tested, because it is an algebraic identity, not an
estimate, and cannot fail for a bug-free implementation. What is refuted,
by attacks 2 and 3 together, is any reading of \((\star)\) as evidence of
progress toward the open target
\(E_{\rm corr}(N)\ll_\epsilon N^{2+\epsilon}\), toward RH, or toward
anything specific to primes: the identity holds equally, exactly, and with
the same proof, for a real sequence built from a function whose own
Riemann-type functional equation does not save it from having a zero at
\(\mathrm{Re}(s)\approx0.8085\ne\tfrac12\). Per the repository's standing
counterexample-battery rule, a construction that survives the battery this
completely -- not approximately, but as the identical identity to sixteen
digits -- has distinguished nothing, and CANDIDATE_ENERGY.md already says as
much about itself. Section 8's open item is exactly where CANDIDATE_ENERGY.md
left it: the actual size of \(E_{\rm corr}(N)\).
